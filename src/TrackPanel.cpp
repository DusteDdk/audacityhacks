/**********************************************************************

  Audacity: A Digital Audio Editor

  TrackPanel.cpp

  Dominic Mazzoni
  and lots of other contributors

  Implements TrackPanel.

********************************************************************//*!

\file TrackPanel.cpp
\brief
  Implements TrackPanel.

*//***************************************************************//**

\class TrackPanel
\brief
  The TrackPanel class coordinates updates and operations on the
  main part of the screen which contains multiple tracks.

  It uses many other classes, but in particular it uses the
  TrackInfo class to draw the controls area on the left of a track,
  and the TrackArtist class to draw the actual waveforms.

  Note that in some of the older code here,
  "Label" means the TrackInfo plus the vertical ruler.
  Confusing relative to LabelTrack labels.

  The TrackPanel manages multiple tracks and their TrackInfos.

  Note that with stereo tracks there will be one TrackInfo
  being used by two wavetracks.

*//*****************************************************************//**

\class TrackPanel::AudacityTimer
\brief Timer class dedicated to informing the TrackPanel that it
is time to refresh some aspect of the screen.

*//*****************************************************************/


#include "TrackPanel.h"
#include "TrackPanelConstants.h"
#include "TrackPanelDrawingContext.h"

#include <wx/setup.h> // for wxUSE_* macros

#include "AdornedRulerPanel.h"
#include "tracks/ui/CommonTrackPanelCell.h"
#include "KeyboardCapture.h"
#include "PendingTracks.h"
#include "Project.h"
#include "ProjectAudioIO.h"
#include "ProjectAudioManager.h"
#include "ProjectHistory.h"
#include "ProjectWindows.h"
#include "ProjectSettings.h"
#include "ProjectStatus.h"
#include "ProjectTimeRuler.h"
#include "ProjectWindow.h"
#include "SyncLock.h"
#include "Theme.h"
#include "TrackArt.h"
#include "TrackPanelMouseEvent.h"

#include "UndoManager.h"
#include "UIHandle.h"

#include "AColor.h"
#include "AllThemeResources.h"
#include "AudioIO.h"
#include "float_cast.h"

#include "Prefs.h"
#include "RefreshCode.h"
#include "TrackArtist.h"
#include "TrackPanelAx.h"
#include "TrackPanelResizerCell.h"
#include "Viewport.h"
#include "WaveTrack.h"
#include "WaveChannelViewConstants.h"
#include "tracks/playabletrack/wavetrack/ui/WaveChannelView.h"

#include "FrameStatistics.h"
#include "HitTestResult.h"

#include "tracks/ui/TrackControls.h"
#include "tracks/ui/ChannelView.h"
#include "tracks/ui/ChannelVRulerControls.h"

//This loads the appropriate set of cursors, depending on platform.
#include "../images/Cursors.h"

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <deque>
#include <functional>
#include <map>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <vector>

#include <wx/app.h>
#include <wx/dc.h>
#include <wx/dcclient.h>
#include <wx/graphics.h>
#include <wx/weakref.h>

#include "RealtimeEffectManager.h"

BoolSetting SetSelectedTrackMultimode{
   L"/GUI/SetSelectedTrackMultimode", true
};

BoolSetting ShowContentTrack{
   L"/GUI/ShowContentTrack", true
};

BoolSetting ContentTrackEnabled{
   L"/GUI/ContentTrackEnabled", true
};

IntSetting ContentTrackHeightSetting{
   L"/GUI/ContentTrackHeight", 44
};

IntSetting ContentTrackIndexSetting{
   L"/GUI/ContentTrackIndex", 0
};

namespace {
enum class ContentTrackState
{
   Off,
   Silence,
   On
};

enum class ContentOverlayState
{
   Off,
   InaudibleOverlay,
   Overlay
};

constexpr int ContentTrackHeight = 44;
constexpr int ContentTrackStepPixels = 3;
constexpr size_t ContentTrackWindowSamples = 100;
constexpr double ContentTrackOffThreshold = 0.000011220184543; // -99 dBFS.
constexpr double ContentTrackOnThreshold = 0.01; // -40 dBFS.
constexpr double ContentTrackOverlayThreshold = 0.005623413252; // -45 dBFS.

struct SavedSelectedTrackView
{
   std::weak_ptr<WaveTrack> track;
   bool multiView{ false };
   WaveChannelSubViewPlacements placements;
};

using SelectedTrackViewMap = std::map<TrackId, SavedSelectedTrackView>;
std::unordered_map<TrackPanel *, SelectedTrackViewMap> sSelectedTrackMultimode;

struct ContentTrackSegment
{
   int x0{};
   int x1{};
   ContentTrackState state{ ContentTrackState::Off };
   ContentOverlayState overlay{ ContentOverlayState::Off };
};

struct ContentTrackAnalysis
{
   ContentTrackState state{ ContentTrackState::Off };
   ContentOverlayState overlay{ ContentOverlayState::Off };
};

bool SameContentAnalysis(
   const ContentTrackAnalysis &left, const ContentTrackAnalysis &right)
{
   return left.state == right.state && left.overlay == right.overlay;
}

struct ContentTrackRenderKey
{
   AudacityProject *project{};
   double hpos{};
   double zoom{};
   int leftOffset{};
   int width{};
   int height{};
   uint64_t generation{};

   bool operator==(const ContentTrackRenderKey &other) const
   {
      return project == other.project
         && hpos == other.hpos
         && zoom == other.zoom
         && leftOffset == other.leftOffset
         && width == other.width
         && height == other.height
         && generation == other.generation;
   }
};

struct ContentTrackRenderCache
{
   std::mutex mutex;
   std::shared_ptr<wxBitmap> bitmap;
   ContentTrackRenderKey readyKey;
   ContentTrackRenderKey runningKey;
   ContentTrackRenderKey scheduledKey;
   std::atomic<uint64_t> generation{ 0 };
   std::atomic<uint64_t> renderSerial{ 0 };
   bool hasReady{ false };
   bool running{ false };
   bool scheduled{ false };
};

ContentTrackRenderCache sContentTrackRender;

class ContentTrackThreadPool
{
public:
   ContentTrackThreadPool()
   {
      const auto cpus = std::thread::hardware_concurrency();
      const auto count = std::max(1u, cpus > 2 ? cpus - 2 : 1);
      mWorkers.reserve(count);
      for (auto ii = 0u; ii < count; ++ii) {
         mWorkers.emplace_back([this] {
            while (true) {
               std::function<void()> job;
               {
                  std::unique_lock<std::mutex> lock{ mMutex };
                  mCondition.wait(lock, [this] {
                     return mStop || !mJobs.empty();
                  });
                  if (mStop && mJobs.empty())
                     return;
                  job = std::move(mJobs.front());
                  mJobs.pop_front();
               }
               job();
            }
         });
      }
   }

   ~ContentTrackThreadPool()
   {
      {
         std::lock_guard<std::mutex> lock{ mMutex };
         mStop = true;
      }
      mCondition.notify_all();
      for (auto &worker : mWorkers) {
         if (worker.joinable())
            worker.join();
      }
   }

   unsigned Size() const
   {
      return std::max<size_t>(1, mWorkers.size());
   }

   void Post(std::function<void()> job)
   {
      {
         std::lock_guard<std::mutex> lock{ mMutex };
         mJobs.push_back(std::move(job));
      }
      mCondition.notify_one();
   }

private:
   mutable std::mutex mMutex;
   std::condition_variable mCondition;
   std::deque<std::function<void()>> mJobs;
   std::vector<std::thread> mWorkers;
   bool mStop{ false };
};

ContentTrackThreadPool &ContentTrackPool()
{
   static ContentTrackThreadPool pool;
   return pool;
}

ContentTrackState ContentStateForPeak(double peak)
{
   if (peak < ContentTrackOffThreshold)
      return ContentTrackState::Off;
   if (peak < ContentTrackOnThreshold)
      return ContentTrackState::Silence;
   return ContentTrackState::On;
}

wxColour ContentTrackColor(ContentTrackState state)
{
   switch (state) {
   case ContentTrackState::On:
      return wxColour(35, 150, 70);
   case ContentTrackState::Silence:
      return wxColour(188, 143, 38);
   case ContentTrackState::Off:
   default:
      return wxColour(48, 48, 52);
   }
}

wxColour ContentOverlayColor(ContentOverlayState state)
{
   switch (state) {
   case ContentOverlayState::Overlay:
      return wxColour(190, 45, 45);
   case ContentOverlayState::InaudibleOverlay:
      return wxColour(210, 180, 45);
   case ContentOverlayState::Off:
   default:
      return wxColour(45, 145, 70);
   }
}

ContentTrackAnalysis ClassifyContentWindow(
   const std::vector<std::shared_ptr<WaveTrack>> &tracks, double time)
{
   std::array<float, ContentTrackWindowSamples> buffer{};
   float peak = 0.0f;
   auto contributingTracks = 0;
   auto overlayTracks = 0;

   for (const auto &waveTrack : tracks) {
      float trackPeak = 0.0f;
      for (const auto pChannel : waveTrack->Channels()) {
         buffer.fill(0.0f);

         const auto start =
            std::max(sampleCount(0), pChannel->TimeToLongSamples(time));
         pChannel->GetFloats(
            buffer.data(), start, buffer.size(), FillFormat::fillZero, false);

         // The content lane is deliberately rough and cheap: one confirmed
         // 100-sample window per few screen pixels.  This single pass over the
         // fetched buffer feeds both the content state and overlay-risk state.
         for (const auto sample : buffer) {
            const auto magnitude = std::abs(sample);
            if (magnitude > trackPeak)
               trackPeak = magnitude;
         }
      }

      peak = std::max(peak, trackPeak);
      if (trackPeak >= ContentTrackOffThreshold)
         ++contributingTracks;
      if (trackPeak >= ContentTrackOverlayThreshold)
         ++overlayTracks;
   }

   ContentOverlayState overlay = ContentOverlayState::Off;
   if (overlayTracks > 1)
      overlay = ContentOverlayState::Overlay;
   else if (contributingTracks > 1)
      // More than one track is present, but not enough loud tracks to be a
      // definite overlay; show it as an inaudible/low-level overlap.
      overlay = ContentOverlayState::InaudibleOverlay;

   return { ContentStateForPeak(peak), overlay };
}

void AppendContentTrackSegment(std::vector<ContentTrackSegment> &segments,
   int x0, int x1, const ContentTrackAnalysis &analysis)
{
   if (x1 <= x0)
      return;

   if (!segments.empty()) {
      auto &last = segments.back();
      if (last.x1 == x0
          && last.state == analysis.state
          && last.overlay == analysis.overlay) {
         last.x1 = x1;
         return;
      }
   }

   segments.push_back({ x0, x1, analysis.state, analysis.overlay });
}

std::vector<ContentTrackSegment> BuildContentTrackSegmentsRange(
   const std::vector<std::shared_ptr<WaveTrack>> &tracks,
   const ContentTrackRenderKey &key, int rangeStart, int rangeEnd,
   uint64_t renderSerial)
{
   std::vector<ContentTrackSegment> segments;
   if (rangeEnd <= rangeStart)
      return segments;

   ContentTrackAnalysis currentAnalysis;
   auto segmentStart = rangeStart;
   bool haveSegment = false;

   for (auto x = rangeStart; x < rangeEnd; x += ContentTrackStepPixels) {
      if (sContentTrackRender.generation.load(std::memory_order_relaxed)
          != key.generation
          || sContentTrackRender.renderSerial.load(std::memory_order_relaxed)
          != renderSerial)
         return {};

      const auto time =
         std::max(0.0, key.hpos + (x - key.leftOffset) / key.zoom);
      const auto analysis = ClassifyContentWindow(tracks, time);

      if (!haveSegment) {
         currentAnalysis = analysis;
         segmentStart = x;
         haveSegment = true;
      }
      else if (!SameContentAnalysis(analysis, currentAnalysis)) {
         AppendContentTrackSegment(
            segments, segmentStart, x, currentAnalysis);
         currentAnalysis = analysis;
         segmentStart = x;
      }
   }

   if (haveSegment)
      AppendContentTrackSegment(
         segments, segmentStart, rangeEnd, currentAnalysis);

   return segments;
}

unsigned ContentTrackWorkerCount(int width)
{
   const auto steps =
      std::max(1, (width + ContentTrackStepPixels - 1) / ContentTrackStepPixels);
   const auto wanted = ContentTrackPool().Size();
   return std::max(1u, std::min<unsigned>(wanted, steps));
}

std::vector<ContentTrackSegment> BuildContentTrackSegments(
   const std::vector<std::shared_ptr<WaveTrack>> &tracks,
   const ContentTrackRenderKey &key, uint64_t renderSerial)
{
   std::vector<ContentTrackSegment> segments;
   if (key.width <= key.leftOffset)
      return segments;

   const auto dataWidth = key.width - key.leftOffset;
   const auto workerCount = ContentTrackWorkerCount(dataWidth);
   if (workerCount == 1)
      return BuildContentTrackSegmentsRange(
         tracks, key, key.leftOffset, key.width, renderSerial);

   std::vector<std::vector<ContentTrackSegment>> chunks(workerCount);
   std::mutex doneMutex;
   std::condition_variable doneCondition;
   auto remaining = workerCount;
   auto &pool = ContentTrackPool();

   for (auto ii = 0u; ii < workerCount; ++ii) {
      const auto chunkStart =
         key.leftOffset + static_cast<int>((dataWidth * ii) / workerCount);
      const auto chunkEnd =
         key.leftOffset + static_cast<int>((dataWidth * (ii + 1)) / workerCount);

      pool.Post([&, ii, chunkStart, chunkEnd] {
         chunks[ii] = BuildContentTrackSegmentsRange(
            tracks, key, chunkStart, chunkEnd, renderSerial);
         {
            std::lock_guard<std::mutex> lock{ doneMutex };
            --remaining;
         }
         doneCondition.notify_one();
      });
   }

   {
      std::unique_lock<std::mutex> lock{ doneMutex };
      doneCondition.wait(lock, [&] { return remaining == 0; });
   }

   for (auto &chunk : chunks) {
      for (const auto &segment : chunk) {
         AppendContentTrackSegment(
            segments, segment.x0, segment.x1,
            { segment.state, segment.overlay });
      }
   }

   return segments;
}

void InvalidateContentTrackRender()
{
   sContentTrackRender.generation.fetch_add(1, std::memory_order_relaxed);
   sContentTrackRender.renderSerial.fetch_add(1, std::memory_order_relaxed);
   std::lock_guard<std::mutex> lock{ sContentTrackRender.mutex };
   sContentTrackRender.hasReady = false;
   sContentTrackRender.scheduled = false;
}

void DrawContentTrackSegment(wxDC &dc, ContentTrackState state,
   const wxRect &contentRect, int x0, int x1)
{
   if (x1 <= x0)
      return;

   dc.SetPen(*wxTRANSPARENT_PEN);
   dc.SetBrush(wxBrush(ContentTrackColor(state)));
   dc.DrawRectangle(x0, contentRect.y, x1 - x0, contentRect.height);
}

void DrawContentOverlaySegment(wxDC &dc, ContentOverlayState state,
   const wxRect &contentRect, int x0, int x1)
{
   if (x1 <= x0)
      return;

   dc.SetPen(*wxTRANSPARENT_PEN);
   dc.SetBrush(wxBrush(ContentOverlayColor(state)));
   dc.DrawRectangle(x0, contentRect.y, x1 - x0, contentRect.height);
}

wxBitmap MakeContentTrackBitmap(
   const ContentTrackRenderKey &key,
   const std::vector<ContentTrackSegment> &segments)
{
   wxBitmap bitmap{ key.width, key.height };
   wxMemoryDC dc{ bitmap };

   wxRect rect{ 0, 0, key.width, key.height };
   const auto leftOffset = std::clamp(key.leftOffset, 0, key.width);
   const wxRect labelRect{ 0, 0, leftOffset, key.height };
   const wxRect contentRect{ leftOffset, 0, key.width - leftOffset, key.height };
   const auto topHeight = std::max(1, contentRect.height / 2);
   const wxRect contentTop{
      contentRect.x, contentRect.y, contentRect.width, topHeight };
   const wxRect contentBottom{
      contentRect.x, contentRect.y + topHeight, contentRect.width,
      contentRect.height - topHeight };
   const auto labelTopHeight = std::max(1, labelRect.height / 2);

   dc.SetPen(*wxTRANSPARENT_PEN);
   dc.SetBrush(wxBrush(wxColour(36, 36, 40)));
   dc.DrawRectangle(labelRect);
   dc.SetTextForeground(wxColour(245, 245, 245));
   dc.DrawText(_("Content"), labelRect.x + 4, labelRect.y + 2);
   dc.DrawText(_("Overlay"), labelRect.x + 4, labelRect.y + labelTopHeight + 2);
   dc.DrawText(ContentTrackEnabled.Read() ? _("Disable") : _("Enable"),
      std::max(labelRect.x + 4, labelRect.GetRight() - 62),
      labelRect.y + labelTopHeight + 2);

   dc.SetBrush(wxBrush(wxColour(70, 70, 74)));
   dc.DrawRectangle(contentRect);

   for (const auto &segment : segments) {
      DrawContentTrackSegment(dc, segment.state, contentTop,
         std::max(segment.x0, contentTop.x),
         std::min(segment.x1, contentTop.GetRight() + 1));
      DrawContentOverlaySegment(dc, segment.overlay, contentBottom,
         std::max(segment.x0, contentBottom.x),
         std::min(segment.x1, contentBottom.GetRight() + 1));
   }

   dc.SetPen(wxPen(wxColour(10, 10, 10), 1));
   dc.SetBrush(*wxTRANSPARENT_BRUSH);
   dc.DrawRectangle(rect);
   AColor::Line(dc, rect.x, rect.y + labelTopHeight,
      rect.GetRight(), rect.y + labelTopHeight);
   dc.SelectObject(wxNullBitmap);

   return bitmap;
}

void StartContentTrackRender(TrackPanel &panel, const ContentTrackRenderKey &key)
{
   const auto trackList = panel.GetTracks();
   const auto viewInfo = panel.GetViewInfo();
   if (!trackList || !viewInfo)
      return;

   bool shouldStartDebounce = false;
   {
      std::lock_guard<std::mutex> lock{ sContentTrackRender.mutex };
      if ((sContentTrackRender.hasReady
             && sContentTrackRender.readyKey == key)
          || (sContentTrackRender.running
             && sContentTrackRender.runningKey == key))
         return;

      // Repeated scroll/zoom paints update one pending key.  This avoids a
      // sleeping-thread pileup while still cancelling obsolete active renders.
      sContentTrackRender.renderSerial.fetch_add(1, std::memory_order_relaxed);
      shouldStartDebounce = !sContentTrackRender.scheduled;
      sContentTrackRender.scheduled = true;
      sContentTrackRender.scheduledKey = key;
   }

   if (!shouldStartDebounce)
      return;

   std::vector<std::shared_ptr<WaveTrack>> waveTracks;
   for (auto track : trackList->Any<WaveTrack>())
      waveTracks.push_back(track->SharedPointer<WaveTrack>());

   wxWeakRef<TrackPanel> weakPanel{ &panel };
   std::thread{
      [waveTracks = std::move(waveTracks), weakPanel] {
         std::this_thread::sleep_for(std::chrono::milliseconds(200));
         ContentTrackRenderKey key;
         uint64_t renderSerial{};
         {
            std::lock_guard<std::mutex> lock{ sContentTrackRender.mutex };
            if (!sContentTrackRender.scheduled
                || sContentTrackRender.generation.load(std::memory_order_relaxed)
                   != sContentTrackRender.scheduledKey.generation)
               return;
            key = sContentTrackRender.scheduledKey;
            sContentTrackRender.scheduled = false;
            sContentTrackRender.running = true;
            sContentTrackRender.runningKey = key;
            renderSerial =
               sContentTrackRender.renderSerial.load(std::memory_order_relaxed);
         }

         auto segments = BuildContentTrackSegments(waveTracks, key, renderSerial);

         const auto currentGeneration =
            sContentTrackRender.generation.load(std::memory_order_relaxed);
         const auto currentRenderSerial =
            sContentTrackRender.renderSerial.load(std::memory_order_relaxed);
         {
            std::lock_guard<std::mutex> lock{ sContentTrackRender.mutex };
            sContentTrackRender.running = false;
            if (currentGeneration != key.generation
                || currentRenderSerial != renderSerial)
               return;
         }

         if (wxTheApp) {
            wxTheApp->CallAfter(
               [weakPanel, key, renderSerial, segments = std::move(segments)] {
               if (sContentTrackRender.generation.load(std::memory_order_relaxed)
                   != key.generation
                   || sContentTrackRender.renderSerial.load(std::memory_order_relaxed)
                   != renderSerial)
                  return;

               auto bitmap = MakeContentTrackBitmap(key, segments);
               {
                  std::lock_guard<std::mutex> lock{ sContentTrackRender.mutex };
                  if (sContentTrackRender.generation.load(std::memory_order_relaxed)
                      != key.generation
                      || sContentTrackRender.renderSerial.load(std::memory_order_relaxed)
                      != renderSerial)
                     return;
                  sContentTrackRender.readyKey = key;
                  sContentTrackRender.bitmap =
                     std::make_shared<wxBitmap>(std::move(bitmap));
                  sContentTrackRender.hasReady = true;
               }

               if (weakPanel)
                  weakPanel->Refresh(false);
            });
         }
      }
   }.detach();
}

void DrawContentTrack(TrackPanel &panel, wxDC &dc, const wxRect &rect)
{
   if (!ShowContentTrack.Read())
      return;

   const auto viewInfo = panel.GetViewInfo();
   const auto project = panel.GetProject();
   if (!viewInfo || !project || rect.width <= 0 || rect.height <= 0)
      return;

   const auto leftOffset =
      std::clamp(viewInfo->GetLeftOffset(), rect.x, rect.GetRight() + 1);
   if (rect.GetRight() + 1 - leftOffset <= 0)
      return;

   if (!ContentTrackEnabled.Read()) {
      const wxRect labelRect{ rect.x, rect.y, leftOffset - rect.x, rect.height };
      const wxRect contentRect{
         leftOffset, rect.y, rect.GetRight() + 1 - leftOffset, rect.height };
      dc.SetPen(*wxTRANSPARENT_PEN);
      dc.SetBrush(wxBrush(wxColour(36, 36, 40)));
      dc.DrawRectangle(labelRect);
      dc.SetTextForeground(wxColour(245, 245, 245));
      dc.DrawText(_("Content"), labelRect.x + 4, labelRect.y + 2);
      dc.DrawText(_("Enable"),
         std::max(labelRect.x + 4, labelRect.GetRight() - 62),
         labelRect.y + rect.height / 2 + 2);
      dc.SetBrush(wxBrush(wxColour(58, 58, 62)));
      dc.DrawRectangle(contentRect);
      dc.SetPen(wxPen(wxColour(10, 10, 10), 1));
      dc.SetBrush(*wxTRANSPARENT_BRUSH);
      dc.DrawRectangle(rect);
      return;
   }

   const ContentTrackRenderKey key{
      project, viewInfo->hpos, viewInfo->GetZoom(), leftOffset - rect.x,
      rect.width, rect.height,
      sContentTrackRender.generation.load(std::memory_order_relaxed)
   };

   std::shared_ptr<wxBitmap> bitmap;
   bool hasReady = false;
   {
      std::lock_guard<std::mutex> lock{ sContentTrackRender.mutex };
      hasReady = sContentTrackRender.hasReady
         && sContentTrackRender.readyKey == key;
      if (hasReady)
         bitmap = sContentTrackRender.bitmap;
   }

   if (hasReady && bitmap && bitmap->IsOk()) {
      wxMemoryDC source{ *bitmap };
      dc.Blit(rect.x, rect.y, rect.width, rect.height, &source, 0, 0);
      source.SelectObject(wxNullBitmap);
   }
   else {
      const wxRect labelRect{ rect.x, rect.y, leftOffset - rect.x, rect.height };
      const wxRect contentRect{
         leftOffset, rect.y, rect.GetRight() + 1 - leftOffset, rect.height };
      dc.SetPen(*wxTRANSPARENT_PEN);
      dc.SetBrush(wxBrush(wxColour(36, 36, 40)));
      dc.DrawRectangle(labelRect);
      dc.SetTextForeground(wxColour(245, 245, 245));
      dc.DrawText(_("Content"), labelRect.x + 4, labelRect.y + 2);
      dc.DrawText(ContentTrackEnabled.Read() ? _("Disable") : _("Enable"),
         std::max(labelRect.x + 4, labelRect.GetRight() - 62),
         labelRect.y + rect.height / 2 + 2);
      dc.SetBrush(wxBrush(wxColour(70, 70, 74)));
      dc.DrawRectangle(contentRect);
      if (ContentTrackEnabled.Read())
         StartContentTrackRender(panel, key);

      dc.SetPen(wxPen(wxColour(10, 10, 10), 1));
      dc.SetBrush(*wxTRANSPARENT_BRUSH);
      dc.DrawRectangle(rect);
   }
}

class ContentTrackResizeHandle final : public UIHandle
{
public:
   explicit ContentTrackResizeHandle(int y)
      : mMouseClickY{ y }
      , mInitialHeight{
           std::clamp(ContentTrackHeightSetting.Read(), 24, 240)
        }
   {}

   Result Click(
      const TrackPanelMouseEvent &, AudacityProject *) override
   {
      return RefreshCode::RefreshNone;
   }

   Result Drag(
      const TrackPanelMouseEvent &event, AudacityProject *) override
   {
      const auto delta = event.event.m_y - mMouseClickY;
      const auto height = std::clamp(mInitialHeight + delta, 24, 240);
      ContentTrackHeightSetting.Write(height);
      InvalidateContentTrackRender();
      return RefreshCode::RefreshAll | RefreshCode::FixScrollbars;
   }

   HitTestPreview Preview(
      const TrackPanelMouseState &, AudacityProject *) override
   {
      static wxCursor resizeCursor{ wxCURSOR_SIZENS };
      return { XO("Click and drag to resize the content track."), &resizeCursor };
   }

   Result Release(
      const TrackPanelMouseEvent &, AudacityProject *, wxWindow *) override
   {
      gPrefs->Flush();
      return RefreshCode::RefreshAll | RefreshCode::FixScrollbars;
   }

   Result Cancel(AudacityProject *) override
   {
      ContentTrackHeightSetting.Write(mInitialHeight);
      InvalidateContentTrackRender();
      return RefreshCode::RefreshAll | RefreshCode::FixScrollbars;
   }

   std::shared_ptr<const Track> FindTrack() const override { return {}; }

private:
   int mMouseClickY{};
   int mInitialHeight{};
};

int ContentTrackIndexForY(TrackPanel &panel, int y)
{
   const auto viewInfo = panel.GetViewInfo();
   const auto tracks = panel.GetTracks();
   if (!viewInfo || !tracks)
      return 0;

   auto absoluteY = y + viewInfo->vpos - kTopMargin;
   auto index = 0;
   auto yy = 0;
   for (const auto pTrack : *tracks) {
      wxCoord height = 0;
      for (auto pChannel : pTrack->Channels())
         height += ChannelView::Get(*pChannel).GetHeight();

      if (absoluteY < yy + height / 2)
         return index;

      yy += height;
      ++index;
   }
   return index;
}

class ContentTrackMoveHandle final : public UIHandle
{
public:
   Result Click(
      const TrackPanelMouseEvent &, AudacityProject *) override
   {
      return RefreshCode::RefreshNone;
   }

   Result Drag(
      const TrackPanelMouseEvent &event, AudacityProject *project) override
   {
      auto &panel = TrackPanel::Get(*project);
      const auto index = ContentTrackIndexForY(panel, event.event.m_y);
      if (index != ContentTrackIndexSetting.Read()) {
         ContentTrackIndexSetting.Write(index);
         InvalidateContentTrackRender();
         return RefreshCode::RefreshAll | RefreshCode::FixScrollbars;
      }
      return RefreshCode::RefreshNone;
   }

   HitTestPreview Preview(
      const TrackPanelMouseState &, AudacityProject *) override
   {
      static wxCursor moveCursor{ wxCURSOR_SIZING };
      return { XO("Click and drag to move the content track."), &moveCursor };
   }

   Result Release(
      const TrackPanelMouseEvent &, AudacityProject *, wxWindow *) override
   {
      gPrefs->Flush();
      return RefreshCode::RefreshAll | RefreshCode::FixScrollbars;
   }

   Result Cancel(AudacityProject *) override
   {
      return RefreshCode::RefreshAll | RefreshCode::FixScrollbars;
   }

   std::shared_ptr<const Track> FindTrack() const override { return {}; }
};

class ContentTrackEnableHandle final : public UIHandle
{
public:
   Result Click(
      const TrackPanelMouseEvent &, AudacityProject *) override
   {
      ContentTrackEnabled.Toggle();
      gPrefs->Flush();
      InvalidateContentTrackRender();
      return RefreshCode::RefreshAll;
   }

   Result Drag(
      const TrackPanelMouseEvent &, AudacityProject *) override
   {
      return RefreshCode::RefreshNone;
   }

   HitTestPreview Preview(
      const TrackPanelMouseState &, AudacityProject *) override
   {
      static wxCursor cursor{ wxCURSOR_HAND };
      return {
         ContentTrackEnabled.Read()
            ? XO("Disable content track updates.")
            : XO("Enable content track updates."),
         &cursor
      };
   }

   Result Release(
      const TrackPanelMouseEvent &, AudacityProject *, wxWindow *) override
   {
      return RefreshCode::RefreshNone;
   }

   Result Cancel(AudacityProject *) override
   {
      return RefreshCode::RefreshNone;
   }

   std::shared_ptr<const Track> FindTrack() const override { return {}; }
};

struct ContentTrackCell final : CommonTrackPanelCell {
   std::vector< UIHandlePtr > HitTest(
      const TrackPanelMouseState &st, const AudacityProject *pProject) override
   {
      (void)pProject;
      const auto leftOffset = st.rect.x + kTrackInfoWidth;
      if (st.state.m_x < leftOffset
          && st.state.m_x >= leftOffset - 68
          && st.state.m_y >= st.rect.y + st.rect.height / 2) {
         auto result = std::make_shared<ContentTrackEnableHandle>();
         result = AssignUIHandlePtr(mEnableHandle, result);
         return { result };
      }

      if (st.state.m_y >= st.rect.GetBottom() - kTrackSeparatorThickness - 3) {
         auto result =
            std::make_shared<ContentTrackResizeHandle>(st.state.m_y);
         result = AssignUIHandlePtr(mResizeHandle, result);
         return { result };
      }

      auto result = std::make_shared<ContentTrackMoveHandle>();
      result = AssignUIHandlePtr(mMoveHandle, result);
      return { result };
   }

   std::shared_ptr< Track > DoFindTrack() override { return {}; }

   void Draw(
      TrackPanelDrawingContext &context,
      const wxRect &rect, unsigned iPass ) override
   {
      if (iPass == TrackArtist::PassTracks)
         DrawContentTrack(*TrackArtist::Get(context)->parent, context.dc, rect);

      if (iPass == TrackArtist::PassBorders) {
         context.dc.SetBrush(*wxTRANSPARENT_BRUSH);
         context.dc.SetPen(*wxBLACK_PEN);
         context.dc.DrawRectangle(rect);
      }
   }

   static std::shared_ptr<ContentTrackCell> Instance()
   {
      static auto instance = std::make_shared< ContentTrackCell >();
      return instance;
   }

   std::weak_ptr<ContentTrackResizeHandle> mResizeHandle;
   std::weak_ptr<ContentTrackMoveHandle> mMoveHandle;
   std::weak_ptr<ContentTrackEnableHandle> mEnableHandle;
};
}

static_assert( kVerticalPadding == kTopMargin + kBottomMargin );
static_assert( kTrackInfoTitleHeight + kTrackInfoTitleExtra == kAffordancesAreaHeight, "Drag bar is misaligned with the menu button");

/**

\class TrackPanel

This is a diagram of TrackPanel's division of one (non-stereo) track rectangle.
Total height equals ChannelView::GetHeight()'s value.  Total width is the wxWindow's
width.  Each character that is not . represents one pixel.

Inset space of this track, and top inset of the next track, are used to draw the
focus highlight.

Top inset of the right channel of a stereo track, and bottom shadow line of the
left channel, are used for the channel separator.

"Margin" is a term used for inset plus border (top and left) or inset plus
shadow plus border (right and bottom).

GetVRulerOffset() counts columns from the left edge up to and including
controls, and is a constant.

GetVRulerWidth() is variable -- all tracks have the same ruler width at any
time, but that width may be adjusted when tracks change their vertical scales.

GetLeftOffset() counts columns up to and including the VRuler and one more,
the "one pixel" column.

Cell for label has a rectangle that OMITS left, top, and bottom
margins

Cell for vruler has a rectangle right of the label,
up to and including the One Pixel column, and OMITS top and bottom margins

Cell() for track returns a rectangle with x == GetLeftOffset(), and OMITS
right, top, and bottom margins

+--------------- ... ------ ... --------------------- ...       ... -------------+
| Top Inset                                                                      |
|                                                                                |
|  +------------ ... ------ ... --------------------- ...       ... ----------+  |
| L|+-Border---- ... ------ ... --------------------- ...       ... -Border-+ |R |
| e||+---------- ... -++--- ... -+++----------------- ...       ... -------+| |i |
| f|B|                ||         |||                                       |BS|g |
| t|o| Controls       || V       |O|  The good stuff                       |oh|h |
|  |r|                || R       |n|                                       |ra|t |
| I|d|                || u       |e|                                       |dd|  |
| n|e|                || l       | |                                       |eo|I |
| s|r|                || e       |P|                                       |rw|n |
| e|||                || r       |i|                                       ||||s |
| t|||                ||         |x|                                       ||||e |
|  |||                ||         |e|                                       ||||t |
|  |||                ||         |l|                                       ||||  |
|  |||                ||         |||                                       ||||  |

.  ...                ..         ...                                       ....  .
.  ...                ..         ...                                       ....  .
.  ...                ..         ...                                       ....  .

|  |||                ||         |||                                       ||||  |
|  ||+----------     -++--  ... -+++----------------- ...       ... -------+|||  |
|  |+-Border---- ... -----  ... --------------------- ...       ... -Border-+||  |
|  |  Shadow---- ... -----  ... --------------------- ...       ... --Shadow-+|  |
*/

// Is the distance between A and B less than D?
template < class A, class B, class DIST > bool within(A a, B b, DIST d)
{
   return (a > b - d) && (a < b + d);
}

BEGIN_EVENT_TABLE(TrackPanel, CellularPanel)
    EVT_MOUSE_EVENTS(TrackPanel::OnMouseEvent)
    EVT_KEY_DOWN(TrackPanel::OnKeyDown)

    EVT_PAINT(TrackPanel::OnPaint)

    EVT_TIMER(wxID_ANY, TrackPanel::OnTimer)

    EVT_SIZE(TrackPanel::OnSize)

END_EVENT_TABLE()

/// Makes a cursor from an XPM, uses CursorId as a fallback.
/// TODO:  Move this function to some other source file for reuse elsewhere.
std::unique_ptr<wxCursor> MakeCursor( int WXUNUSED(CursorId), const char * const pXpm[36],  int HotX, int HotY )
{
#define CURSORS_SIZE32
#ifdef CURSORS_SIZE32
   const int HotAdjust =0;
#else
   const int HotAdjust =8;
#endif

   wxImage Image = wxImage(wxBitmap(pXpm).ConvertToImage());
   Image.SetMaskColour(255,0,0);
   Image.SetMask();// Enable mask.

   Image.SetOption( wxIMAGE_OPTION_CUR_HOTSPOT_X, HotX-HotAdjust );
   Image.SetOption( wxIMAGE_OPTION_CUR_HOTSPOT_Y, HotY-HotAdjust );
   return std::make_unique<wxCursor>( Image );
}


namespace{

AttachedWindows::RegisteredFactory sKey{
   []( AudacityProject &project ) -> wxWeakRef< wxWindow > {
      auto &ruler = AdornedRulerPanel::Get( project );
      auto &viewInfo = ViewInfo::Get( project );
      auto &window = ProjectWindow::Get( project );
      auto mainPage = window.GetTrackListWindow();
      wxASSERT( mainPage ); // to justify safenew

      auto &tracks = TrackList::Get( project );
      auto result = safenew TrackPanel(mainPage,
         window.NextWindowID(),
         wxDefaultPosition,
         wxDefaultSize,
         tracks.shared_from_this(),
         &viewInfo,
         &project,
         &ruler);
      SetProjectPanel( project, *result );
      return result;
   }
};

}

TrackPanel &TrackPanel::Get( AudacityProject &project )
{
   return GetAttachedWindows(project).Get< TrackPanel >( sKey );
}

const TrackPanel &TrackPanel::Get( const AudacityProject &project )
{
   return Get( const_cast< AudacityProject & >( project ) );
}

void TrackPanel::Destroy( AudacityProject &project )
{
   auto *pPanel = GetAttachedWindows(project).Find<TrackPanel>( sKey );
   if (pPanel) {
      pPanel->wxWindow::Destroy();
      GetAttachedWindows(project).Assign(sKey, nullptr);
   }
}

// Don't warn us about using 'this' in the base member initializer list.
#ifndef __WXGTK__ //Get rid if this pragma for gtk
#pragma warning( disable: 4355 )
#endif
TrackPanel::TrackPanel(wxWindow * parent, wxWindowID id,
                       const wxPoint & pos,
                       const wxSize & size,
                       const std::shared_ptr<TrackList> &tracks,
                       ViewInfo * viewInfo,
                       AudacityProject * project,
                       AdornedRulerPanel * ruler)
   : CellularPanel(parent, id, pos, size, viewInfo,
                   wxWANTS_CHARS | wxNO_BORDER),
     mTracks(tracks),
     mRuler(ruler),
     mTrackArtist(nullptr),
     mRefreshBacking(false)
#ifndef __WXGTK__   //Get rid if this pragma for gtk
#pragma warning( default: 4355 )
#endif
{
   SetLayoutDirection(wxLayout_LeftToRight);
   SetLabel(XO("Track Panel"));
   SetName(XO("Track Panel"));
   SetBackgroundStyle(wxBG_STYLE_PAINT);

#if wxUSE_ACCESSIBILITY
   // Inject finder of track rectangles into the accessibility helper
   {
      const auto finder = [
         weakThis = wxWeakRef<TrackPanel>{ this }
      ] (const Track &track) -> wxRect {
         if (weakThis)
            return weakThis->FindTrackRect(&track);
         return {};
      };
      auto &focus = TrackFocus::Get(*GetProject());
      auto &viewport = Viewport::Get(*GetProject());
      TrackPanelAx *pAx{};
      SetAccessible(pAx =
         safenew TrackPanelAx{
            viewport.weak_from_this(), focus.weak_from_this(), finder });
      focus.SetCallbacks(std::make_unique<TrackPanelAx::Adapter>(pAx));
   }
#endif

   mTrackArtist = std::make_unique<TrackArtist>( this );

   mTimeCount = 0;
   mTimer.parent = this;
   // Timer is started after the window is visible
   ProjectWindow::Get( *GetProject() ).Bind(wxEVT_IDLE,
      &TrackPanel::OnIdle, this);

   // Register for tracklist updates
   mTrackListSubscription = PendingTracks::Get(*GetProject())
   .Subscribe([this](const TrackListEvent &event){
      InvalidateContentTrackRender();
      switch (event.mType) {
      case TrackListEvent::SELECTION_CHANGE:
         UpdateSelectedTrackMultimode(); break;
      case TrackListEvent::RESIZING:
      case TrackListEvent::ADDITION:
         OnTrackListResizing(event); break;
      case TrackListEvent::DELETION:
         UpdateSelectedTrackMultimode();
         OnTrackListDeletion(); break;
      default:
         break;
      }
   });

   auto theProject = GetProject();
   mSyncLockSubscription = SyncLockState::Get(*theProject)
      .Subscribe(*this, &TrackPanel::OnSyncLockChange);

   mFocusChangeSubscription = TrackFocus::Get(*theProject)
      .Subscribe(*this, &TrackPanel::OnTrackFocusChange);

   mUndoSubscription = UndoManager::Get(*theProject)
      .Subscribe(*this, &TrackPanel::OnUndoReset);

   mAudioIOSubscription =
      AudioIO::Get()->Subscribe(*this, &TrackPanel::OnAudioIO);

   mRealtimeEffectManagerSubscription = RealtimeEffectManager::Get(*theProject)
      .Subscribe([this](const RealtimeEffectManagerMessage& msg)
      {
         if (auto pTrack = dynamic_cast<Track *>(msg.group))
            //update "effects" button
            RefreshTrack(pTrack);
      });

   mProjectRulerInvalidatedSubscription =
      ProjectTimeRuler::Get(*theProject).GetRuler().Subscribe([this](auto mode) { Refresh(); });
   mSelectionSubscription = viewInfo->selectedRegion
      .Subscribe([this](auto&){ Refresh(false); });

   UpdatePrefs();
   UpdateSelectedTrackMultimode();
}

void TrackPanel::UpdateSelectedTrackMultimode()
{
   auto &savedViews = sSelectedTrackMultimode[this];

   auto restore = [this, &savedViews](SelectedTrackViewMap::iterator it) {
      if (auto track = it->second.track.lock()) {
         auto &view = WaveChannelView::GetFirst(*track);
         view.SetMultiView(it->second.multiView);
         view.RestorePlacements(it->second.placements);
         UpdateVRuler(track.get());
      }
      return savedViews.erase(it);
   };

   if (!SetSelectedTrackMultimode.Read()) {
      for (auto it = savedViews.begin(); it != savedViews.end(); )
         it = restore(it);
      Refresh(false);
      return;
   }

   for (auto it = savedViews.begin(); it != savedViews.end(); ) {
      auto track = it->second.track.lock();
      if (!track || !track->GetSelected())
         it = restore(it);
      else
         ++it;
   }

   bool changed = false;
   for (auto track : mTracks->Selected<WaveTrack>()) {
      auto &view = WaveChannelView::GetFirst(*track);
      auto displays = view.GetDisplays();
      auto &entry = savedViews[track->GetId()];
      if (!entry.track.expired())
         continue;

      entry.track = track->SharedPointer<WaveTrack>();
      entry.multiView = view.GetMultiView();
      entry.placements = view.SavePlacements();

      // Preserve the user's top view while temporarily showing both waveform
      // and spectrum for the selected track.
      const auto display = displays.empty()
         ? WaveChannelViewConstants::Waveform
         : displays.begin()->id;
      view.SetMultiView(true);
      view.SetDisplay(display, false);
      UpdateVRuler(track);
      changed = true;
   }

   if (changed)
      Refresh(false);
}


TrackPanel::~TrackPanel()
{
   sSelectedTrackMultimode.erase(this);
   mTimer.Stop();

   // This can happen if a label is being edited and the user presses
   // ALT+F4 or Command+Q
   if (HasCapture())
      ReleaseMouse();
}

void TrackPanel::UpdatePrefs()
{
   // All vertical rulers must be recalculated since the minimum and maximum
   // frequencies may have been changed.
   UpdateVRulers();

   Refresh();
}

/// Gets the pointer to the AudacityProject that
/// goes with this track panel.
AudacityProject * TrackPanel::GetProject() const
{
   auto window = GetParent();

   while(window != nullptr)
   {
      if(const auto projectWindow = dynamic_cast<ProjectWindow*>(window))
         return projectWindow->FindProject().get();

      window = window->GetParent();
   }
   return nullptr;
}

void TrackPanel::OnSize( wxSizeEvent &evt )
{
   evt.Skip();
   const auto &size = evt.GetSize();
   mViewInfo->SetWidth( size.GetWidth() );
   mViewInfo->SetHeight( size.GetHeight() );
}

void TrackPanel::OnIdle(wxIdleEvent& event)
{
   event.Skip();
   // The window must be ready when the timer fires (#1401)
   if (IsShownOnScreen())
   {
      mTimer.Start(std::chrono::milliseconds{kTimerInterval}.count(), FALSE);

      // Timer is started, we don't need the event anymore
      GetProjectFrame( *GetProject() ).Unbind(wxEVT_IDLE,
         &TrackPanel::OnIdle, this);
   }
   else
   {
      // Get another idle event, wx only guarantees we get one
      // event after "some other normal events occur"
      event.RequestMore();
   }
}

/// AS: This gets called on our wx timer events.
void TrackPanel::OnTimer(wxTimerEvent& )
{
   mTimeCount++;

   AudacityProject *const p = GetProject();
   auto &window = ProjectWindow::Get( *p );
   auto &viewport = Viewport::Get(*p);

   auto &projectAudioIO = ProjectAudioIO::Get( *p );
   auto gAudioIO = AudioIO::Get();

   // Check whether we were playing or recording, but the stream has stopped.
   if (projectAudioIO.GetAudioIOToken()>0 && !IsAudioActive())
   {
      //the stream may have been started up after this one finished (by some other project)
      //in that case reset the buttons don't stop the stream
      auto &projectAudioManager = ProjectAudioManager::Get( *p );
      projectAudioManager.Stop(!gAudioIO->IsStreamActive());
   }

   // Next, check to see if we were playing or recording
   // audio, but now Audio I/O is completely finished.
   if (projectAudioIO.GetAudioIOToken()>0 &&
         !gAudioIO->IsAudioTokenActive(projectAudioIO.GetAudioIOToken()))
   {
      projectAudioIO.SetAudioIOToken(0);
      viewport.Redraw();
   }
   if (mLastDrawnSelectedRegion != mViewInfo->selectedRegion) {
      UpdateSelectionDisplay();
   }

   // Notify listeners for timer ticks
   window.GetPlaybackScroller().OnTimer();

   DrawOverlays(false);
   mRuler->DrawOverlays(false);

   if(IsAudioActive() && gAudioIO->GetNumCaptureChannels()) {

      // Periodically update the display while recording

      if ((mTimeCount % 5) == 0) {
         // Must tell OnPaint() to recreate the backing bitmap
         // since we've not done a full refresh.
         mRefreshBacking = true;
         Refresh( false );
      }
   }
   if(mTimeCount > 1000)
      mTimeCount = 0;
}

void TrackPanel::OnSyncLockChange(SyncLockChangeMessage)
{
   Refresh(false);
}

void TrackPanel::OnUndoReset(UndoRedoMessage message)
{
   if (message.type == UndoRedoMessage::Reset) {
      TrackFocus::Get( *GetProject() ).Set( nullptr );
      Refresh( false );
   }
}

/// AS: OnPaint( ) is called during the normal course of
///  completing a repaint operation.
void TrackPanel::OnPaint(wxPaintEvent & /* event */)
{
   // If the selected region changes - we must repaint the tracks, because the
   // selection is baked into track image
   if (mLastDrawnSelectedRegion != mViewInfo->selectedRegion)
   {
      mRefreshBacking = true;
      mLastDrawnSelectedRegion = mViewInfo->selectedRegion;
   }

   auto sw =
      FrameStatistics::CreateStopwatch(FrameStatistics::SectionID::TrackPanel);

   {
      wxPaintDC dc(this);

      // Retrieve the damage rectangle
      wxRect box = GetUpdateRegion().GetBox();

      // Recreate the backing bitmap if we have a full refresh
      // (See TrackPanel::Refresh())
      if (mRefreshBacking || (box == GetRect()))
      {
         // Reset (should a mutex be used???)
         mRefreshBacking = false;

         // Redraw the backing bitmap
         DrawTracks(&GetBackingDCForRepaint());

         // Copy it to the display
         DisplayBitmap(dc);
      }
      else
      {
         // Copy full, possibly clipped, damage rectangle
         RepairBitmap(dc, box.x, box.y, box.width, box.height);
      }

      if (const auto sentinel =
             ProjectAudioManager::Get(*GetProject()).GetSentinelPlaybackPosition()) {
         const auto x = mViewInfo->TimeToPosition(
            *sentinel, mViewInfo->GetLeftOffset());
         if (x >= 0 && x < GetSize().GetWidth()) {
            // Ctrl-click places a persistent orange play-over anchor; draw it
            // over the whole track panel so it reads as one global marker.
            dc.SetPen(wxPen(wxColour(255, 128, 0), 1));
            AColor::Line(dc, x, 0, x, GetSize().GetHeight());
         }
      }

      // Done with the clipped DC

      // Drawing now goes directly to the client area.
      // DrawOverlays() may need to draw outside the clipped region.
      // (Used to make a NEW, separate wxClientDC, but that risks flashing
      // problems on Mac.)
      dc.DestroyClippingRegion();
      DrawOverlays(true, &dc);
   }
}

void TrackPanel::MakeParentRedrawScrollbars()
{
   Viewport::Get(*GetProject()).UpdateScrollbarsForTracks();
}

namespace {
   std::shared_ptr<Track> FindTrack(TrackPanelCell *pCell)
   {
      if (pCell)
         // FindTrack as applied through the CommonTrackPanelCell interface
         // will really find a track, though for now it finds a left or right
         // channel.
         return static_cast<CommonTrackPanelCell*>(pCell)->FindTrack();
      return {};
   }
}

void TrackPanel::ProcessUIHandleResult
   (TrackPanelCell *pClickedCell, TrackPanelCell *pLatestCell,
    UIHandle::Result refreshResult)
{
   const auto panel = this;
   auto pLatestTrack = FindTrack( pLatestCell ).get();

   // This precaution checks that the track is not only nonnull, but also
   // really owned by the track list
   auto pClickedTrack = GetTracks()->Lock(
      std::weak_ptr<Track>{ FindTrack( pClickedCell ) }
   ).get();

   // TODO:  make a finer distinction between refreshing the track control area,
   // and the waveform area.  As it is, redraw both whenever you must redraw either.

   // Copy data from the underlying tracks to the pending tracks that are
   // really displayed
   PendingTracks::Get(*panel->GetProject()).UpdatePendingTracks();

   using namespace RefreshCode;

   if (refreshResult & DestroyedCell) {
      panel->UpdateViewIfNoTracks();
      // Beware stale pointer!
      if (pLatestTrack == pClickedTrack)
         pLatestTrack = nullptr;
      pClickedTrack = nullptr;
   }

   if (pClickedTrack && (refreshResult & RefreshCode::UpdateVRuler))
      panel->UpdateVRuler(pClickedTrack);

   if (refreshResult & RefreshCode::DrawOverlays) {
      panel->DrawOverlays(false);
      mRuler->DrawOverlays(false);
   }

   // Refresh all if told to do so, or if told to refresh a track that
   // is not known.
   const bool refreshAll =
      (    (refreshResult & RefreshAll)
       || ((refreshResult & RefreshCell) && !pClickedTrack)
       || ((refreshResult & RefreshLatestCell) && !pLatestTrack));

   if (refreshAll)
      panel->Refresh(false);
   else {
      if (refreshResult & RefreshCell)
         panel->RefreshTrack(pClickedTrack);
      if (refreshResult & RefreshLatestCell)
         panel->RefreshTrack(pLatestTrack);
   }

   if (refreshResult & FixScrollbars)
      panel->MakeParentRedrawScrollbars();

   if (refreshResult & Resize)
      Viewport::Get(*GetProject()).HandleResize();

   if ((refreshResult & RefreshCode::EnsureVisible) && pClickedTrack) {
      auto & focus = TrackFocus::Get(*GetProject());
      focus.Set(pClickedTrack);
      if (const auto pFocus = focus.Get())
         Viewport::Get(*GetProject()).ShowTrack(*pFocus);
   }
}

void TrackPanel::HandlePageUpKey()
{
   Viewport::Get(*GetProject())
      .SetHorizontalThumb(2 * mViewInfo->hpos - mViewInfo->GetScreenEndTime());
}

void TrackPanel::HandlePageDownKey()
{
   Viewport::Get(*GetProject())
      .SetHorizontalThumb(mViewInfo->GetScreenEndTime());
}

bool TrackPanel::IsAudioActive()
{
   AudacityProject *p = GetProject();
   return ProjectAudioIO::Get( *p ).IsAudioActive();
}

void TrackPanel::UpdateStatusMessage( const TranslatableString &st )
{
   auto status = st;
   if (HasEscape())
      /* i18n-hint Esc is a key on the keyboard */
      status.Join( XO("(Esc to cancel)"), " " );
   ProjectStatus::Get( *GetProject() ).Set( status );
}

void TrackPanel::UpdateSelectionDisplay()
{
   // Full refresh since the label area may need to indicate
   // newly selected tracks.
   Refresh(false);

   // Make sure the ruler follows suit.
   mRuler->DrawSelection();
}

// Counts selected tracks, counting stereo tracks as one track.
size_t TrackPanel::GetSelectedTrackCount() const
{
   return GetTracks()->Selected().size();
}

void TrackPanel::UpdateViewIfNoTracks()
{
   if (mTracks->empty())
   {
      // BG: There are no more tracks on screen
      //BG: Set zoom to normal
      mViewInfo->SetZoom(ZoomInfo::GetDefaultZoom());

      //STM: Set selection to 0,0
      //PRL: and default the rest of the selection information
      mViewInfo->selectedRegion = SelectedRegion();

      // PRL:  Following causes the time ruler to align 0 with left edge.
      // Bug 972
      mViewInfo->hpos = 0;

      Viewport::Get(*GetProject()).HandleResize();
      //STM: Clear message if all tracks are removed
      ProjectStatus::Get( *GetProject() ).Set({});
   }
}

// The tracks positions within the list have changed, so update the vertical
// ruler size for the track that triggered the event.
void TrackPanel::OnTrackListResizing(const TrackListEvent &e)
{
   auto t = e.mpTrack.lock();
   // A deleted track can trigger the event.  In which case do nothing here.
   // A deleted track can have a valid pointer but no owner, bug 2060
   if( t && t->HasOwner() )
      UpdateVRuler(t.get());

   // fix for bug 2477
   MakeParentRedrawScrollbars();
}

// Tracks have been removed from the list.
void TrackPanel::OnTrackListDeletion()
{
   // copy shared_ptr for safety, as in HandleClick
   auto handle = Target();
   if (handle) {
      handle->OnProjectChange(GetProject());
   }

   // If the focused track disappeared but there are still other tracks,
   // this reassigns focus.
   TrackFocus( *GetProject() ).Get();

   UpdateVRulerSize();
}

void TrackPanel::OnKeyDown(wxKeyEvent & event)
{
   switch (event.GetKeyCode())
   {
      // Allow PageUp and PageDown keys to
      //scroll the Track Panel left and right
   case WXK_PAGEUP:
      HandlePageUpKey();
      return;

   case WXK_PAGEDOWN:
      HandlePageDownKey();
      return;

   default:
      // fall through to base class handler
      event.Skip();
   }
}

void TrackPanel::OnMouseEvent(wxMouseEvent & event)
{
   if (event.LeftDown()) {
      // wxTimers seem to be a little unreliable, so this
      // "primes" it to make sure it keeps going for a while...

      // When this timer fires, we call TrackPanel::OnTimer and
      // possibly update the screen for offscreen scrolling.
      mTimer.Stop();
      mTimer.Start(std::chrono::milliseconds{kTimerInterval}.count(), FALSE);
   }


   if (event.ButtonUp()) {
      //ShowTrack should be called after processing the up-click.
      this->CallAfter( [this, event]{
         const auto foundCell = FindCell(event.m_x, event.m_y);
         const auto t = FindTrack( foundCell.pCell.get() );
         if (t) {
            auto &focus = TrackFocus::Get(*GetProject());
            focus.Set(t.get());
            Viewport::Get(*GetProject()).ShowTrack(*t);
         }
      } );
   }

   // Must also fall through to base class handler
   event.Skip();
}

double TrackPanel::GetMostRecentXPos()
{
   return mViewInfo->PositionToTime(
      MostRecentXCoord(), mViewInfo->GetLeftOffset());
}

void TrackPanel::RefreshTrack(Track *trk, bool refreshbacking)
{
   if (!trk)
      return;

   auto height = ChannelView::GetChannelGroupHeight(trk);

   // Set rectangle top according to the scrolling position, `vpos`
   // Subtract the inset (above) and shadow (below) from the height of the
   // rectangle, but not the border
   // This matters because some separators do paint over the border
   auto &view = ChannelView::Get(*trk->GetChannel(0));
   const auto top =
      -mViewInfo->vpos + view.GetCumulativeHeightBefore() + kTopInset;
   height -= (kTopInset + kShadowThickness);

   // Width also subtracts insets (left and right) plus shadow (right)
   const auto left = kLeftInset;
   const auto width = GetRect().GetWidth()
      - (kLeftInset + kRightInset + kShadowThickness);

   wxRect rect(left, top, width, height);

   if( refreshbacking )
      mRefreshBacking = true;

   Refresh( false, &rect );
}


/// This method overrides Refresh() of wxWindow so that the
/// boolean play indicator can be set to false, so that an old play indicator that is
/// no longer there won't get  XORed (to erase it), thus redrawing it on the
/// TrackPanel
void TrackPanel::Refresh(bool eraseBackground /* = TRUE */,
                         const wxRect *rect /* = NULL */)
{
   // Tell OnPaint() to refresh the backing bitmap.
   //
   // Originally I had the check within the OnPaint() routine and it
   // was working fine.  That was until I found that, even though a full
   // refresh was requested, Windows only set the onscreen portion of a
   // window as damaged.
   //
   // So, if any part of the trackpanel was off the screen, full refreshes
   // didn't work and the display got corrupted.
   if( !rect || ( *rect == GetRect() ) )
   {
      mRefreshBacking = true;
   }
   wxWindow::Refresh(eraseBackground, rect);

   CallAfter([this]{
      if (GetProject())
         CellularPanel::HandleCursorForPresentMouseState(); } );
}

void TrackPanel::OnAudioIO(AudioIOEvent evt)
{
   if (evt.type == AudioIOEvent::MONITOR || evt.type == AudioIOEvent::PAUSE)
      return;
   // Some hit tests want to change their cursor to and from the ban symbol
   CallAfter( [this]{ CellularPanel::HandleCursorForPresentMouseState(); } );
}

/// Draw the actual track areas.  We only draw the borders
/// and the little buttons and menues and whatnot here, the
/// actual contents of each track are drawn by the TrackArtist.
void TrackPanel::DrawTracks(wxDC * dc)
{
   wxRegion region = GetUpdateRegion();

   const wxRect clip = GetRect();

   const SelectedRegion &sr = mViewInfo->selectedRegion;
   mTrackArtist->pSelectedRegion = &sr;
   const auto &pendingTracks = PendingTracks::Get(*GetProject());
   mTrackArtist->pPendingTracks = &pendingTracks;
   mTrackArtist->pZoomInfo = mViewInfo;
   TrackPanelDrawingContext context {
      *dc, Target(), mLastMouseState, mTrackArtist.get()
   };

   // Don't draw a bottom margin here.

   const auto &settings = ProjectSettings::Get( *GetProject() );
   bool bMultiToolDown =
      (ToolCodes::multiTool == settings.GetTool());
   bool envelopeFlag   =
      bMultiToolDown || (ToolCodes::envelopeTool == settings.GetTool());
   bool bigPointsFlag  =
      bMultiToolDown || (ToolCodes::drawTool == settings.GetTool());
   bool sliderFlag     = bMultiToolDown;
   bool brushFlag   = false;
#ifdef EXPERIMENTAL_BRUSH_TOOL
   brushFlag   = (ToolCodes::brushTool == settings.GetTool());
#endif

   const bool hasSolo = GetTracks()->Any<PlayableTrack>()
      .any_of( [&](const PlayableTrack *pt) {
         pt = static_cast<const PlayableTrack *>(
            &pendingTracks.SubstitutePendingChangedTrack(*pt));
         return pt->GetSolo();
      } );

   mTrackArtist->drawEnvelope = envelopeFlag;
   mTrackArtist->bigPoints = bigPointsFlag;
   mTrackArtist->drawSliders = sliderFlag;
   mTrackArtist->onBrushTool = brushFlag;
   mTrackArtist->hasSolo = hasSolo;

   this->CellularPanel::Draw( context, TrackArtist::NPasses );
}

void TrackPanel::SetBackgroundCell
(const std::shared_ptr< CommonTrackPanelCell > &pCell)
{
   mpBackground = pCell;
}

std::shared_ptr< CommonTrackPanelCell > TrackPanel::GetBackgroundCell()
{
   return mpBackground;
}

namespace {
std::vector<int> FindAdjustedChannelHeights(Track &t)
{
   auto channels = t.Channels();
   assert(!channels.empty());

   // Collect heights, and count affordances
   int nAffordances = 0;
   int totalHeight = 0;
   std::vector<int> oldHeights;
   for (auto pChannel : channels) {
      auto &view = ChannelView::Get(*pChannel);
      const auto height = view.GetHeight();
      totalHeight += height;
      oldHeights.push_back(height);
      if (view.GetAffordanceControls())
         ++nAffordances;
   }

   // Allocate results
   auto nChannels = static_cast<int>(oldHeights.size());
   std::vector<int> results;
   results.reserve(nChannels);

   // Now reallocate the channel heights for the presence of affordances
   // and separators
   auto availableHeight = totalHeight
      - nAffordances * kAffordancesAreaHeight
      - (nChannels - 1) * kChannelSeparatorThickness
      - kTrackSeparatorThickness;
   int cumulativeOldHeight = 0;
   int cumulativeNewHeight = 0;
   for (const auto &oldHeight : oldHeights) {
      // Preserve the porportions among the stored heights
      cumulativeOldHeight += oldHeight;
      const auto newHeight =
         cumulativeOldHeight * availableHeight / totalHeight
            - cumulativeNewHeight;
      cumulativeNewHeight += newHeight;
      results.push_back(newHeight);
   }

   return results;
}
}

void TrackPanel::UpdateVRulers()
{
   for (auto t : GetTracks()->Any<WaveTrack>())
      UpdateTrackVRuler(*t);

   UpdateVRulerSize();
}

void TrackPanel::UpdateVRuler(Track *t)
{
   if (t)
      UpdateTrackVRuler(*t);

   UpdateVRulerSize();
}

void TrackPanel::UpdateTrackVRuler(Track &t)
{
   auto heights = FindAdjustedChannelHeights(t);

   wxRect rect(mViewInfo->GetVRulerOffset(),
            0,
            mViewInfo->GetVRulerWidth(),
            0);

   auto pHeight = heights.begin();
   for (auto pChannel : t.Channels()) {
      auto &view = ChannelView::Get(*pChannel);
      const auto height = *pHeight++;
      rect.SetHeight(height);
      const auto subViews = view.GetSubViews(rect);
      if (subViews.empty())
         continue;

      auto iter = subViews.begin(), end = subViews.end(), next = iter;
      auto yy = iter->first;
      wxSize vRulerSize{ 0, 0 };
      auto &size = view.vrulerSize;
      for (; iter != end; iter = next) {
         ++next;
         auto nextY = (next == end)
            ? height
            : next->first;
         rect.SetHeight(nextY - yy);
         // This causes ruler size in the track to be reassigned:
         ChannelVRulerControls::Get(*iter->second).UpdateRuler(rect);
         // But we want to know the maximum width and height over all sub-views:
         vRulerSize.IncTo({ size.first, size.second });
         yy = nextY;
      }
      size = { vRulerSize.x, vRulerSize.y };
   }
}

void TrackPanel::UpdateVRulerSize()
{
   auto trackRange = GetTracks()->Any();
   if (trackRange) {
      wxSize s{ 0, 0 };
      // Find maximum width over all channels
      for (auto t : trackRange)
         for (auto pChannel : t->Channels()) {
            const auto &size = ChannelView::Get(*pChannel).vrulerSize;
            s.IncTo({ size.first, size.second });
         }

      if (mViewInfo->GetVRulerWidth() != s.GetWidth()) {
         mViewInfo->SetVRulerWidth(s.GetWidth());
         mRuler->SetLeftOffset(
            mViewInfo->GetLeftOffset());  // bevel on AdornedRuler
         mRuler->Refresh();
      }
   }
   Refresh(false);
}

void TrackPanel::OnTrackMenu(Track *t)
{
   CellularPanel::DoContextMenu(
      t ? ChannelView::Get(*t->GetChannel(0)).shared_from_this() : nullptr);
}

namespace {
   // Drawing constants
   // DisplaceX and MarginX are large enough to avoid overwriting <- symbol
   // See TrackArt::DrawNegativeOffsetTrackArrows
   enum : int {
      // Displacement of the rectangle from upper left corner
      DisplaceX = 7, DisplaceY = 1,
      // Size of margins about the text extent that determine the rectangle size
      MarginX = 8, MarginY = 2,
      // Derived constants
      MarginsX = 2 * MarginX, MarginsY = 2 * MarginY,
   };

Track &GetTrack(Channel &channel)
{
   // It is assumed that all channels we ever see are in groups that are
   // also Tracks
   return static_cast<Track &>(channel.GetChannelGroup());
}

const Track &GetTrack(const Channel &channel)
{
   // It is assumed that all channels we ever see are in groups that are
   // also Tracks
   return static_cast<const Track &>(channel.GetChannelGroup());
}

void GetTrackNameExtent(
   wxDC &dc, const Channel &channel, wxCoord *pW, wxCoord *pH)
{
   wxFont labelFont(12, wxFONTFAMILY_SWISS, wxFONTSTYLE_NORMAL, wxFONTWEIGHT_NORMAL);
   dc.SetFont(labelFont);
   dc.GetTextExtent(GetTrack(channel).GetName(), pW, pH);
}

wxRect GetTrackNameRect(
   int leftOffset,
   const wxRect &trackRect, wxCoord textWidth, wxCoord textHeight )
{
   return {
      leftOffset + DisplaceX,
      trackRect.y + DisplaceY,
      textWidth + MarginsX,
      textHeight + MarginsY
   };
}

/*

  The following classes define the subdivision of the area of the TrackPanel
  into cells with differing responses to mouse, keyboard, and scroll wheel
  events.

  The classes defining the less inclusive areas are earlier, while those
  defining ever larger hierarchical groupings of cells are later.

  To describe that subdivision again, informally, and top-down:

  Firstly subtract margin areas, on the left and right, that do not interact.

  Secondly subtract a noninterative margin above the first track, and an area
  below all tracks that causes deselection of all tracks if you click it.
  (One or both of those areas might be vertically scrolled off-screen, though.)
  Divide what remains into areas corresponding to the several tracks.

  Thirdly, for each track, subtract an area below, which you can click and drag
  to resize the track vertically.

  Fourthly, subtract an area at the left, which contains the track controls,
  such as the menu and delete and minimize buttons, and others appropriate
  to the track subtype.

  Fifthly, divide what remains into the vertically stacked channels, if there
  are more than one, alternating with separators, which can be clicked to
  resize the channel views.

  Sixthly, divide each channel into one or more vertically stacked sub-views.

  Lastly, split the area for each sub-view into a vertical ruler, and an area
  that displays the channel's own contents.

*/

struct EmptyCell final : CommonTrackPanelCell {
   std::vector< UIHandlePtr > HitTest(
      const TrackPanelMouseState &, const AudacityProject *) override
   { return {}; }
   virtual std::shared_ptr< Track > DoFindTrack() override { return {}; }
   static std::shared_ptr<EmptyCell> Instance()
   {
      static auto instance = std::make_shared< EmptyCell >();
      return instance;
   }

   // TrackPanelDrawable implementation
   void Draw(
      TrackPanelDrawingContext &context,
      const wxRect &rect, unsigned iPass ) override
   {
      if ( iPass == TrackArtist::PassMargins ) {
         // Draw a margin area of TrackPanel
         auto dc = &context.dc;

         AColor::TrackPanelBackground( dc, false );
         dc->DrawRectangle( rect );
      }
   }
};

// A vertical ruler left of a channel
struct VRulerAndChannel final : TrackPanelGroup {
   VRulerAndChannel(
      const std::shared_ptr<ChannelView> &pView, wxCoord leftOffset)
         : mpView{ pView }, mLeftOffset{ leftOffset } {}
   Subdivision Children( const wxRect &rect ) override
   {
      return { Axis::X, Refinement{
         { rect.GetLeft(),
           ChannelVRulerControls::Get(*mpView).shared_from_this() },
         { mLeftOffset, mpView }
      } };
   }
   std::shared_ptr<ChannelView> mpView;
   wxCoord mLeftOffset;
};

// One or more sub-views of one channel, stacked vertically, each containing
// a vertical ruler and a channel
struct VRulersAndChannels final : TrackPanelGroup {
   VRulersAndChannels(
      const std::shared_ptr<Channel> &pChannel,
      ChannelView::Refinement refinement, wxCoord leftOffset)
         : mpChannel{ pChannel }
         , mRefinement{ std::move( refinement ) }
         , mLeftOffset{ leftOffset } {}
   Subdivision Children( const wxRect &rect ) override
   {
      Refinement refinement;
      auto y1 = rect.GetTop();
      for ( const auto &subView : mRefinement ) {
         y1 = std::max( y1, subView.first );
         refinement.emplace_back( y1,
            std::make_shared< VRulerAndChannel >(
               subView.second, mLeftOffset ) );
      }
      return { Axis::Y, std::move( refinement ) };
   }

   // TrackPanelDrawable implementation
   void Draw(
      TrackPanelDrawingContext &context,
      const wxRect &rect, unsigned iPass ) override
   {
      // This overpaints the track area, but sometimes too the stereo channel
      // separator, so draw at least later than that

      if ( iPass == TrackArtist::PassBorders ) {
         if (mRefinement.size() > 1) {
            // Draw lines separating sub-views
            auto &dc = context.dc;
            AColor::CursorColor( &dc );
            auto iter = mRefinement.begin() + 1, end = mRefinement.end();
            for ( ; iter != end; ++iter ) {
               auto yy = iter->first;
               AColor::Line(dc, rect.x, yy, mLeftOffset - 1, yy);
               AColor::Line( dc, mLeftOffset, yy, rect.GetRight(), yy );
            }
         }
      }
   }

   std::shared_ptr<Channel> mpChannel;
   ChannelView::Refinement mRefinement;
   wxCoord mLeftOffset;
};

//Simply place children one after another horizontally, without any specific logic
struct HorizontalGroup final : TrackPanelGroup {

   Refinement mRefinement;

   HorizontalGroup(Refinement refinement)
      : mRefinement(std::move(refinement))
   {
   }

   Subdivision Children(const wxRect& /*rect*/) override
   {
      return { Axis::X, mRefinement };
   }

};


// optional affordance area, and n channels with vertical rulers,
// alternating with n - 1 resizers;
// each channel-ruler pair might be divided into multiple views
struct ChannelStack final : TrackPanelGroup {
   ChannelStack(const std::shared_ptr<Track> &pTrack, wxCoord leftOffset)
      : mpTrack{ pTrack }, mLeftOffset{ leftOffset } {}
   Subdivision Children(const wxRect &rect_) override
   {
      auto rect = rect_;
      Refinement refinement;

      const auto channels = mpTrack->Channels();
      const auto pLast = *channels.rbegin();
      wxCoord yy = rect.GetTop();
      auto heights = FindAdjustedChannelHeights(*mpTrack);
      auto pHeight = heights.begin();
      for (auto pChannel : channels) {
         auto &view = ChannelView::Get(*pChannel);
         if (auto affordance = view.GetAffordanceControls()) {
            Refinement hgroup {
               std::make_pair(mLeftOffset, affordance)
            };
            refinement
               .emplace_back(yy, std::make_shared<HorizontalGroup>(hgroup));
            yy += kAffordancesAreaHeight;
         }

         auto height = *pHeight++;
         rect.SetTop(yy);
         rect.SetHeight(height - kChannelSeparatorThickness);
         refinement.emplace_back(yy,
            std::make_shared<VRulersAndChannels>(pChannel,
               ChannelView::Get(*pChannel).GetSubViews(rect),
               mLeftOffset));
         if (pChannel != pLast) {
            yy += height;
            refinement.emplace_back(
               yy - kChannelSeparatorThickness,
               TrackPanelResizerCell::Get(*pChannel)
                  .shared_from_this());
         }
      }

      return { Axis::Y, std::move(refinement) };
   }

   void Draw(TrackPanelDrawingContext& context,
      const wxRect& rect, unsigned iPass) override
   {
      TrackPanelGroup::Draw(context, rect, iPass);
      if (iPass == TrackArtist::PassTracks)
      {
         auto vRulerRect = rect;
         vRulerRect.width = mLeftOffset - rect.x;

         auto dc = &context.dc;

         // Paint the background;
         AColor::MediumTrackInfo(dc, mpTrack->GetSelected() );
         dc->DrawRectangle( vRulerRect );

         const auto channels = mpTrack->Channels();
         auto& view = ChannelView::Get(**channels.begin());
         if(auto affordance = view.GetAffordanceControls())
         {
            const auto yy = vRulerRect.y + kAffordancesAreaHeight - 1;
            AColor::Dark( dc, false );
            AColor::Line( *dc, vRulerRect.GetLeft(), yy, vRulerRect.GetRight(), yy );
         }

         // Stroke left and right borders
         dc->SetPen(*wxBLACK_PEN);
         
         AColor::Line( *dc, vRulerRect.GetLeftTop(), vRulerRect.GetLeftBottom() );
         AColor::Line( *dc, vRulerRect.GetRightTop(), vRulerRect.GetRightBottom() );
      }
      if (iPass == TrackArtist::PassFocus && mpTrack->IsSelected()) {
         const auto channels = mpTrack->Channels();
         const auto pLast = *channels.rbegin();
         wxCoord yy = rect.GetTop();
         auto heights = FindAdjustedChannelHeights(*mpTrack);
         auto pHeight = heights.begin();
         for (auto pChannel : channels) {
            auto& view = ChannelView::Get(*pChannel);
            auto height = *pHeight++;
            if (auto affordance = view.GetAffordanceControls())
               height += kAffordancesAreaHeight;
            auto trackRect = wxRect(
               mLeftOffset,
               yy,
               rect.GetRight() - mLeftOffset,
               height - kChannelSeparatorThickness);
            TrackArt::DrawCursor(context, trackRect, mpTrack.get());
            yy += height;
         }
      }
   }

   const std::shared_ptr<Track> mpTrack;
   wxCoord mLeftOffset;
};

// A track control panel, left of n vertical rulers and n channels
// alternating with n - 1 resizers
struct LabeledChannelGroup final : TrackPanelGroup {
   LabeledChannelGroup(
      const std::shared_ptr<Track> &pTrack, wxCoord leftOffset)
         : mpTrack{ pTrack }, mLeftOffset{ leftOffset } {}
   Subdivision Children(const wxRect &rect) override
   { return { Axis::X, Refinement{
      { rect.GetLeft(),
         TrackControls::Get(*mpTrack).shared_from_this() },
      { rect.GetLeft() + kTrackInfoWidth,
        std::make_shared<ChannelStack>(mpTrack, mLeftOffset) }
   } }; }

   // TrackPanelDrawable implementation
   void Draw(TrackPanelDrawingContext &context,
      const wxRect &rect, unsigned iPass) override
   {
      if (iPass == TrackArtist::PassBorders) {
         auto &dc = context.dc;
         dc.SetBrush(*wxTRANSPARENT_BRUSH);
         dc.SetPen(*wxBLACK_PEN);

         // border
         dc.DrawRectangle(
            rect.x, rect.y,
            rect.width - kShadowThickness, rect.height - kShadowThickness
         );

         // shadow
         if constexpr (kShadowThickness > 0)
         {
            // Stroke lines along bottom and right, which are slightly short at
            // bottom-left and top-right
            const auto right = rect.GetRight();
            const auto bottom = rect.GetBottom();

            // bottom
            AColor::Line(dc, rect.x + 2, bottom, right, bottom);
            // right
            AColor::Line(dc, right, rect.y + 2, right, bottom);
         }
      }
      if (iPass == TrackArtist::PassFocus) {
         // Sometimes highlight is not drawn on backing bitmap. I thought
         // it was because FindFocus did not return the TrackPanel on Mac, but
         // when I removed that test, yielding this condition:
         //     if (GetFocusedTrack() != NULL) {
         // the highlight was reportedly drawn even when something else
         // was the focus and no highlight should be drawn. -RBD
         const auto artist = TrackArtist::Get(context);
         auto &trackPanel = *artist->parent;
         auto &trackFocus = TrackFocus::Get( *trackPanel.GetProject() );
         if (trackFocus.Get() == mpTrack.get() &&
             wxWindow::FindFocus() == &trackPanel) {
            /// Draw a three-level highlight gradient around the focused track.
            wxRect theRect = rect;
            auto &dc = context.dc;
            dc.SetBrush(*wxTRANSPARENT_BRUSH);

            AColor::TrackFocusPen(&dc, 2);
            dc.DrawRectangle(theRect);
            theRect.Deflate(1);

            AColor::TrackFocusPen(&dc, 1);
            dc.DrawRectangle(theRect);
            theRect.Deflate(1);

            AColor::TrackFocusPen(&dc, 0);
            dc.DrawRectangle(theRect);
         }
      }
   }

   wxRect DrawingArea(TrackPanelDrawingContext &,
      const wxRect &rect, const wxRect &, unsigned iPass) override
   {
      if (iPass == TrackArtist::PassBorders)
         return {
            rect.x - kBorderThickness,
            rect.y - kBorderThickness,
            rect.width + 2 * kBorderThickness + kShadowThickness,
            rect.height + 2 * kBorderThickness + kShadowThickness
         };
      else if (iPass == TrackArtist::PassFocus) {
         constexpr auto extra = kBorderThickness + 3;
         return {
            rect.x - extra,
            rect.y - extra,
            rect.width + 2 * extra + kShadowThickness,
            rect.height + 2 * extra + kShadowThickness
         };
      }
      else
         return rect;
   }

   const std::shared_ptr<Track> mpTrack;
   wxCoord mLeftOffset;
};

// Stacks a label and a single or multi-channel track on a resizer below,
// which is associated with the last channel
struct ResizingChannelGroup final : TrackPanelGroup {
   ResizingChannelGroup(
      const std::shared_ptr<Track> &pTrack, wxCoord leftOffset)
         : mpTrack{ pTrack }, mLeftOffset{ leftOffset } {}
   Subdivision Children(const wxRect &rect) override
   { return { Axis::Y, Refinement{
      { rect.GetTop(),
         std::make_shared<LabeledChannelGroup>(mpTrack, mLeftOffset) },
      { rect.GetTop() + rect.GetHeight() - kTrackSeparatorThickness,
         TrackPanelResizerCell::Get(
            **mpTrack->Channels().rbegin()).shared_from_this()
      }
   } }; }
   const std::shared_ptr<Track> mpTrack;
   wxCoord mLeftOffset;
};

// Stacks a dead area at top, the tracks, and the click-to-deselect area below
struct Subgroup final : TrackPanelGroup {
   explicit Subgroup(TrackPanel &panel) : mPanel{ panel } {}
   Subdivision Children(const wxRect &rect) override
   {
      const auto &viewInfo = *mPanel.GetViewInfo();
      wxCoord yy = -viewInfo.vpos;
      Refinement refinement;

      auto &tracks = *mPanel.GetTracks();
      if (!tracks.empty())
         refinement.emplace_back( yy, EmptyCell::Instance() ),
         yy += kTopMargin;

      const auto showContentTrack = ShowContentTrack.Read();
      const auto contentHeight =
         std::clamp(ContentTrackHeightSetting.Read(), 24, 240);
      int trackCount = 0;
      for (const auto pTrack : tracks) {
         (void)pTrack;
         ++trackCount;
      }
      const auto contentIndex =
         std::clamp(ContentTrackIndexSetting.Read(), 0, trackCount);

      auto addContentTrack = [&] {
         if (showContentTrack) {
            refinement.emplace_back(yy, ContentTrackCell::Instance());
            yy += contentHeight;
         }
      };

      if (contentIndex == 0)
         addContentTrack();

      int trackIndex = 0;
      for (const auto pTrack : tracks) {
         wxCoord height = 0;
         for (auto pChannel : pTrack->Channels()) {
            auto &view = ChannelView::Get(*pChannel);
            height += view.GetHeight();
         }
         refinement.emplace_back( yy,
            std::make_shared<ResizingChannelGroup>(
               pTrack->SharedPointer(), viewInfo.GetLeftOffset())
         );
         yy += height;
         ++trackIndex;
         if (contentIndex == trackIndex)
            addContentTrack();
      }

      refinement.emplace_back(std::max(0, yy), mPanel.GetBackgroundCell());

      return { Axis::Y, std::move(refinement) };
   }
   TrackPanel &mPanel;
};

// Main group shaves off the left and right margins
struct MainGroup final : TrackPanelGroup {
   explicit MainGroup(TrackPanel &panel) : mPanel{ panel } {}
   Subdivision Children(const wxRect &rect) override
   { return { Axis::X, Refinement{
      { 0, EmptyCell::Instance() },
      { kLeftMargin, std::make_shared<Subgroup>(mPanel) },
      { rect.GetRight() + 1 - kRightMargin, EmptyCell::Instance() }
   } }; }
   TrackPanel &mPanel;
};

}

std::shared_ptr<TrackPanelNode> TrackPanel::Root()
{
   // Root and other subgroup objects are throwaways.
   // They might instead be cached to avoid repeated allocation.
   // That cache would need invalidation when there is addition, deletion, or
   // permutation of tracks, or change of width of the vertical rulers.
   return std::make_shared< MainGroup >( *this );
}

// This finds the rectangle of a given track (including all channels),
// either that of the label 'adornment' or the track itself
// The given track is assumed to be the first channel
wxRect TrackPanel::FindTrackRect( const Track * target )
{
   return CellularPanel::FindRect( [&] ( TrackPanelNode &node ) {
      if (auto pGroup = dynamic_cast<const LabeledChannelGroup*>( &node ))
         return pGroup->mpTrack.get() == target;
      return false;
   } );
}

wxRect TrackPanel::FindFocusedTrackRect( const Track * target )
{
   auto rect = FindTrackRect(target);
   if (rect != wxRect{}) {
      // Enlarge horizontally.
      // PRL:  perhaps it's one pixel too much each side, including some gray
      // beyond the yellow?
      rect.x = 0;
      GetClientSize(&rect.width, nullptr);

      // Enlarge vertically, enough to enclose the yellow focus border pixels
      // The the outermost ring of gray pixels is included on three sides
      // but not the top (should that be fixed?)

      // (Note that TrackPanel paints its focus over the "top margin" of the
      // rectangle allotted to the track, according to ChannelView::GetY() and
      // ChannelView::GetHeight(), but also over the margin of the next track.)

      rect.height += kBottomMargin;
      int dy = kTopMargin - 1;
      rect.Inflate( 0, dy );

      // Note that this rectangle does not coincide with any one of
      // the nodes in the subdivision.
   }
   return rect;
}

std::vector<wxRect> TrackPanel::FindRulerRects(const Channel &target)
{
   std::vector<wxRect> results;
   VisitCells( [&](const wxRect &rect, TrackPanelCell &visited) {
      if (auto pRuler = dynamic_cast<const ChannelVRulerControls*>(&visited))
         if (auto pView = pRuler->GetChannelView())
            if (pView->FindChannel().get() == &target)
               results.push_back(rect);
   } );
   return results;
}

std::shared_ptr<TrackPanelCell> TrackPanel::GetFocusedCell()
{
   auto pTrack = TrackFocus::Get(*GetProject()).Get();
   return pTrack
      ? ChannelView::Get(*pTrack->GetChannel(0)).shared_from_this()
      : GetBackgroundCell();
}

void TrackPanel::SetFocusedCell()
{
   // This may have a side-effect of assigning a focus if there was none
   auto& trackFocus = TrackFocus::Get(*GetProject());
   trackFocus.Set(trackFocus.Get());
   KeyboardCapture::Capture(this);
}

void TrackPanel::OnTrackFocusChange(TrackFocusChangeMessage message)
{
   if (message.focusPanel)
      SetFocus();
   if (auto cell = GetFocusedCell())
      Refresh(false);
}
