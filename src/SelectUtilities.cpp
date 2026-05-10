/**********************************************************************
 
 Audacity: A Digital Audio Editor
 
 SelectUtilities.cpp
 
 Paul Licameli split from SelectMenus.cpp
 
 **********************************************************************/

#include "SelectUtilities.h"

#include <algorithm>
#include <cmath>
#include <vector>

#include <wx/frame.h>

#include "AudacityMessageBox.h"
#include "AudioIO.h"
#include "BasicUI.h"
#include "CommonCommandFlags.h"
#include "Project.h"
#include "ProjectAudioIO.h"
#include "ProjectHistory.h"
#include "ProjectNumericFormats.h"
#include "ProjectWindows.h"
#include "ProjectRate.h"
#include "SelectionState.h"
#include "SyncLock.h"
#include "TimeDialog.h"
#include "TrackFocus.h"
#include "TrackPanel.h"
#include "ViewInfo.h"
#include "WaveClip.h"
#include "WaveTrack.h"

#include "CommandManager.h"

namespace {

constexpr auto GetZeroCrossingWindowSize(double projectRate)
{
   return size_t(std::max(1.0, projectRate / 100));
}

std::vector<const WaveTrack*> GetZeroCrossingTracks(
   AudacityProject &project, bool includeSyncLockedTracks)
{
   std::vector<const WaveTrack*> result;
   // The manual Zero Crossings command passes false here, preserving the
   // traditional selected-tracks-only behavior.  The automatic adjustment may
   // pass true so sync-lock-selected tracks contribute to the shared crossing.
   for (auto track : TrackList::Get(project).Any<const WaveTrack>()) {
      if (track->GetSelected() ||
          (includeSyncLockedTracks && SyncLock::IsSyncLockSelected(*track)))
         result.push_back(track);
   }
   return result;
}

double NearestZeroCrossing(
   AudacityProject &project, double t0,
   const std::vector<const WaveTrack*> &tracks)
{
   auto rate = ProjectRate::Get(project).GetRate();

   // Window is 1/100th of a second.
   auto windowSize = GetZeroCrossingWindowSize(rate);
   Floats dist{ windowSize, true };

   int nTracks = 0;
   for (auto one : tracks) {
      const auto nChannels = one->NChannels();
      auto oneWindowSize = size_t(std::max(1.0, one->GetRate() / 100));
      Floats buffer1{ oneWindowSize };
      Floats buffer2{ oneWindowSize };
      float *const buffers[]{ buffer1.get(), buffer2.get() };
      auto s = one->TimeToLongSamples(t0);

      // fillTwo to ensure that missing values are treated as 2, and hence do
      // not get used as zero crossings.
      one->GetFloats(0, nChannels, buffers,
         s - (int)oneWindowSize/2, oneWindowSize, false, FillFormat::fillTwo);

      // Looking for actual crossings.  Update dist
      for (size_t iChannel = 0; iChannel < nChannels; ++iChannel) {
         const auto oneDist = buffers[iChannel];
         double prev = 2.0;
         for (size_t i = 0; i < oneWindowSize; ++i) {
            float fDist = std::fabs(oneDist[i]); // score is absolute value
            if (prev * oneDist[i] > 0) // both same sign?  No good.
               fDist = fDist + 0.4; // No good if same sign.
            else if (prev > 0.0)
               fDist = fDist + 0.1; // medium penalty for downward crossing.
            prev = oneDist[i];
            oneDist[i] = fDist;
         }

         // TODO: The mixed rate zero crossing code is broken,
         // if oneWindowSize > windowSize we'll miss out some
         // samples - so they will still be zero, so we'll use them.
         for (size_t i = 0; i < windowSize; i++) {
            size_t j;
            if (windowSize != oneWindowSize)
               j = i * (oneWindowSize - 1) / (windowSize - 1);
            else
               j = i;

            dist[i] += oneDist[j];
            // Apply a small penalty for distance from the original endpoint
            // We'll always prefer an upward
            dist[i] +=
               0.1 * (std::abs(int(i) - int(windowSize / 2))) / float(windowSize / 2);
         }
      }
      nTracks++;
   }

   // Find minimum
   int argmin = 0;
   float min = 3.0;
   for (size_t i = 0; i < windowSize; ++i) {
      if (dist[i] < min) {
         argmin = i;
         min = dist[i];
      }
   }

   // If we're worse than 0.2 on average, on one track, then no good.
   if ((nTracks == 1) && (min > (0.2 * nTracks)))
      return t0;
   // If we're worse than 0.6 on average, on multi-track, then no good.
   if ((nTracks > 1) && (min > (0.6 * nTracks)))
      return t0;

   return t0 + (argmin - (int)windowSize / 2) / rate;
}

bool CanSearchZeroCrossings(
   AudacityProject &project, const std::vector<const WaveTrack*> &tracks,
   bool showError)
{
   auto &selectedRegion = ViewInfo::Get(project).selectedRegion;

   // Selecting precise sample indices across tracks that may have clips with
   // various stretch ratios in itself is not possible. Even in single-track
   // mode, we cannot know what the final waveform will look like until
   // stretching is applied, making this operation futile. Hence we disallow
   // it if any stretched clip is involved.
   const auto projectRate = ProjectRate(project).GetRate();
   const auto searchWindowDuration =
      GetZeroCrossingWindowSize(projectRate) / projectRate;
   const auto wouldSearchClipWithPitchOrSpeed =
      [searchWindowDuration](const WaveTrack& track, double t)
   {
      const auto clips = track.GetSortedClipsIntersecting(
         t - searchWindowDuration / 2, t + searchWindowDuration / 2);
      return std::any_of(
         clips.begin(), clips.end(),
         [](const auto& clip) { return clip->HasPitchOrSpeed(); });
   };

   if (std::any_of(
          tracks.begin(), tracks.end(), [&](const WaveTrack* track) {
             return wouldSearchClipWithPitchOrSpeed(
                       *track, selectedRegion.t0()) ||
                    wouldSearchClipWithPitchOrSpeed(
                       *track, selectedRegion.t1());
          }))
   {
      if (showError) {
         using namespace BasicUI;
         ShowMessageBox(
            XO("Zero-crossing search regions intersect stretched clip(s)."),
            MessageBoxOptions {}.Caption(XO("Error")).IconStyle(Icon::Error));
      }
      return false;
   }

   return true;
}

// Temporal selection (not TimeTrack selection)
// potentially for all wave tracks.
void DoSelectTimeAndAudioTracks(
   AudacityProject &project, bool bAllTime, bool bAllTracks)
{
   auto &tracks = TrackList::Get(project);
   auto &selectedRegion = ViewInfo::Get(project).selectedRegion;

   if (bAllTime)
      selectedRegion.setTimes(tracks.GetStartTime(), tracks.GetEndTime());

   if (bAllTracks) {
      // Unselect all tracks before selecting audio.
      for (auto t : tracks)
         t->SetSelected(false);
      for (auto t : tracks.Any<WaveTrack>())
         t->SetSelected(true);
      ProjectHistory::Get( project ).ModifyState(false);
   }
}

}
namespace SelectUtilities {

BoolSetting AdjustSelectionToZeroCrossOnSelection{
   "/GUI/AdjustSelectionToZeroCrossOnSelection", true };

// Secondary tweak for the automatic mode only: when true, sync-lock state is
// ignored and the zero-cross search is constrained to explicitly selected tracks.
BoolSetting AutoZeroCrossSelectionOnSelectedOnly{
   "/GUI/AutoZeroCrossSelectionOnSelectedOnly", false };

void DoSelectTimeAndTracks
(AudacityProject &project, bool bAllTime, bool bAllTracks)
{
   auto &tracks = TrackList::Get( project );
   auto &selectedRegion = ViewInfo::Get( project ).selectedRegion;

   if( bAllTime )
      selectedRegion.setTimes(tracks.GetStartTime(), tracks.GetEndTime());

   if( bAllTracks ) {
      for (auto t : tracks)
         t->SetSelected(true);

      ProjectHistory::Get( project ).ModifyState(false);
   }
}

void SelectNone( AudacityProject &project )
{
   auto &tracks = TrackList::Get( project );
   for (auto t : tracks)
      t->SetSelected(false);

   auto &trackPanel = TrackPanel::Get( project );
   trackPanel.Refresh(false);
}

// Select the full time range, if no
// time range is selected.
void SelectAllIfNone( AudacityProject &project )
{
   auto &viewInfo = ViewInfo::Get( project );
   auto flags = CommandManager::Get( project ).GetUpdateFlags();
   if((flags & EditableTracksSelectedFlag()).none() ||
      viewInfo.selectedRegion.isPoint())
      DoSelectAllAudio( project );
}

// Select the full time range, if no time range is selected and
// selecting is allowed. Returns "false" selecting not allowed.
bool SelectAllIfNoneAndAllowed( AudacityProject &project )
{
   auto allowed = gPrefs->ReadBool(wxT("/GUI/SelectAllOnNone"), false);
   auto &viewInfo = ViewInfo::Get( project );
   auto flags = CommandManager::Get( project ).GetUpdateFlags();

   if((flags & EditableTracksSelectedFlag()).none() ||
      viewInfo.selectedRegion.isPoint()) {
      if (!allowed) {
         return false;
      }
      DoSelectAllAudio( project );
   }
   return true;
}

void DoListSelection(
   AudacityProject &project, Track &t, bool shift, bool ctrl, bool modifyState)
{
   auto &tracks = TrackList::Get(project);
   auto &selectionState = SelectionState::Get(project);
   auto &viewInfo = ViewInfo::Get(project);
   auto &window = GetProjectFrame(project);

   auto isSyncLocked = SyncLockState::Get(project).IsSyncLocked();

   selectionState.HandleListSelection(
      tracks, viewInfo, t,
      shift, ctrl, isSyncLocked);

   if (!ctrl)
      TrackFocus::Get(project).Set(&t);
   window.Refresh(false);
   if (modifyState)
      ProjectHistory::Get(project).ModifyState(true);
}

void DoSelectAll(AudacityProject &project)
{
   DoSelectTimeAndTracks( project, true, true );
}

void DoSelectAllAudio(AudacityProject &project)
{
   DoSelectTimeAndAudioTracks( project, true, true );
}

// This function selects all tracks if no tracks selected,
// and all time if no time selected.
// There is an argument for making it just count wave tracks,
// However you could then not select a label and cut it,
// without this function selecting all tracks.
void DoSelectSomething(AudacityProject &project)
{
   auto &tracks = TrackList::Get( project );
   auto &selectedRegion = ViewInfo::Get( project ).selectedRegion;

   bool bTime = selectedRegion.isPoint();
   bool bTracks = tracks.Selected().empty();

   if (bTime || bTracks)
      DoSelectTimeAndTracks(project, bTime, bTracks);
}

bool AdjustSelectionToZeroCrossing(
   AudacityProject &project, bool includeSyncLockedTracks, bool showError)
{
   auto &selectedRegion = ViewInfo::Get(project).selectedRegion;
   // This is the common implementation used by both the menu command and the
   // auto-adjust hook; the includeSyncLockedTracks argument is the only policy
   // difference between those callers.
   const auto tracks =
      GetZeroCrossingTracks(project, includeSyncLockedTracks);

   if (tracks.empty() || !CanSearchZeroCrossings(project, tracks, showError))
      return false;

   const auto oldT0 = selectedRegion.t0();
   const auto oldT1 = selectedRegion.t1();
   const double t0 = NearestZeroCrossing(project, oldT0, tracks);
   bool adjusted = false;

   if (selectedRegion.isPoint()) {
      selectedRegion.setTimes(t0, t0);
      adjusted = (t0 != oldT0);
   }
   else {
      const double t1 = NearestZeroCrossing(project, oldT1, tracks);
      // Empty selection is generally not much use, so do not make it if empty.
      if (std::fabs(t1 - t0) * ProjectRate::Get(project).GetRate() > 1.5) {
         selectedRegion.setTimes(t0, t1);
         adjusted = (t0 != oldT0) || (t1 != oldT1);
      }
   }

   return adjusted;
}

bool MaybeAdjustSelectionToZeroCrossing(
   AudacityProject &project, bool showError)
{
   if (!AdjustSelectionToZeroCrossOnSelection.Read())
      return false;

   // Auto-adjust normally honors sync-lock.  The selected-only preference makes
   // automatic adjustment behave like the manual Zero Crossings command.
   const bool includeSyncLockedTracks =
      SyncLockState::Get(project).IsSyncLocked() &&
      !AutoZeroCrossSelectionOnSelectedOnly.Read();

   return AdjustSelectionToZeroCrossing(
      project, includeSyncLockedTracks, showError);
}

void ActivatePlayRegion(AudacityProject &project)
{
   auto &viewInfo = ViewInfo::Get( project );
   auto &playRegion = viewInfo.playRegion;
   playRegion.SetActive( true );
   if (playRegion.Empty()) {
      auto &selectedRegion = viewInfo.selectedRegion;
      if (!selectedRegion.isPoint())
         playRegion.SetTimes(selectedRegion.t0(), selectedRegion.t1());
      else
         // Arbitrary first four seconds
         playRegion.SetTimes(0.0, 4.0);
   }

   // Ensure the proper state of looping in the menu
   CommandManager::Get(project).UpdateCheckmarks();
}

void InactivatePlayRegion(AudacityProject &project)
{
   auto &viewInfo = ViewInfo::Get( project );
   auto &playRegion = viewInfo.playRegion;
   auto &selectedRegion = viewInfo.selectedRegion;
   // Set only the times that are fetched by the playback engine, but not
   // the last-active times that are used for display.
   playRegion.SetActive( false );
   playRegion.SetTimes( selectedRegion.t0(), selectedRegion.t1() );

   // Ensure the proper state of looping in the menu
   CommandManager::Get(project).UpdateCheckmarks();
}

void TogglePlayRegion(AudacityProject &project)
{
   auto &viewInfo = ViewInfo::Get( project );
   auto &playRegion = viewInfo.playRegion;
   if (playRegion.Active())
      InactivatePlayRegion(project);
   else
      ActivatePlayRegion(project);
}

void ClearPlayRegion(AudacityProject &project)
{
   auto &viewInfo = ViewInfo::Get( project );
   auto &playRegion = viewInfo.playRegion;
   playRegion.Clear();

   if (playRegion.Active())
      InactivatePlayRegion(project);
}

void SetPlayRegionToSelection(AudacityProject &project)
{
   auto &viewInfo = ViewInfo::Get( project );
   auto &playRegion = viewInfo.playRegion;
   auto &selectedRegion = viewInfo.selectedRegion;
   playRegion.SetAllTimes( selectedRegion.t0(), selectedRegion.t1() );
   if(!playRegion.Empty())
      ActivatePlayRegion(project);
}

void OnSetRegion(AudacityProject &project,
   bool left, bool selection, const TranslatableString &dialogTitle)
{
   auto token = ProjectAudioIO::Get( project ).GetAudioIOToken();
   auto &viewInfo = ViewInfo::Get( project );
   auto &playRegion = viewInfo.playRegion;
   auto &selectedRegion = viewInfo.selectedRegion;
   const auto &formats = ProjectNumericFormats::Get( project );
   auto &window = GetProjectFrame( project );

   const auto getValue = [&]() -> double {
      if (selection) {
         if (left)
            return selectedRegion.t0();
         else
            return selectedRegion.t1();
      }
      else {
         if (left)
            return playRegion.GetStart();
         else
            return playRegion.GetEnd();
      }
   };

   const auto setValue = [&](double value){
      if (selection) {
         if (left)
            selectedRegion.setT0(value, false);
         else
            selectedRegion.setT1(value, false);
      }
      else {
         if (left)
            playRegion.SetStart(value);
         else
            playRegion.SetEnd(value);
      }
   };

   bool bSelChanged = false;
   auto gAudioIO = AudioIO::Get();
   if ((token > 0) && gAudioIO->IsStreamActive(token))
   {
      double indicator = gAudioIO->GetStreamTime();
      setValue(indicator);
      bSelChanged = true;
   }
   else
   {
      auto fmt = formats.GetSelectionFormat();

      TimeDialog dlg(&window, dialogTitle,
         fmt, project, getValue(), XO("Position"));

      if (wxID_OK == dlg.ShowModal())
      {
         //Get the value from the dialog
         setValue( std::max(0.0, dlg.GetTimeValue()) );
         bSelChanged = true;
      }
   }

   if (bSelChanged)
      ProjectHistory::Get( project ).ModifyState(false);
}
}
