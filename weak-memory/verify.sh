#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean_bin="$project_dir/../.tools/lean-4.32.2-linux/bin"

if [[ ! -x "$lean_bin/lake" ]]; then
  echo "Local Lean installation not found: $lean_bin/lake" >&2
  exit 1
fi

echo "Trusted C source descriptor"
case "${WEAK_MEMORY_SOURCE_CHECK_PREVERIFIED:-0}" in
  0)
    python3 "$project_dir/tools/extract_treiber_source_trust_boundary.py" --check
    ;;
  1)
    echo "Preverified by the remote orchestrator with the pinned local Clang"
    ;;
  *)
    echo "WEAK_MEMORY_SOURCE_CHECK_PREVERIFIED must be 0 or 1" >&2
    exit 2
    ;;
esac

echo "C11 Treiber tests"
make -C "$project_dir/c" test

echo "Lean proofs"
export PATH="$lean_bin:$PATH"
cd "$project_dir"
lake build
lake build WeakMemory.TreiberVerifiedModelExample
lake build WeakMemory.TreiberVerifiedModelClientOrderExamples
lake build WeakMemory.TreiberC11V1Frontend
lake build WeakMemory.TreiberC11V1Examples
lake build WeakMemory.WeakCASSiteResult
lake build WeakMemory.MSQueueSpec
lake build WeakMemory.MSQueueHistory
lake build WeakMemory.MSQueueSourceHistory
lake build WeakMemory.MSQueueSourceScheduleEquivalence
lake build WeakMemory.MSQueueSourceRealTime
lake build WeakMemory.MSQueueInfinite
lake build WeakMemory.MSQueueInfiniteSafety
lake build WeakMemory.MSQueueSourceSameThreadRealTime
lake build WeakMemory.MSQueueSourceMethodTrace
lake build WeakMemory.MSQueueSourceHistoryWellFormed
lake build WeakMemory.MultiLocationRC11Examples
lake build WeakMemory.MultiLocationRC11ReleaseSequenceExamples
lake build WeakMemory.MultiLocationRC11ScheduleCounterexample
lake build WeakMemory.MSQueueSourceExamples
lake build WeakMemory.MSQueueSourceWellFormedExamples
lake build WeakMemory.MSQueueSourceRC11Examples
lake build WeakMemory.MSQueueChainExamples
lake build WeakMemory.MSQueueSourceChain
lake build WeakMemory.MSQueueRecordScheduling
lake build WeakMemory.MSQueueRecordPrefix
lake build WeakMemory.MSQueueSourceSchedule
lake build WeakMemory.MSQueueSourceVisibility
lake build WeakMemory.MSQueueStructuralRMW
lake build WeakMemory.MSQueueSourceWriteClassification
lake build WeakMemory.MSQueueSourceWriteOrigins
lake build WeakMemory.MSQueueSourcePredecessors
lake build WeakMemory.MSQueueSourceControlProvenance
lake build WeakMemory.MSQueueSourceReservation
lake build WeakMemory.MSQueueSourceDependencies
lake build WeakMemory.MSQueueSourceHeadProvenance
lake build WeakMemory.MSQueueSourceHeadDependencies
lake build WeakMemory.MSQueueSourceRecordDependencies
lake build WeakMemory.MSQueueSourcePayload
lake build WeakMemory.MSQueueSourceObservations
lake build WeakMemory.MSQueueSourceLinkGraph
lake build WeakMemory.MSQueueSourcePrefix
lake build WeakMemory.MSQueueSourcePrefixReadiness
lake build WeakMemory.MSQueueSourceHeadPrefixReadiness
lake build WeakMemory.MSQueueSourceHeadTailGap
lake build WeakMemory.MSQueueSourceTailPrefixReadiness
lake build WeakMemory.MSQueueSourceEmptyPrefixReadiness
lake build WeakMemory.MSQueueSourceReplay
lake build WeakMemory.MSQueueSourceUniversalReplay
lake build WeakMemory.MSQueueSourceCompletion
lake build WeakMemory.MSQueueSourceHistoryBridge
lake build WeakMemory.MSQueueSourceChainExamples
lake build WeakMemory.WeakCASTreiberResult
lake exe weakMemoryDemo

echo "GenMC bounded RC11 checks"
"$project_dir/run_genmc.sh"
