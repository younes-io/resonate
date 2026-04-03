#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$ROOT"

FILES=(
  proofs/dafny/model/Collections.dfy
  proofs/dafny/model/ResonateModel.dfy
  proofs/dafny/model/CoordinationModel.dfy
  proofs/dafny/model/StorageSpec.dfy
  proofs/dafny/executable/SchedulePlannerKernel.dfy
  proofs/dafny/executable/TimeoutBatchKernel.dfy
  proofs/dafny/proofs/PromiseStateMachine.dfy
  proofs/dafny/proofs/TimeoutProofs.dfy
  proofs/dafny/proofs/CoordinationProofs.dfy
)

DAFNY_ARGS=(
  --verification-time-limit
  60
)

if command -v dafny >/dev/null 2>&1; then
  exec dafny verify "${DAFNY_ARGS[@]}" "${FILES[@]}"
fi

if [ -f .config/dotnet-tools.json ]; then
  if dotnet tool list --local 2>/dev/null | awk 'NR > 2 {print $1}' | grep -qx 'dafny'; then
    exec dotnet tool run dafny verify "${DAFNY_ARGS[@]}" "${FILES[@]}"
  fi
fi

echo "Dafny is not installed." >&2
echo "Install it with one of:" >&2
echo "  brew install dafny" >&2
echo "  dotnet tool install --local dafny --version 4.11.0" >&2
exit 1
