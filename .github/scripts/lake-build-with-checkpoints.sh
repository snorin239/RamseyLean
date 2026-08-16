#!/usr/bin/env bash

set -euo pipefail

log_file="${RUNNER_TEMP:-.}/lake-build-${GITHUB_JOB:-local}.log"
: > "$log_file"

last_marker() {
  LC_ALL=C sed -nE \
    's/.*(\[[0-9]+\/[0-9]+\] (Built|Replayed) [^[:cntrl:]]*).*/\1/p' \
    "$log_file" | tail -n 1
}

checkpoint_loop() {
  local minutes=0
  local marker
  while sleep 60; do
    minutes=$((minutes + 1))
    if ((minutes % 15 == 0)); then
      marker="$(last_marker || true)"
      if [[ -z "$marker" ]]; then
        marker="no completed Lake job reported yet"
      fi
      echo "::notice title=Lake checkpoint::After $minutes minutes: $marker"
    fi
  done
}

checkpoint_loop &
checkpoint_pid=$!

set +e
lake build "$@" 2>&1 | tee "$log_file"
lake_status=${PIPESTATUS[0]}
set -e

kill "$checkpoint_pid" 2>/dev/null || true
wait "$checkpoint_pid" 2>/dev/null || true

marker="$(last_marker || true)"
if [[ -z "$marker" ]]; then
  marker="no completed Lake job reported"
fi
echo "::notice title=Final Lake marker::$marker"

if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  printf '### Lake build marker\n\n`%s`\n' "$marker" >> "$GITHUB_STEP_SUMMARY"
fi

exit "$lake_status"
