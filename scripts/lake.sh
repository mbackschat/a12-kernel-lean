#!/usr/bin/env bash
# The entry point for every local `lake` and `lake env lean` command: same arguments as `lake`.
#
# It exists so that two Lean process trees never share a host. On 2026-10-22 one host ran
# Lean-building sessions of this repository and of bpmn-lean-experiment side by side; that
# project's own wrapper records whole-build peaks of 2.4-8 GB, while the heaviest modules measured
# here peak below 1 GiB each. The lock is therefore host-wide by name, not per repository:
# bpmn-lean-experiment's wrapper must take the same path for either side to see the other. A second
# tree is refused rather than queued, and the holder's pid tells a live build from a stale lock.
#
# The pin replaces any inherited LEAN_NUM_THREADS, which sizes Lake's job pool and each Lean
# process's task pool. 8 is the default of the 8-core host on which no memory failure is recorded,
# so the pin changes nothing there and keeps a larger host or an override from multiplying the peak.
set -euo pipefail

lean_build_threads=8
lean_build_lock="/tmp/lean-build-$(id -u).lock"

if ! mkdir "$lean_build_lock" 2>/dev/null; then
  holder="$(cat "$lean_build_lock/pid" 2>/dev/null || true)"
  if [[ -n "$holder" ]] && kill -0 "$holder" 2>/dev/null; then
    echo "LEAN_BUILD_REFUSED another Lean build is active (pid ${holder}, lock ${lean_build_lock})" >&2
  else
    echo "LEAN_BUILD_REFUSED the lock ${lean_build_lock} has no live holder (recorded pid: ${holder:-none}); remove it only after confirming no Lean build is running" >&2
  fi
  exit 75
fi
release_lock() {
  rm -f "$lean_build_lock/pid"
  rmdir "$lean_build_lock" 2>/dev/null || true
}
trap release_lock EXIT
trap 'exit 130' HUP INT TERM
printf '%s\n' "$$" > "$lean_build_lock/pid"

export LEAN_NUM_THREADS="$lean_build_threads"
lake "$@"
