#!/usr/bin/env bash
set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
guard="${repository_root}/scripts/check-lean-source-hygiene.sh"

if [[ ! -x "$guard" ]]; then
  echo "source-hygiene self-test requires executable ${guard}" >&2
  exit 1
fi

temporary_root="$(mktemp -d "${TMPDIR:-/tmp}/a12-source-hygiene-test.XXXXXX")"
trap 'rm -rf "$temporary_root"' EXIT

write_nonblank_lines() {
  local path="$1"
  local count="$2"
  local prefix="${3:--- fixture line}"
  awk -v count="$count" -v prefix="$prefix" '
    BEGIN {
      for (line = 1; line <= count; line++) {
        print prefix " " line
      }
    }
  ' > "$path"
}

write_registry_lines() {
  local path="$1"
  local count="$2"
  awk -v count="$count" '
    BEGIN {
      for (line = 1; line <= count; line++) {
        print "#print axioms Example.root" line
      }
    }
  ' > "$path"
}

write_testing_doc() {
  local path="$1"
  shift
  {
    printf '%s\n' '<!-- lean-source-hygiene-exceptions:start -->'
    while (( $# > 0 )); do
      printf '<!-- lean-source-hygiene-exception: %s -->\n' "$1"
      shift
    done
    printf '%s\n' '<!-- lean-source-hygiene-exceptions:end -->'
  } > "$path"
}

new_fixture() {
  local name="$1"
  local fixture="${temporary_root}/${name}"
  mkdir -p "$fixture/scripts" "$fixture/docs" "$fixture/A12Kernel"
  cp "$guard" "$fixture/scripts/check-lean-source-hygiene.sh"
  chmod +x "$fixture/scripts/check-lean-source-hygiene.sh"
  git -C "$fixture" init -q
  printf '%s\n' 'import A12Kernel.Basic' > "$fixture/A12Kernel.lean"
  printf '%s\n' '-- smoke' > "$fixture/A12Kernel/Basic.lean"
  write_testing_doc "$fixture/docs/TESTING.md"
  printf '%s\n' "$fixture"
}

track_fixture() {
  git -C "$1" add .
}

expect_failure() {
  local fixture="$1"
  local expected="$2"
  local output
  if output="$(cd "$fixture" && ./scripts/check-lean-source-hygiene.sh 2>&1)"; then
    echo "source-hygiene self-test expected failure containing: ${expected}" >&2
    exit 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    printf '%s\n' "$output" >&2
    echo "source-hygiene self-test missed diagnostic: ${expected}" >&2
    exit 1
  fi
}

over_ceiling="$(new_fixture over-ceiling)"
write_nonblank_lines "$over_ceiling/A12Kernel/Oversized.lean" 1001
track_fixture "$over_ceiling"
expect_failure "$over_ceiling" "A12Kernel/Oversized.lean: 1001 nonblank lines exceeds the ordinary hard ceiling of 1000"

unreviewed="$(new_fixture unreviewed)"
write_nonblank_lines "$unreviewed/A12Kernel/NeedsReview.lean" 601
track_fixture "$unreviewed"
expect_failure "$unreviewed" "A12Kernel/NeedsReview.lean: 601 nonblank lines requires an exact reviewed exception"

umbrella="$(new_fixture umbrella)"
printf '%s\n' 'import A12Kernel.Basic' 'def executableContent := 1' > "$umbrella/A12Kernel.lean"
track_fixture "$umbrella"
expect_failure "$umbrella" "A12Kernel.lean:2: umbrella roots may contain only imports, comments, and whitespace"

stale="$(new_fixture stale)"
write_testing_doc "$stale/docs/TESTING.md" \
  'A12Kernel/Missing.lean | review-threshold | cohesive reviewed owner'
track_fixture "$stale"
expect_failure "$stale" "stale source-hygiene exception path is not a tracked Lean file: A12Kernel/Missing.lean"

unauthorized="$(new_fixture unauthorized-exception)"
write_nonblank_lines "$unauthorized/A12Kernel/OtherAudit.lean" 1001
write_testing_doc "$unauthorized/docs/TESTING.md" \
  'A12Kernel/OtherAudit.lean | exceptional-ceiling | unauthorized registry'
track_fixture "$unauthorized"
expect_failure "$unauthorized" "only A12Kernel/TrustAudit.lean may use the exceptional-ceiling mode"

duplicate="$(new_fixture duplicate-exception)"
write_nonblank_lines "$duplicate/A12Kernel/Reviewed.lean" 601
write_testing_doc "$duplicate/docs/TESTING.md" \
  'A12Kernel/Reviewed.lean | review-threshold | first rationale' \
  'A12Kernel/Reviewed.lean | review-threshold | second rationale'
track_fixture "$duplicate"
expect_failure "$duplicate" "duplicate source-hygiene exception path: A12Kernel/Reviewed.lean"

malformed_registry="$(new_fixture malformed-registry)"
write_registry_lines "$malformed_registry/A12Kernel/TrustAudit.lean" 1001
printf '%s\n' 'example : True := by trivial' >> "$malformed_registry/A12Kernel/TrustAudit.lean"
write_testing_doc "$malformed_registry/docs/TESTING.md" \
  'A12Kernel/TrustAudit.lean | exceptional-ceiling | single-session theorem-root registry'
track_fixture "$malformed_registry"
expect_failure "$malformed_registry" "A12Kernel/TrustAudit.lean:1002: exceptional registry contains semantic or fixture declaration"

green="$(new_fixture green)"
write_nonblank_lines "$green/A12Kernel/Ordinary.lean" 600
write_nonblank_lines "$green/A12Kernel/Reviewed.lean" 601
write_registry_lines "$green/A12Kernel/TrustAudit.lean" 1001
write_testing_doc "$green/docs/TESTING.md" \
  'A12Kernel/Reviewed.lean | review-threshold | cohesive reviewed owner' \
  'A12Kernel/TrustAudit.lean | exceptional-ceiling | single-session theorem-root registry'
mkdir -p "$green/.lake/build"
write_nonblank_lines "$green/.lake/build/Generated.lean" 1200
track_fixture "$green"
if ! output="$(cd "$green" && ./scripts/check-lean-source-hygiene.sh 2>&1)"; then
  printf '%s\n' "$output" >&2
  echo "source-hygiene self-test expected the valid fixture to pass" >&2
  exit 1
fi
if [[ "$output" != "Lean source hygiene passed: 5 tracked files; largest ordinary file 601 nonblank lines; 2 reviewed exceptions" ]]; then
  printf 'unexpected source-hygiene success summary: %s\n' "$output" >&2
  exit 1
fi

echo "Lean source-hygiene self-test passed"
