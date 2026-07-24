#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

usage() {
  echo "usage: ./scripts/prepare-github-publish.sh --check|--update" >&2
}

case "${1:-}" in
  --check|--update)
    mode="$1"
    ;;
  *)
    usage
    exit 2
    ;;
esac

trust_summary=""
if ! trust_summary="$(./scripts/check-lean-trust.sh)"; then
  echo "GitHub publication preparation failed: trust audit did not pass" >&2
  exit 1
fi
printf '%s\n' "$trust_summary"

if [[ ! "$trust_summary" =~ ^trusted[[:space:]]theorem[[:space:]]audit[[:space:]]passed:[[:space:]]([1-9][0-9]*)[[:space:]]theorem[[:space:]]roots\;[[:space:]]([1-9][0-9]*)[[:space:]]declarations[[:space:]]in[[:space:]]([1-9][0-9]*)[[:space:]]modules$ ]]; then
  echo "GitHub publication preparation failed: unrecognized trust-audit summary" >&2
  exit 1
fi

format_count() {
  awk -v number="$1" '
    BEGIN {
      formatted = ""
      while (length(number) > 3) {
        formatted = "," substr(number, length(number) - 2) formatted
        number = substr(number, 1, length(number) - 3)
      }
      print number formatted
    }
  '
}

theorem_count="$(format_count "${BASH_REMATCH[1]}")"
declaration_count="$(format_count "${BASH_REMATCH[2]}")"
module_count="$(format_count "${BASH_REMATCH[3]}")"

start_marker="<!-- github-publish-stats:start -->"
end_marker="<!-- github-publish-stats:end -->"
expected_line="**Verified at publication:** **${theorem_count} trusted theorem roots**, **${declaration_count} audited declarations**, and **${module_count} trusted modules** in the mechanized theory."

start_count="$(grep -Fxc "$start_marker" README.md || true)"
end_count="$(grep -Fxc "$end_marker" README.md || true)"
if [[ "$start_count" != 1 || "$end_count" != 1 ]]; then
  echo "GitHub publication preparation failed: README statistics markers must occur exactly once" >&2
  exit 1
fi

current_line="$(awk -v start="$start_marker" -v end="$end_marker" '
  $0 == start { inside = 1; next }
  $0 == end { inside = 0 }
  inside { print }
' README.md)"

if [[ "$mode" == "--check" ]]; then
  if [[ "$current_line" != "$expected_line" ]]; then
    echo "README trust statistics are stale; run ./scripts/prepare-github-publish.sh --update before publishing" >&2
    echo "expected: $expected_line" >&2
    exit 1
  fi
  echo "README trust statistics are current"
  exit 0
fi

temporary_readme="$(mktemp "${TMPDIR:-/tmp}/a12-kernel-lean-readme.XXXXXX")"
trap 'rm -f "$temporary_readme"' EXIT
awk -v start="$start_marker" -v end="$end_marker" -v replacement="$expected_line" '
  $0 == start {
    print
    print replacement
    inside = 1
    next
  }
  $0 == end {
    inside = 0
    print
    next
  }
  !inside { print }
' README.md > "$temporary_readme"
mv "$temporary_readme" README.md
trap - EXIT
echo "README trust statistics updated; review and commit the change before an explicit GitHub push"
