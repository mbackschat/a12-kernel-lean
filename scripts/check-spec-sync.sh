#!/usr/bin/env bash
set -euo pipefail

# Guards the outbound half of the a12-dmkits contract: a behavioral spec/ change must
# carry its synchronization classification in the same change. The synchronization ledger
# owns a locally originated correction; SOURCES.md owns an inbound one already committed
# and reviewed upstream. This guard is deliberately git-only and cheap, because a spec/
# edit normally lands as a docs(spec) commit and therefore skips every Lean rung, which is
# how commit 972bede reached main without its entry.

for required_tool in git grep sed sort; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    echo "spec synchronization guard requires ${required_tool}" >&2
    exit 1
  fi
done

changed_paths="$(
  {
    git diff HEAD --name-only
    git ls-files --others --exclude-standard
  } | sort -u
)"

spec_changes="$(printf '%s\n' "$changed_paths" | grep -E '^spec/.*\.md$' || true)"

if [[ -z "$spec_changes" ]]; then
  echo "spec synchronization guard passed: no spec/ change in this working state"
  exit 0
fi

if printf '%s\n' "$changed_paths" \
  | grep -qxE 'docs/(A12-DMKITS-SPEC-SYNC-LEDGER|SOURCES)\.md'; then
  echo "spec synchronization guard passed: the spec/ change carries a synchronization owner"
  exit 0
fi

if [[ "${A12_SPEC_CHANGE_IS_NONBEHAVIORAL:-}" == "1" ]]; then
  echo "spec synchronization guard passed: change declared non-behavioral by the author" >&2
  exit 0
fi

{
  echo "spec synchronization guard failed: a spec/ change carries no synchronization classification"
  echo "  changed spec/ files:"
  printf '%s\n' "$spec_changes" | sed 's/^/    /'
  cat <<'EOF'
  Classify the direction before committing, per the ledger contract:
    - locally originated and still needing reconciliation: add or update an entry in
      docs/A12-DMKITS-SPEC-SYNC-LEDGER.md in this same change;
    - inbound from an exact committed and reviewed a12-dmkits revision: record that
      revision and its evidence routes in docs/SOURCES.md instead, and create no
      outbound entry merely to echo the finding back to its origin;
    - pure spelling, formatting, link, or navigation-only: exempt, and declared with
      A12_SPEC_CHANGE_IS_NONBEHAVIORAL=1 ./scripts/check-spec-sync.sh
EOF
} >&2
exit 1
