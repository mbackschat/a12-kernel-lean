#!/usr/bin/env bash
set -euo pipefail

# Guards both halves of what a behavioral spec/ change owes, in two rungs.
#
# Rung 1, synchronization: the change carries its direction. The synchronization ledger
# owns a locally originated correction; SOURCES.md owns an inbound one already committed
# and reviewed upstream. This guard is deliberately git-only and cheap, because a spec/
# edit normally lands as a docs(spec) commit and therefore skips every Lean rung, which is
# how commit 972bede reached main without its entry.
#
# Rung 2, adoption: the change reached the theory, or says in words why it did not. Rung 1
# alone let two measured distinctions enter spec/ while the Lean account stayed silent —
# the completed-period difference family answered whether a pair is admitted where the
# Kernel reports three distinct codes, and the enumeration category arity surfaced one
# error where the Kernel picks two by direction. Both passed every gate, because nothing
# asked the question. A clause-level audit on 2026-09-22 found five divergences of that
# kind and its two mirror images, where a peer claim reached spec/ against this
# repository's own measurement.
#
# Touching A12Kernel/ is a weak proxy for adoption and is meant to be. The gate is not
# trying to prove the clause was modelled; it is trying to stop non-adoption from being
# SILENT. A clause with no executable counterpart is ordinary and often correct — the
# parser layer, an unmodelled family, a reachability annotation — so the escape hatch is
# one variable. What it buys is a sentence a reviewer can disagree with, in place of an
# absence nobody can see.

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

# A non-behavioral change owes neither rung: it states no new Kernel behaviour, so there is
# nothing to synchronize and nothing for the theory to adopt.
if [[ "${A12_SPEC_CHANGE_IS_NONBEHAVIORAL:-}" == "1" ]]; then
  echo "spec synchronization guard passed: change declared non-behavioral by the author" >&2
  exit 0
fi

if printf '%s\n' "$changed_paths" \
  | grep -qxE 'docs/(A12-DMKITS-SPEC-SYNC-LEDGER|SOURCES)\.md'; then

  # Rung 2 runs only once rung 1 is satisfied, so one failure message appears at a time and
  # names the rung the author still owes.
  if printf '%s\n' "$changed_paths" | grep -qE '^A12Kernel/'; then
    echo "spec synchronization guard passed: the spec/ change carries a synchronization owner and reaches the theory"
    exit 0
  fi

  if [[ -n "${A12_SPEC_CHANGE_HAS_NO_LEAN_OWNER:-}" ]]; then
    echo "spec synchronization guard passed: the spec/ change carries a synchronization owner" >&2
    echo "  adoption waived by the author: ${A12_SPEC_CHANGE_HAS_NO_LEAN_OWNER}" >&2
    echo "  put that reason in the commit body, where the next reader meets it" >&2
    exit 0
  fi

  {
    echo "spec synchronization guard failed: a behavioral spec/ change did not reach the theory"
    echo "  changed spec/ files:"
    printf '%s\n' "$spec_changes" | sed 's/^/    /'
    cat <<'EOF'
  The synchronization owner is present, so the direction is classified. What is missing is
  whether the clause reached the executable account. Choose one:
    - it did: land the semantic, proof, or conformance change under A12Kernel/ in this same
      change, so the distinction the clause states is decidable rather than only written;
    - it did not, and that is correct: say why, in a sentence that belongs in the commit body,
      with
        A12_SPEC_CHANGE_HAS_NO_LEAN_OWNER="<reason>" ./scripts/check-spec-sync.sh
      Ordinary reasons: the clause is parser-layer and this project models no parser; its
      family is unmodelled and the gap record owns it; it is a reachability or authorability
      annotation, which by the discharge rule may not gate a semantic clause anyway.
  A clause whose distinction no case can decide is prose, and prose does not fail when the
  account drifts. If the honest answer is "not yet", record it as a gap and waive here.
EOF
  } >&2
  exit 1
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
