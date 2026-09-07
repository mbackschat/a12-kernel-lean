#!/usr/bin/env bash
# Regenerate docs/CONFORMANCE-COVERAGE.md from ground truth: the Kernel's own error catalogs, this
# repository's owned documents, and its tracked Lean source.
#
# The report is DERIVED — it owns no fact it prints, and every number is recomputed from scratch.
#
# A wrong report is worse than no report, so the class-coverage count can be re-derived by a second,
# structurally different mechanism: `--verify` recomputes it with multi-pattern fixed-string whole-word
# matching and aborts on any disagreement. That check has already caught two real defects — a tokeniser
# without a left word boundary reports the Kernel class DATUM as covered because the Java name
# `vergleicheDATUM` contains it, and a `comm` over differently collated inputs corrupts every set
# difference silently. Run `--verify` after changing anything in Axis 1.
set -euo pipefail

for required_tool in awk grep sort uniq comm wc find git xargs; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    echo "conformance coverage report requires ${required_tool}" >&2
    exit 1
  fi
done

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

# `comm` is only valid when both inputs are collated identically, and the developer locale is not C:
# under de_DE, `sort` places BICINTERNATIONAL_FORMALER_FEHLER differently, which silently corrupts
# every set difference below rather than failing. Pin the collation once for the whole run.
export LC_ALL=C

kernel_root="../a12-kernel"
report="docs/CONFORMANCE-COVERAGE.md"
mode="update"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --print) mode="print" ;;
    --update) mode="update" ;;
    --verify) mode="verify" ;;
    *) echo "usage: $0 [--update|--print|--verify]" >&2; exit 2 ;;
  esac
  shift
done

if [[ ! -d "$kernel_root" ]]; then
  echo "the Kernel checkout ${kernel_root} is required for the refusal-class denominator" >&2
  echo "it is read-only input; this report never writes outside this repository" >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

percent() { if [[ "${2:-0}" -eq 0 ]]; then echo 0; else echo $(( 100 * $1 / $2 )); fi; }
count() { wc -l < "$1" | tr -d ' '; }

# ---------------------------------------------------------------------------
# Axis 1 — static legality: the Kernel's own refusal classes.
#
# The English catalogs are the denominator because a class the Kernel cannot name in English cannot
# reach an en_US probe, the only carrier measured so far. `build/` is pruned rather than filtered so
# the traversal stays cheap on a large sibling checkout.
# ---------------------------------------------------------------------------
find "$kernel_root/kernel-tool" "$kernel_root/kernel-rt" \
  \( -name build -o -name .git \) -prune -o \
  -name 'error_messages_en.properties' -print \
  | sort > "$work/catalogs"

# shellcheck disable=SC2046
awk '
  FNR == 1 { split(FILENAME, parts, "/internal/"); split(parts[2], seg, "/"); catalog = seg[1] }
  /^[A-Z][A-Z0-9_]*=/ { split($0, kv, "="); print kv[1] "\t" catalog }
' $(cat "$work/catalogs") | sort -u > "$work/class-catalog"

# The runtime formal checks answer on TWO independent axes, and the message bundles above carry only
# one of them. `FehlerHandler.addFehler(errorKey, fehlerText, …)` takes the surfaced code and the
# already-resolved text as separate arguments: `getFehlertext` picks the bundle key from the abstract
# error AND the number art, while the code comes from the abstract error alone. So the four
# ZAHL_ZUVIELE_VORKOMMASTELLEN_* keys are four texts behind one observable `zahlZuvieleVorkommastellen`
# — and conversely no bundle key names the code a `validateFull` consumer actually reads. Counting the
# codes as their own catalog is what keeps the consumer-visible vocabulary in the denominator.
formal_codes="$kernel_root/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/util/IFormaleFehlerConstants.java"
if [[ -f "$formal_codes" ]]; then
  grep -o '= *"[A-Za-z0-9_]*"' "$formal_codes" \
    | sed 's/= *"//; s/"$//' \
    | awk 'NF { print $0 "\truntime_formal_codes" }' \
    | sort -u >> "$work/class-catalog"
  sort -u -o "$work/class-catalog" "$work/class-catalog"
else
  echo "runtime formal-code vocabulary not found at ${formal_codes}; the Kernel layout has changed" >&2
  exit 1
fi

cut -f1 "$work/class-catalog" | sort -u > "$work/classes"
total_classes="$(count "$work/classes")"

if [[ "$total_classes" -eq 0 ]]; then
  echo "no refusal classes found under ${kernel_root}; the catalog layout has changed" >&2
  exit 1
fi

# Primary mechanism: extract every **maximal** identifier run, then intersect with the class set.
# Taking the maximal run is what makes it exact in both directions — `vergleicheDATUM` yields that
# whole identifier, which is not equal to `DATUM`, so the Kernel class is not reported as covered,
# while a standalone occurrence always is. The anchored shape filter that follows only shrinks the set
# before the join; exactness lives in the join, which is why widening it to admit the camelCase
# `runtime_formal_codes` names cannot introduce a partial match. `--verify` re-derives the same answer
# through whole-word fixed-string matching, a mechanism that shares neither step.
class_hits() { # $1 out, $2 include glob, rest: named content roots (never the repository root)
  local out="$1" include="$2"; shift 2
  grep -oh -E '[A-Za-z0-9_]+' -r "$@" --include="$include" 2>/dev/null \
    | grep -E '^[A-Za-z][A-Za-z0-9_]+$' | sort -u > "$work/tokens" || : > "$work/tokens"
  comm -12 "$work/classes" "$work/tokens" > "$out"
}

# Audit mechanism, structurally different: multi-pattern fixed-string whole-word matching. It is kept
# out of the default path only because BSD grep's `-F -f` with 441 patterns and `-w` costs about
# eleven seconds per corpus against this one's forty milliseconds — a measured 250x, not a guess.
audit_hits() { # $1 out, $2 include glob, rest: named content roots
  local out="$1" include="$2"; shift 2
  grep -ohw -F -f "$work/classes" -r "$@" --include="$include" 2>/dev/null \
    | sort -u > "$out" || : > "$out"
}

class_hits "$work/in-account"  '*.md'   spec docs
class_hits "$work/in-lean"     '*.lean' A12Kernel
class_hits "$work/in-observed" '*.json' evidence

if [[ "$mode" == "verify" ]]; then
  audit_hits "$work/check-account"  '*.md'   spec docs
  audit_hits "$work/check-lean"     '*.lean' A12Kernel
  audit_hits "$work/check-observed" '*.json' evidence
  for corpus in account lean observed; do
    if ! diff -q "$work/in-${corpus}" "$work/check-${corpus}" >/dev/null; then
      echo "coverage mechanism disagreement in the ${corpus} corpus — the report would be wrong" >&2
      diff "$work/in-${corpus}" "$work/check-${corpus}" >&2 || true
      exit 1
    fi
  done
  echo "coverage mechanisms agree on all three corpora (${total_classes} classes checked)"
fi

sort -u "$work/in-account" "$work/in-lean" "$work/in-observed" > "$work/touched"
in_account="$(count "$work/in-account")"
in_lean="$(count "$work/in-lean")"
observed="$(count "$work/in-observed")"
touched="$(count "$work/touched")"
untouched="$(( total_classes - touched ))"
modelled_untouched="$(( total_classes - in_lean ))"
unaccounted="$(comm -23 "$work/in-observed" "$work/in-account" | count /dev/stdin)"

# A class known only from an archived receipt is a fact this repository holds but no longer reads.
grep -oh -E '[A-Za-z0-9_]+' -r spec docs --include='*.md' --exclude-dir=archived 2>/dev/null \
  | grep -E '^[A-Za-z][A-Za-z0-9_]+$' | sort -u > "$work/live-tokens" || : > "$work/live-tokens"
comm -12 "$work/classes" "$work/live-tokens" > "$work/live-account"
archived_only="$(comm -23 "$work/in-account" "$work/live-account" | count /dev/stdin)"

comm -23 "$work/classes" "$work/touched" > "$work/untouched-classes"
awk -F'\t' 'NR==FNR { open[$1]=1; next } ($1 in open) { print $2 }' \
  "$work/untouched-classes" "$work/class-catalog" | sort | uniq -c | sort -rn > "$work/by-catalog"

# ---------------------------------------------------------------------------
# Axis 2 — admitted behaviour, which no class name reaches. One pass, flag-based per record: an
# earlier version accumulated each record's text by string concatenation, which is quadratic and cost
# the whole run 57 seconds on its own.
# ---------------------------------------------------------------------------
read -r capability_records calibrated evidence_pending <<<"$(awk '
  function close_record() {
    if (!started) return
    total++
    if (calibrated_flag) calibrated++
    if (pending_flag) pending++
  }
  /^<a id="cap-/ { close_record(); started = 1; calibrated_flag = 0; pending_flag = 0; next }
  started {
    if ($0 ~ /checkpoint|[Kk]ernel-calibrated|L is exact|retained exact [Kk]ernel/) calibrated_flag = 1
    if ($0 ~ /evidence pending|externally uncalibrated/) pending_flag = 1
  }
  END { close_record(); print total+0, calibrated+0, pending+0 }
' docs/implementation/*.md)"

# ---------------------------------------------------------------------------
# Axis 3 — the open obligation load.
# ---------------------------------------------------------------------------
gap_records="$(grep -c '^### SG' docs/SEMANTICS-GAPS.md || true)"
remaining_rows="$(grep -c '^- `remaining`:' docs/SEMANTICS-GAPS.md || true)"
route_blocked="$(grep -c '^- `route-state`: blocked' docs/SEMANTICS-GAPS.md || true)"
ledger_pending="$(grep -c '^- `status`: pending' docs/A12-DMKITS-SPEC-SYNC-LEDGER.md || true)"
ledger_handed="$(grep -c '^- `status`: handed-off' docs/A12-DMKITS-SPEC-SYNC-LEDGER.md || true)"

# ---------------------------------------------------------------------------
# Axis 4 — the estate ratio CLAUDE.md makes a standing guard: support must not exceed theory, and
# evidence alone should stay below one third of theory. Nothing else computes it.
# ---------------------------------------------------------------------------
nonblank_lines() { # tracked paths on stdin
  LC_ALL=C xargs grep -hcv '^[[:space:]]*$' 2>/dev/null | awk '{ s += $1 } END { print s+0 }'
}

git ls-files 'A12Kernel/Core.lean' 'A12Kernel/Cell.lean' 'A12Kernel/Document.lean' \
  'A12Kernel/Basic.lean' 'A12Kernel.lean' 'A12Kernel/Proofs.lean' 'A12Kernel/Conformance.lean' \
  'A12Kernel/Semantics/*' 'A12Kernel/Elaboration/*' 'A12Kernel/Proofs/*' 'A12Kernel/Conformance/*' \
  | grep '\.lean$' | sort -u > "$work/theory-files"
git ls-files 'A12Kernel/Evidence/*' 'A12Kernel/Reference/*' 'A12Kernel/Process/*' \
  'A12Kernel/Trust/*' 'A12Kernel/TrustAudit.lean' 'A12Kernel/*Main.lean' \
  | grep '\.lean$' | sort -u > "$work/support-files"
git ls-files 'A12Kernel/Evidence/*' | grep '\.lean$' | sort -u > "$work/evidence-files"

theory_lines="$(nonblank_lines < "$work/theory-files")"
support_lines="$(nonblank_lines < "$work/support-files")"
evidence_lines="$(nonblank_lines < "$work/evidence-files")"

# Every tracked Lean file must land in exactly one estate, or the ratio guard is measuring a subset.
git ls-files '*.lean' | sort -u > "$work/all-lean"
sort -u "$work/theory-files" "$work/support-files" > "$work/classified"
unclassified="$(comm -23 "$work/all-lean" "$work/classified" | count /dev/stdin)"

# ---------------------------------------------------------------------------
# Axis 5 — retained empirical backbone.
# ---------------------------------------------------------------------------
capture_dirs="$(find evidence -mindepth 3 -maxdepth 3 -type d | count /dev/stdin)"
observation_rows="$(find evidence -type f \
  \( -name '*-obs.json' -o -name 'semantic-observations.json' \) -print0 \
  | LC_ALL=C xargs -0 grep -oh '"inputHash"' 2>/dev/null | count /dev/stdin)"

# ---------------------------------------------------------------------------
# Render.
# ---------------------------------------------------------------------------
revision="$(git rev-parse --short HEAD)"
today="$(date +%Y-%m-%d)"

route_for() {
  case "$1" in
    _30_8) echo 'runtime formal-error **texts** — a **document** probe (`:adapter:kernelProbe` → `validateFull`); finer than the code below, since art and sign pick the text' ;;
    runtime_formal_codes) echo 'runtime formal-error **codes** a `validateFull` consumer actually reads — same document probe' ;;
    vk_parser_error_messages) echo 'condition/DSL static legality — the fast `dmtool rule check` batch route' ;;
    vk_service_errortext_error_messages) echo 'message templates and parameters — the fast `rule check --message` batch route' ;;
    custom_field_types) echo 'host-registered custom field types — **scope question**, may sit outside the Kernel-owned target' ;;
    vk_codegen_no_meta_model_ckecks_error_messages) echo 'codegen-time model checks — reachable through `model check`' ;;
    vk_calc_error_messages) echo 'computation authoring — the `computation add --dry-run` batch route' ;;
    vk_dynEnum_error_messages) echo 'dynamic enumerations — needs a dynamic-enum declaration shape' ;;
    kernel_core_errortext_error_messages) echo 'shared error-text base utilities — carrier not yet identified' ;;
    vk_parser_common_error_messages) echo 'shared parser diagnostics — the fast `rule check` batch route' ;;
    test_rule_error_messages) echo 'on-the-fly rule testing — likely instrument-only, not a semantic class' ;;
    *) echo 'route not yet identified' ;;
  esac
}

if [[ "$mode" == "verify" ]]; then
  exit 0
fi

if [[ "$mode" == "print" ]]; then
  echo "MODELLED        : ${in_lean}/${total_classes} ($(percent "$in_lean" "$total_classes")%) — the figure that counts; ${modelled_untouched} not yet modelled"
  echo "  also touched in prose only: ${touched} ($(percent "$touched" "$total_classes")%) — an upper bound on knowledge, trivially inflatable, never the target"
  echo "  in prose ${in_account} | observed ${observed} | archived-only ${archived_only} | observed-unaccounted ${unaccounted} (want 0)"
  echo "capabilities    : ${capability_records} records, ${calibrated} calibrated, ${evidence_pending} evidence-pending"
  echo "obligations     : ${gap_records} gaps, ${remaining_rows} remaining rows, ${route_blocked} route-blocked, ${ledger_pending} pending / ${ledger_handed} handed-off"
  echo "estate          : theory ${theory_lines}, support ${support_lines} ($(percent "$support_lines" "$theory_lines")%), evidence ${evidence_lines} ($(percent "$evidence_lines" "$theory_lines")%) nonblank Lean lines, ${unclassified} unclassified"
  echo "evidence        : ${capture_dirs} captures, ${observation_rows} observation rows"
  echo
  echo "untouched by catalog:"
  awk '{ printf "  %5d  %s\n", $1, $2 }' "$work/by-catalog"
  exit 0
fi

{
cat <<HEADER
# Kernel conformance coverage

<!-- GENERATED FILE — do not edit by hand. Regenerate with \`./scripts/report-conformance-coverage.sh\`. -->

**This report is derived, never authoritative.** Every number is recomputed from the Kernel's own error
catalogs under \`../a12-kernel/\`, this repository's owned documents, and its tracked Lean source. It owns
no fact: capability status stays in [\`IMPLEMENTATION-MAP.md\`](IMPLEMENTATION-MAP.md), open obligations in
[\`SEMANTICS-GAPS.md\`](SEMANTICS-GAPS.md), sequencing in [\`PLAN.md\`](PLAN.md), provenance in
[\`SOURCES.md\`](SOURCES.md). When this file and an owner disagree, the owner is right and this file is stale.

The class counts come from one mechanism — maximal-identifier extraction intersected with the Kernel's
class set — and \`./scripts/report-conformance-coverage.sh --verify\` re-derives them by a structurally
different one, multi-pattern fixed-string whole-word matching, aborting on any disagreement. The audit is
not on the default path because it costs about forty seconds against this one's four. Run it after any
change to how coverage is counted; it has already caught two real defects, recorded in the script.

Measured at \`${revision}\` on ${today}.

## Headline

**${in_lean} of ${total_classes} Kernel refusal classes modelled in Lean ($(percent "$in_lean" "$total_classes")%). ${modelled_untouched} are not.**

That is the project's progress figure and the only one worth quoting. A secondary count, *touched*, stands
at ${touched} ($(percent "$touched" "$total_classes")%): it counts a class named anywhere in the written
account, **including a checkpoint's own list of what it deliberately did not reach**. Touched is an upper
bound on what this repository knows about, and it can be raised to 100% in an afternoon by writing prose,
so it is reported to expose that gap rather than to stand in for progress. When the two are quoted
together the modelled figure leads.

## Axis 1 — static legality, the one axis with a real denominator

| | classes | share |
|---|---|---|
| Distinct refusal classes in the Kernel's \`error_messages_en.properties\` catalogs | ${total_classes} | 100% |
| Named in \`spec/\` or \`docs/\` prose | ${in_account} | $(percent "$in_account" "$total_classes")% |
| Named in tracked Lean source | ${in_lean} | $(percent "$in_lean" "$total_classes")% |
| Observed in a retained probe artifact | ${observed} | $(percent "$observed" "$total_classes")% |
| Touched by any of the three | ${touched} | $(percent "$touched" "$total_classes")% |
| **Untouched everywhere** | **${untouched}** | **$(percent "$untouched" "$total_classes")%** |

Two hygiene readings, both of which should stay at zero or be acted on:

- **Observed but absent from the written account: ${unaccounted}.** A class seen in a probe and never
  written down is a measurement whose result was lost.
- **Known only from archived material: ${archived_only}.** These are facts this repository holds but no
  longer reads; they belong in a live owner or should be re-measured.

### Where the untouched classes are

Ordered by size, because that is the order in which they are worth attacking.

| untouched | catalog | route |
|---|---|---|
HEADER

while read -r class_count catalog; do
  printf '| %s | `%s` | %s |\n' "$class_count" "$catalog" "$(route_for "$catalog")"
done < "$work/by-catalog"

cat <<AXES

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour produce no
refusal class, so Axis 1 is blind to them. The capability records are the available proxy, and a coarser
one: it counts whether a record cites external calibration, not how much of its family is covered.

| | records | share |
|---|---|---|
| Capability records in [\`implementation/\`](implementation/) | ${capability_records} | 100% |
| Citing a Kernel checkpoint or calibration | ${calibrated} | $(percent "$calibrated" "$capability_records")% |
| Carrying an explicit evidence-pending note | ${evidence_pending} | $(percent "$evidence_pending" "$capability_records")% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [\`SEMANTICS-GAPS.md\`](SEMANTICS-GAPS.md) | ${gap_records} |
| \`remaining\` rows across those gaps | ${remaining_rows} |
| Gaps whose route is **blocked** | ${route_blocked} |
| Ledger entries \`pending\` with a12-dmkits | ${ledger_pending} |
| Ledger entries \`handed-off\` | ${ledger_handed} |

A blocked route is the only figure here that should stop work; a \`remaining\` row is ordinary scope. If
blocked is nonzero, that is what to escalate.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[\`CLAUDE.md\`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and
evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (\`Semantics/\`, \`Elaboration/\`, \`Proofs/\`, \`Conformance/\`, core types) | ${theory_lines} | 100% |
| Support (\`Evidence/\`, \`Reference/\`, \`Process/\`, \`Trust/\`, drivers) | ${support_lines} | $(percent "$support_lines" "$theory_lines")% — ceiling 100% |
| Evidence alone | ${evidence_lines} | $(percent "$evidence_lines" "$theory_lines")% — ceiling 33% |

Tracked Lean files in neither estate: ${unclassified}. A nonzero value means the ratio above is measuring
a subset, so it is a defect in this generator rather than in the estate.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under \`../evidence/\` | ${capture_dirs} |
| Retained observation rows across all artifacts | ${observation_rows} |

## Velocity

One row is appended per run, and only when a headline number moved — so a flat \`touched\` column across
several dated rows is the signal that progression has stalled. The actionable reading when it does is
Axis 1's route column: a stall usually means the remaining blocks need a route this session has not set
up, rather than more rows on the route it already has.

<!-- velocity-history:start -->
| date | revision | touched | modelled | untouched | calibrated caps | open gaps |
|---|---|---|---|---|---|---|
AXES
} > "$work/report"

new_row="| ${today} | \`${revision}\` | ${touched} | ${in_lean} | ${untouched} | ${calibrated} | ${gap_records} |"

: > "$work/history"
if [[ -f "$report" ]]; then
  awk '/^<!-- velocity-history:start -->/ { inside = 1; next }
       /^<!-- velocity-history:end -->/ { inside = 0 }
       inside && /^\| 2[0-9][0-9][0-9]-/ { print }' "$report" > "$work/history"
fi
cat "$work/history" >> "$work/report"

last_numbers="$(tail -n 1 "$work/history" 2>/dev/null | awk -F'|' '{ print $4 $5 $6 $7 $8 }' | tr -d ' ')"
new_numbers="$(echo "$new_row" | awk -F'|' '{ print $4 $5 $6 $7 $8 }' | tr -d ' ')"
if [[ "$last_numbers" != "$new_numbers" ]]; then
  echo "$new_row" >> "$work/report"
fi
printf '<!-- velocity-history:end -->\n' >> "$work/report"

mv "$work/report" "$report"
echo "conformance coverage report written: ${report}"
echo "  ${touched}/${total_classes} classes touched, ${in_lean} modelled, ${untouched} untouched"
