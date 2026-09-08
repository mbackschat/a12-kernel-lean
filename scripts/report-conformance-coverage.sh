#!/usr/bin/env bash
# Regenerate docs/CONFORMANCE-COVERAGE.md from ground truth: the Kernel's own error catalogs, this
# repository's owned documents, and its Lean source. Identifier occurrences are vocabulary reach,
# not evidence that the corresponding behaviour is modelled or Kernel-conformant.
#
# The report is DERIVED — it owns no fact it prints, and every number is recomputed from scratch.
#
# A wrong report is worse than no report, so the class-coverage count can be re-derived by a second,
# structurally different mechanism: `--verify` recomputes it with multi-pattern fixed-string whole-word
# matching and aborts on any disagreement. That check has already caught two real defects — a tokeniser
# without a left word boundary reports the Kernel class DATUM as covered because the Java name
# `vergleicheDATUM` contains it, and a `comm` over differently collated inputs corrupts every set
# difference silently. `--verify` also locks capability record boundaries and gap-shard ownership.
# Run it after changing how any coverage axis is counted.
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

capability_counts() {
  awk '
    function close_record() {
      if (!started) return
      total++
      if (calibrated_flag) calibrated++
      if (pending_flag) pending++
      started = 0
    }
    FNR == 1 || /^# / || /^## / { close_record() }
    /^<a id="cap-/ { close_record(); started = 1; calibrated_flag = 0; pending_flag = 0; next }
    started {
      if ($0 ~ /checkpoint|[Kk]ernel-calibrated|L is exact|retained exact [Kk]ernel/) calibrated_flag = 1
      if ($0 ~ /evidence pending|externally uncalibrated/) pending_flag = 1
    }
    END { close_record(); print total+0, calibrated+0, pending+0 }
  ' docs/implementation/*.md
}

gap_counts() {
  awk '
    /^### SG/ { gaps++ }
    /^- `remaining`:/ { remaining++ }
    /^- `route-state`: blocked/ { blocked++ }
    END { print gaps+0, remaining+0, blocked+0 }
  ' docs/gaps/*.md
}

verify_queue_queries() (
  mkdir -p "$work/queue/docs/implementation" "$work/queue/docs/gaps"
  cd "$work/queue"
  cat > docs/implementation/a.md <<'CAPABILITIES'
<a id="cap-pending"></a>
#### Pending
- `assurance`: external evidence pending; checkpoint covers a subset.
<a id="cap-clear-before-heading"></a>
#### Clear
- `assurance`: internal only.
## General policy
A checkpoint may leave external evidence pending.
CAPABILITIES
  cat > docs/implementation/b.md <<'CAPABILITIES'
<a id="cap-clear-before-file"></a>
#### Clear
- `assurance`: internal only.
CAPABILITIES
  cat > docs/implementation/c.md <<'CAPABILITIES'
A checkpoint may leave external evidence pending.
<a id="cap-calibrated"></a>
#### Calibrated
- `assurance`: Kernel-calibrated.
CAPABILITIES
  printf '### SG1 — index entry\n' > docs/SEMANTICS-GAPS.md
  cat > docs/gaps/a.md <<'GAPS'
### SG1 — blocked
- `remaining`: first obligation.
- `remaining`: second obligation.
- `route-state`: blocked — missing carrier.
GAPS
  cat > docs/gaps/b.md <<'GAPS'
### SG2 — ready
- `remaining`: third obligation.
- `route-state`: ready.
GAPS
  local capabilities gaps failed=0
  capabilities="$(capability_counts)"
  gaps="$(gap_counts)"
  if [[ "$capabilities" != '4 2 1' ]]; then
    echo "capability record boundaries: expected '4 2 1', got '${capabilities}'" >&2
    failed=1
  fi
  if [[ "$gaps" != '2 3 1' ]]; then
    echo "gap shard ownership: expected '2 3 1', got '${gaps}'" >&2
    failed=1
  fi
  [[ "$failed" -eq 0 ]]
)

if [[ "$mode" == "verify" ]]; then
  verify_queue_queries
  echo "coverage queue queries preserve record boundaries and read gap shards"
fi

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
read -r capability_records calibrated evidence_pending <<<"$(capability_counts)"

# ---------------------------------------------------------------------------
# Axis 3 — the open obligation load.
# ---------------------------------------------------------------------------
read -r gap_records remaining_rows route_blocked <<<"$(gap_counts)"
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
revision_datetime="$(git show -s --format=%cI HEAD)"
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
  echo "diagnostic names: ${in_lean}/${total_classes} ($(percent "$in_lean" "$total_classes")%) occur in Lean source; ${modelled_untouched} absent"
  echo "  named anywhere: ${touched} ($(percent "$touched" "$total_classes")%) across the scanned prose, Lean, and evidence JSON"
  echo "  in prose ${in_account} | in evidence JSON ${observed} | archived-only ${archived_only} | evidence names absent from prose ${unaccounted}"
  echo "conformance     : no whole-Kernel percentage; identifier occurrence does not establish behaviour"
  echo "capabilities    : ${capability_records} records, ${calibrated} mention checkpoints/calibration, ${evidence_pending} explicitly evidence-pending"
  echo "obligations     : ${gap_records} gaps, ${remaining_rows} remaining rows, ${route_blocked} route-blocked, ${ledger_pending} pending / ${ledger_handed} handed-off"
  echo "estate          : theory ${theory_lines}, support ${support_lines} ($(percent "$support_lines" "$theory_lines")%), evidence ${evidence_lines} ($(percent "$evidence_lines" "$theory_lines")%) nonblank Lean lines, ${unclassified} unclassified"
  echo "evidence        : ${capture_dirs} capture directories, ${observation_rows} inputHash markers in compact observation files"
  echo
  echo "untouched by catalog:"
  awk '{ printf "  %5d  %s\n", $1, $2 }' "$work/by-catalog"
  exit 0
fi

{
cat <<HEADER
# Kernel conformance coverage

<!-- GENERATED FILE — do not edit by hand. Regenerate with \`./scripts/report-conformance-coverage.sh\`. -->

**This report is derived, never authoritative.** It reads the Kernel's error catalogs and runtime formal-code constants under \`../a12-kernel/\`, this repository's owned documents, Lean source, and evidence JSON. Capability status stays in [\`IMPLEMENTATION-MAP.md\`](IMPLEMENTATION-MAP.md), open obligations in [\`SEMANTICS-GAPS.md\`](SEMANTICS-GAPS.md), sequencing in [\`PLAN.md\`](PLAN.md), and provenance in [\`SOURCES.md\`](SOURCES.md). When this file and an owner disagree, the owner is right and this file is stale.

The identifier counts come from maximal-identifier extraction intersected with the Kernel vocabulary. \`./scripts/report-conformance-coverage.sh --verify\` re-derives them by multi-pattern fixed-string whole-word matching and aborts on disagreement. Run it after changing a counting mechanism; it also checks capability record boundaries and gap-shard ownership.

Working-tree counts generated on ${today}; HEAD was \`${revision}\`. The vocabulary scans include untracked files under their named roots; the estate inventory uses tracked paths. This is not a measurement of the exact committed revision's bytes.

## Headline

**Whole-Kernel conformance is not quantified here. ${in_lean} of ${total_classes} diagnostic identifiers occur in Lean source ($(percent "$in_lean" "$total_classes")%); ${modelled_untouched} do not.**

An occurrence can be a definition, fixture, comment, request, or list of exclusions. It establishes neither implemented behaviour nor a matching Kernel observation. The vocabulary denominator also says nothing about successful evaluation, scheduling, addressing, or combinations of features. Use capability scopes, their retained evidence, and open obligations to assess semantic progress; they do not currently supply a complete behavioural denominator either.

## Axis 1 — diagnostic vocabulary, with a finite denominator

| | classes | share |
|---|---|---|
| Distinct identifiers in the selected diagnostic catalogs and runtime formal-code constants | ${total_classes} | 100% |
| Named in \`spec/\` or \`docs/\` prose | ${in_account} | $(percent "$in_account" "$total_classes")% |
| Named in Lean source under \`A12Kernel/\` | ${in_lean} | $(percent "$in_lean" "$total_classes")% |
| Named in JSON under \`evidence/\` | ${observed} | $(percent "$observed" "$total_classes")% |
| Touched by any of the three | ${touched} | $(percent "$touched" "$total_classes")% |
| **Untouched everywhere** | **${untouched}** | **$(percent "$untouched" "$total_classes")%** |

Two occurrence checks that may warrant an ownership lookup:

- **Named in evidence JSON but absent from prose: ${unaccounted}.** Inspect the occurrence before treating it as an unaccounted observation.
- **Named in archived prose but absent from live prose: ${archived_only}.** Check existing ownership before proposing any new work; the name alone establishes no missing semantic fact.

### Where the untouched classes are

Ordered by count for lookup. Semantic priority remains with the plan and live gaps.

| untouched | catalog | route |
|---|---|---|
HEADER

while read -r class_count catalog; do
  printf '| %s | `%s` | %s |\n' "$class_count" "$catalog" "$(route_for "$catalog")"
done < "$work/by-catalog"

cat <<AXES

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour are not measured by diagnostic vocabulary. This text query counts capability records mentioning a checkpoint or calibration, not how much of each family is calibrated. The checkpoint and evidence-pending sets can overlap.

| | records | share |
|---|---|---|
| Capability records in [\`implementation/\`](implementation/) | ${capability_records} | 100% |
| Citing a Kernel checkpoint or calibration | ${calibrated} | $(percent "$calibrated" "$capability_records")% |
| Carrying an explicit evidence-pending note | ${evidence_pending} | $(percent "$evidence_pending" "$capability_records")% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [\`gaps/\`](gaps/), indexed by [\`SEMANTICS-GAPS.md\`](SEMANTICS-GAPS.md) | ${gap_records} |
| \`remaining\` rows across those gaps | ${remaining_rows} |
| Gaps whose route is **blocked** | ${route_blocked} |
| Ledger entries \`pending\` with a12-dmkits | ${ledger_pending} |
| Ledger entries \`handed-off\` | ${ledger_handed} |

A blocked route stops the work that depends on it. Other ready obligations can continue. Remaining-work entries differ in size and may overlap; their count is not a completion percentage.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[\`CLAUDE.md\`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (\`Semantics/\`, \`Elaboration/\`, \`Proofs/\`, \`Conformance/\`, core types) | ${theory_lines} | 100% |
| Support (\`Evidence/\`, \`Reference/\`, \`Process/\`, \`Trust/\`, drivers) | ${support_lines} | $(percent "$support_lines" "$theory_lines")% — ceiling 100% |
| Evidence alone | ${evidence_lines} | $(percent "$evidence_lines" "$theory_lines")% — ceiling 33% |

Tracked Lean files in neither estate: ${unclassified}. A nonzero value means the ratio above measures a subset and the inventory needs review.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under \`../evidence/\` | ${capture_dirs} |
| \`inputHash\` markers in \`*-obs.json\` and \`semantic-observations.json\` | ${observation_rows} |

The marker count excludes other observation formats, including runtime \`artifact.json\` files with \`rows\` arrays. It is neither a total observation count nor a count of independent behavioural discriminators.

## Velocity

One row is appended when one of the recorded counts changes. Flat vocabulary counts do not indicate stalled semantic work: runtime calibration, proofs, and admitted behaviour can advance without introducing a diagnostic name. Historical rows preserve the counts produced by their then-current queries.

Datetime is HEAD's commit time in ISO 8601 format, including its UTC offset; it is not the report's execution time. The revision is context for working-tree counts, not a claim that every counted byte was committed there.

<!-- velocity-history:start -->
| datetime | revision | touched | Lean names | untouched | checkpoint caps | open gaps |
|---|---|---|---|---|---|---|
AXES
} > "$work/report"

new_row="| ${revision_datetime} | \`${revision}\` | ${touched} | ${in_lean} | ${untouched} | ${calibrated} | ${gap_records} |"

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
echo "  ${touched}/${total_classes} diagnostic names touched, ${in_lean} in Lean, ${untouched} untouched"
