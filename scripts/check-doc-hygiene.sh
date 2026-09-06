#!/usr/bin/env bash
set -euo pipefail

for required_tool in awk grep sort uniq wc; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    echo "documentation hygiene guard requires ${required_tool}" >&2
    exit 1
  fi
done

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

operational_documents=(
  docs/IMPLEMENTATION-MAP.md
  docs/implementation/*.md
  docs/SEMANTICS-GAPS.md
  docs/SOURCES.md
  docs/sources/*.md
)

failed=false

for document in "${operational_documents[@]}"; do
  if [[ ! -f "$document" ]]; then
    echo "documentation hygiene owner is missing: ${document}" >&2
    failed=true
    continue
  fi

  document_size="$(wc -c < "$document")"
  if (( document_size > 200000 )); then
    echo "${document}: operational document has ${document_size} bytes; split it before the 200000-byte hard ceiling" >&2
    failed=true
  fi

  while IFS=$'\t' read -r line_number line_length; do
    [[ -z "$line_number" ]] && continue
    echo "${document}:${line_number}: claim line has ${line_length} characters; hard ceiling is 1000" >&2
    failed=true
  done < <(awk 'length($0) > 1000 { print NR "\t" length($0) }' "$document")

  while IFS=$'\t' read -r line_number semicolons; do
    [[ -z "$line_number" ]] && continue
    echo "${document}:${line_number}: claim line has ${semicolons} semicolons; split independent claims instead of appending them" >&2
    failed=true
  done < <(awk '{ line = $0; count = gsub(/;/, ";", line); if (count > 4) print NR "\t" count }' "$document")
done

status_owners=(
  docs/IMPLEMENTATION-MAP.md
  docs/implementation/*.md
  docs/SEMANTICS-GAPS.md
)

for status_owner in "${status_owners[@]}"; do
  while IFS=: read -r line_number _; do
    [[ -z "$line_number" ]] && continue
    echo "${status_owner}:${line_number}: exact revision/hash identity belongs in SOURCES.md or EVIDENCE.md; link its keyed record here" >&2
    failed=true
  done < <(grep -En '([0-9a-fA-F]{40,}|`[0-9a-fA-F]{7,64}`)' "$status_owner" || true)
done

check_anchored_record_size() {
  local document="$1"
  local anchor_prefix="$2"
  local ceiling="$3"

  while IFS=$'\t' read -r line_number record_size anchor_id; do
    [[ -z "$line_number" ]] && continue
    echo "${document}:${line_number}: ${anchor_id} has ${record_size} bytes; split the record before the ${ceiling}-byte hard ceiling" >&2
    failed=true
  done < <(awk -v prefix="$anchor_prefix" -v ceiling="$ceiling" '
    function flush() {
      if (anchor != "" && bytes > ceiling) print start "\t" bytes "\t" anchor
    }
    $0 ~ "^<a id=\"" prefix {
      flush()
      anchor = $0
      sub(/^<a id="/, "", anchor)
      sub(/"><\/a>$/, "", anchor)
      start = NR
      bytes = 0
    }
    anchor != "" { bytes += length($0) + 1 }
    END { flush() }
  ' "$document")
}

check_anchored_record_lines() {
  local document="$1"
  local anchor_prefix="$2"

  while IFS=$'\t' read -r line_number record_lines anchor_id; do
    [[ -z "$line_number" ]] && continue
    echo "${document}:${line_number}: ${anchor_id} spans ${record_lines} lines; split the record before the 80-line hard ceiling" >&2
    failed=true
  done < <(awk -v prefix="$anchor_prefix" '
    function flush() {
      if (anchor != "" && lines > 80) print start "\t" lines "\t" anchor
    }
    $0 ~ "^<a id=\"" prefix {
      flush()
      anchor = $0
      sub(/^<a id="/, "", anchor)
      sub(/"><\/a>$/, "", anchor)
      start = NR
      lines = 0
    }
    anchor != "" { lines += 1 }
    END { flush() }
  ' "$document")
}

for document in docs/implementation/*.md; do
  check_anchored_record_size "$document" "cap-" 24000
  check_anchored_record_lines "$document" "cap-"
done

for document in docs/sources/*.md; do
  check_anchored_record_size "$document" "src-" 24000
  check_anchored_record_lines "$document" "src-"
done

while IFS=$'\t' read -r line_number record_size heading; do
  [[ -z "$line_number" ]] && continue
  echo "docs/SEMANTICS-GAPS.md:${line_number}: ${heading} has ${record_size} bytes; split the open obligation before the 12000-byte hard ceiling" >&2
  failed=true
done < <(awk '
  function flush() {
    if (heading != "" && bytes > 12000) print start "\t" bytes "\t" heading
  }
  /^### SG[0-9]+ / {
    flush()
    heading = $0
    start = NR
    bytes = 0
  }
  heading != "" { bytes += length($0) + 1 }
  END { flush() }
' docs/SEMANTICS-GAPS.md)

while IFS=$'\t' read -r line_number record_lines heading; do
  [[ -z "$line_number" ]] && continue
  echo "docs/SEMANTICS-GAPS.md:${line_number}: ${heading} spans ${record_lines} lines; split the open obligation before the 80-line hard ceiling" >&2
  failed=true
done < <(awk '
  function flush() {
    if (heading != "" && lines > 80) print start "\t" lines "\t" heading
  }
  /^### SG[0-9]+ / {
    flush()
    heading = $0
    start = NR
    lines = 0
  }
  heading != "" { lines += 1 }
  END { flush() }
' docs/SEMANTICS-GAPS.md)

if grep -Fq '| Capability | Exists | Owner | Assurance | Remains |' docs/implementation/*.md; then
  echo "docs/implementation/: capability tables are not allowed; use one anchored keyed record per capability" >&2
  failed=true
fi

while IFS=: read -r file line_number _; do
  [[ -z "$file" ]] && continue
  echo "${file}:${line_number}: a source-checkpoint link must target a specific src- anchor; label an intentional hub link as source registry" >&2
  failed=true
done < <(grep -HnF '[source checkpoint](../SOURCES.md)' docs/implementation/*.md || true)

for prefix in cap src; do
  if [[ "$prefix" == cap ]]; then
    hub="docs/IMPLEMENTATION-MAP.md"
    shards=(docs/implementation/*.md)
  else
    hub="docs/SOURCES.md"
    shards=(docs/sources/*.md)
  fi

  while IFS= read -r duplicate; do
    [[ -z "$duplicate" ]] && continue
    echo "${hub}: duplicate ${prefix}-anchor ${duplicate}" >&2
    failed=true
  done < <(grep -h "^<a id=\"${prefix}-" "$hub" | sort | uniq -d)

  while IFS= read -r duplicate; do
    [[ -z "$duplicate" ]] && continue
    echo "${shards[0]%/*}/: duplicate detailed ${prefix}-anchor ${duplicate}" >&2
    failed=true
  done < <(grep -h "^<a id=\"${prefix}-" "${shards[@]}" | sort | uniq -d)

  while IFS= read -r anchor; do
    [[ -z "$anchor" ]] && continue
    if ! grep -Fqx "$anchor" "$hub"; then
      echo "${hub}: missing compatibility entry for ${anchor}" >&2
      failed=true
      continue
    fi
    anchor_id="${anchor#*id=\"}"
    anchor_id="${anchor_id%\"*}"
    if ! grep -Fq "#${anchor_id})" "$hub"; then
      echo "${hub}: compatibility entry ${anchor_id} does not link to its detailed shard record" >&2
      failed=true
    fi
  done < <(grep -h "^<a id=\"${prefix}-" "${shards[@]}" | sort -u)
done

while IFS=: read -r line_number _; do
  [[ -z "$line_number" ]] && continue
  echo "docs/SEMANTICS-GAPS.md:${line_number}: completed or correction chronology does not belong in the open-only gap owner" >&2
  failed=true
done < <(grep -Ein '^- (\*\*)?(closed|resolved|corrected|partly resolved|upstream reconciliation closed)(\*\*)?([ :,.]|$)' docs/SEMANTICS-GAPS.md || true)

# Revision citations newly written in this range must resolve. A citation is "new" only when it
# does not already appear in the tree at the range's start, so moving or re-quoting a record does
# not re-flag its existing receipts; peer history is rewritten upstream and 176 of the 426 existing
# citations resolve nowhere, which is honest history rather than a defect (see docs/SOURCES.md).
# Retires LF138: a fabricated receipt reads exactly like a measured one.
revision_range="${A12_REVISION_RANGE:-HEAD~1..HEAD}"
range_base="${revision_range%%..*}"
if git rev-parse --verify --quiet "$range_base" >/dev/null; then
  hex_of() { grep -hoE '(^|[^0-9a-f])[0-9a-f]{40}([^0-9a-f]|$)' | grep -oE '[0-9a-f]{40}' | sort -u; }
  added_citations="$(git diff "$revision_range" -- docs/ spec/ | grep '^+' | hex_of || true)"
  existing_citations="$(git grep -hI -e '' "$range_base" -- docs/ spec/ 2>/dev/null | hex_of || true)"
  new_citations="$(comm -23 <(printf '%s\n' "$added_citations") <(printf '%s\n' "$existing_citations"))"
  siblings_present=true
  for sibling in ../a12-rulekit ../a12-kernel; do
    git -C "$sibling" rev-parse --git-dir >/dev/null 2>&1 || siblings_present=false
  done
  for citation in $new_citations; do
    if git cat-file -t "$citation" >/dev/null 2>&1 \
      || git -C ../a12-rulekit cat-file -t "$citation" >/dev/null 2>&1 \
      || git -C ../a12-kernel cat-file -t "$citation" >/dev/null 2>&1; then
      continue
    fi
    if [[ "$siblings_present" == true ]]; then
      echo "new revision citation ${citation} resolves in no checkout; cite the revision you read, never an extension of a short form [LF138]" >&2
      failed=true
    else
      echo "documentation hygiene guard: citation ${citation} UNVERIFIABLE, a sibling checkout is absent; re-run where ../a12-rulekit and ../a12-kernel are present" >&2
    fi
  done
fi

if [[ "$failed" == true ]]; then
  exit 1
fi

echo "documentation hygiene guard passed: bounded operational claims, open-only gaps, and provenance ownership"
