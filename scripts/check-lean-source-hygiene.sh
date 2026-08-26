#!/usr/bin/env bash
set -euo pipefail

for required_tool in awk git; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    echo "Lean source-hygiene guard requires ${required_tool}" >&2
    exit 1
  fi
done

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"

if [[ "$(git rev-parse --is-inside-work-tree 2>/dev/null)" != "true" ]]; then
  echo "Lean source-hygiene guard must run inside a Git worktree" >&2
  exit 1
fi

review_threshold=800
ordinary_ceiling=1200
exception_document="docs/TESTING.md"
exceptional_registry="A12Kernel/TrustAudit.lean"

if [[ ! -f "$exception_document" ]]; then
  echo "Lean source-hygiene exception owner is missing: ${exception_document}" >&2
  exit 1
fi

trim() {
  local value="$1"
  value="${value#"${value%%[![:space:]]*}"}"
  value="${value%"${value##*[![:space:]]}"}"
  printf '%s' "$value"
}

is_generated_or_build_output() {
  case "$1" in
    .lake/*|*/.lake/*|build/*|*/build/*|.build/*|*/.build/*|out/*|*/out/*)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

tracked_files=()
tracked_index=$'\n'
while IFS= read -r -d '' source; do
  if is_generated_or_build_output "$source"; then
    continue
  fi
  tracked_files+=("$source")
  tracked_index+="${source}"$'\n'
done < <(git ls-files -z -- '*.lean')

if (( ${#tracked_files[@]} == 0 )); then
  echo "Lean source-hygiene guard found no tracked Lean files" >&2
  exit 1
fi

is_tracked_lean_source() {
  case "$tracked_index" in
    *$'\n'"$1"$'\n'*) return 0 ;;
    *) return 1 ;;
  esac
}

exception_records=""
exception_paths=$'\n'
exception_count=0
inside_exception_map=false
start_marker_count=0
end_marker_count=0

while IFS= read -r line || [[ -n "$line" ]]; do
  case "$line" in
    '<!-- lean-source-hygiene-exceptions:start -->')
      start_marker_count=$((start_marker_count + 1))
      inside_exception_map=true
      continue
      ;;
    '<!-- lean-source-hygiene-exceptions:end -->')
      end_marker_count=$((end_marker_count + 1))
      inside_exception_map=false
      continue
      ;;
  esac

  if [[ "$line" == *"lean-source-hygiene-exception:"* ]]; then
    if [[ "$inside_exception_map" != true ]]; then
      echo "${exception_document}: source-hygiene exception entry appears outside its marked map" >&2
      exit 1
    fi
    if [[ ! "$line" =~ ^\<\!--[[:space:]]lean-source-hygiene-exception:[[:space:]]([^|]+)\|([^|]+)\|(.*)[[:space:]]--\>[[:space:]]*$ ]]; then
      echo "${exception_document}: malformed source-hygiene exception entry: ${line}" >&2
      exit 1
    fi
    path="$(trim "${BASH_REMATCH[1]}")"
    mode="$(trim "${BASH_REMATCH[2]}")"
    rationale="$(trim "${BASH_REMATCH[3]}")"
    if [[ -z "$path" || -z "$mode" || -z "$rationale" ]]; then
      echo "${exception_document}: source-hygiene exception path, mode, and rationale must be nonempty" >&2
      exit 1
    fi
    case "$exception_paths" in
      *$'\n'"$path"$'\n'*)
        echo "duplicate source-hygiene exception path: ${path}" >&2
        exit 1
        ;;
    esac
    case "$mode" in
      review-threshold) ;;
      exceptional-ceiling)
        if [[ "$path" != "$exceptional_registry" ]]; then
          echo "only ${exceptional_registry} may use the exceptional-ceiling mode; found ${path}" >&2
          exit 1
        fi
        ;;
      *)
        echo "${exception_document}: unknown source-hygiene exception mode '${mode}' for ${path}" >&2
        exit 1
        ;;
    esac
    exception_paths+="${path}"$'\n'
    exception_records+="${path}"$'\t'"${mode}"$'\t'"${rationale}"$'\n'
    exception_count=$((exception_count + 1))
  fi
done < "$exception_document"

if (( start_marker_count != 1 || end_marker_count != 1 )); then
  echo "${exception_document}: source-hygiene exception map markers must occur exactly once" >&2
  exit 1
fi

while IFS=$'\t' read -r path mode rationale; do
  [[ -z "$path" ]] && continue
  if ! is_tracked_lean_source "$path"; then
    echo "stale source-hygiene exception path is not a tracked Lean file: ${path}" >&2
    exit 1
  fi
done <<< "$exception_records"

exception_for() {
  local requested="$1"
  local record_path
  local record_mode
  local record_rationale
  while IFS=$'\t' read -r record_path record_mode record_rationale; do
    if [[ "$record_path" == "$requested" ]]; then
      printf '%s\t%s\n' "$record_mode" "$record_rationale"
      return 0
    fi
  done <<< "$exception_records"
  return 1
}

check_umbrella() {
  local source="$1"
  local violation
  if violation="$(awk '
    BEGIN { depth = 0 }
    {
      input = $0
      code = ""
      position = 1
      while (position <= length(input)) {
        pair = substr(input, position, 2)
        if (depth > 0) {
          if (pair == "/-") {
            depth++
            position += 2
          } else if (pair == "-/") {
            depth--
            position += 2
          } else {
            position++
          }
        } else if (pair == "--") {
          break
        } else if (pair == "/-") {
          depth++
          position += 2
        } else {
          code = code substr(input, position, 1)
          position++
        }
      }
      if (code ~ /^[[:space:]]*$/) {
        next
      }
      if (code ~ /^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+[A-Za-z_][A-Za-z0-9_.]*[[:space:]]*$/) {
        next
      }
      print NR
      exit 1
    }
    END {
      if (depth != 0) {
        print NR
        exit 1
      }
    }
  ' "$source")"; then
    return 0
  fi
  echo "${source}:${violation}: umbrella roots may contain only imports, comments, and whitespace" >&2
  return 1
}

check_exceptional_registry() {
  local source="$1"
  local violation
  if violation="$(awk '
    BEGIN {
      depth = 0
      allowedPrivateDef = 0
      printAxioms = 0
      failed = 0
    }
    {
      input = $0
      code = ""
      position = 1
      while (position <= length(input)) {
        pair = substr(input, position, 2)
        if (depth > 0) {
          if (pair == "/-") {
            depth++
            position += 2
          } else if (pair == "-/") {
            depth--
            position += 2
          } else {
            position++
          }
        } else if (pair == "--") {
          break
        } else if (pair == "/-") {
          depth++
          position += 2
        } else {
          code = code substr(input, position, 1)
          position++
        }
      }
      sub(/^[[:space:]]+/, "", code)
      sub(/[[:space:]]+$/, "", code)
      if (code == "") {
        next
      }
      declaration = "^(@\\[[^]]+\\][[:space:]]*)*((private|protected|public|noncomputable|meta|partial|unsafe)[[:space:]]+)*(theorem|lemma|example|structure|inductive|class|instance|abbrev|axiom|opaque|def)([[:space:]]|$)"
      if (code ~ declaration) {
        if (code ~ /^private[[:space:]]+def[[:space:]]+isAuditedLogicalModule([[:space:](]|$)/ && allowedPrivateDef == 0) {
          allowedPrivateDef = 1
        } else {
          failed = 1
          print NR
          exit 1
        }
      }
      if (code ~ /^#print[[:space:]]+axioms[[:space:]]+[A-Za-z0-9_.]+[[:space:]]*$/) {
        printAxioms++
      } else if (code ~ /^#(print|eval|check|reduce|synth|guard)([[:space:]]|$)/) {
        failed = 1
        print NR
        exit 1
      }
    }
    END {
      if (!failed && (depth != 0 || printAxioms == 0)) {
        print NR
        exit 1
      }
    }
  ' "$source")"; then
    return 0
  fi
  echo "${source}:${violation}: exceptional registry contains semantic or fixture declaration" >&2
  return 1
}

umbrella_roots=(
  A12Kernel.lean
  A12Kernel/Proofs.lean
  A12Kernel/Conformance.lean
  A12Kernel/Elaboration/Flat.lean
  A12Kernel/Elaboration/Flat/Condition.lean
  A12Kernel/Elaboration/NumericAggregate.lean
  A12Kernel/Elaboration/NumericComputation.lean
  A12Kernel/Elaboration/NumericValidation.lean
  A12Kernel/Elaboration/ValidationCondition.lean
  A12Kernel/Proofs/NumericValidation.lean
  A12Kernel/Conformance/Elaboration.lean
  A12Kernel/Conformance/GeneratedComputationValidation.lean
  A12Kernel/Conformance/NumericAggregateElaboration.lean
  A12Kernel/Conformance/NumericComputation.lean
  A12Kernel/Conformance/NumericValidation.lean
  A12Kernel/Conformance/ValidationRule.lean
  A12Kernel/Conformance/ValidationRule/OrdinarySupport.lean
  A12Kernel/Reference/Support.lean
)

for umbrella in "${umbrella_roots[@]}"; do
  if is_tracked_lean_source "$umbrella"; then
    check_umbrella "$umbrella"
  fi
done

largest_ordinary=0
largest_ordinary_path=""

for source in "${tracked_files[@]}"; do
  count="$(awk 'NF { count++ } END { print count + 0 }' "$source")"
  exception=""
  if exception="$(exception_for "$source")"; then
    mode="${exception%%$'\t'*}"
  else
    mode=""
  fi

  if [[ "$source" != "$exceptional_registry" && "$count" -gt "$largest_ordinary" ]]; then
    largest_ordinary="$count"
    largest_ordinary_path="$source"
  fi

  if (( count <= review_threshold )); then
    if [[ -n "$mode" ]]; then
      echo "stale source-hygiene exception for ${source}: ${count} nonblank lines no longer exceeds ${review_threshold}" >&2
      exit 1
    fi
    continue
  fi

  if (( count <= ordinary_ceiling )); then
    if [[ "$mode" != "review-threshold" ]]; then
      echo "${source}: ${count} nonblank lines requires an exact reviewed exception above ${review_threshold}; split by semantic ownership or add a reviewed rationale to ${exception_document}" >&2
      exit 1
    fi
    continue
  fi

  if [[ "$source" != "$exceptional_registry" ]]; then
    echo "${source}: ${count} nonblank lines exceeds the ordinary hard ceiling of ${ordinary_ceiling}; split by semantic ownership" >&2
    exit 1
  fi
  if [[ "$mode" != "exceptional-ceiling" ]]; then
    echo "${source}: ${count} nonblank lines requires its exact exceptional-ceiling entry in ${exception_document}" >&2
    exit 1
  fi
  check_exceptional_registry "$source"
done

while IFS=$'\t' read -r path mode rationale; do
  [[ -z "$path" ]] && continue
  count="$(awk 'NF { count++ } END { print count + 0 }' "$path")"
  case "$mode" in
    review-threshold)
      if (( count <= review_threshold || count > ordinary_ceiling )); then
        echo "stale review-threshold exception for ${path}: ${count} nonblank lines is outside $((review_threshold + 1))-${ordinary_ceiling}" >&2
        exit 1
      fi
      ;;
    exceptional-ceiling)
      if (( count <= ordinary_ceiling )); then
        echo "stale exceptional-ceiling exception for ${path}: ${count} nonblank lines no longer exceeds ${ordinary_ceiling}" >&2
        exit 1
      fi
      ;;
  esac
done <<< "$exception_records"

printf 'Lean source hygiene passed: %s tracked files; largest ordinary file %s nonblank lines; %s reviewed exception%s\n' \
  "${#tracked_files[@]}" "$largest_ordinary" "$exception_count" \
  "$([[ "$exception_count" == 1 ]] && printf '' || printf 's')"
