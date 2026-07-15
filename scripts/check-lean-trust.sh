#!/usr/bin/env bash
set -euo pipefail

for required_tool in find grep lake sed sort; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    echo "trusted theorem audit requires ${required_tool}" >&2
    exit 1
  fi
done

checked_grep() {
  local status
  if grep "$@"; then
    return 0
  else
    status=$?
  fi
  if (( status == 1 )); then
    return 1
  fi
  echo "trusted theorem audit grep failed with status ${status}" >&2
  exit "$status"
}

proof_files=""
if ! proof_files="$(find A12Kernel/Proofs -type f -name '*.lean' -print | sort)"; then
  echo "failed to enumerate trusted proof modules" >&2
  exit 1
fi
if [[ -z "$proof_files" ]]; then
  echo "trusted proof module inventory is empty" >&2
  exit 1
fi

missing_import=false
while IFS= read -r proof_file; do
  proof_module="${proof_file%.lean}"
  proof_module="${proof_module//\//.}"
  if ! checked_grep -Fqx -- "import ${proof_module}" A12Kernel/Proofs.lean; then
    echo "trusted theorem root does not import ${proof_module}" >&2
    missing_import=true
  fi
done <<< "$proof_files"

if [[ "$missing_import" == true ]]; then
  exit 1
fi

project_root="$(pwd -P)"

collect_project_source_closure() {
  local queue=("$@")
  local seen=()
  local index=0
  local source_dependency
  local source_dependencies
  local relative_dependency
  local seen_source
  local already_seen

  while (( index < ${#queue[@]} )); do
    local source="${queue[$index]}"
    index=$((index + 1))
    already_seen=false
    if (( ${#seen[@]} > 0 )); then
      for seen_source in "${seen[@]}"; do
        if [[ "$seen_source" == "$source" ]]; then
          already_seen=true
          break
        fi
      done
    fi
    if [[ "$already_seen" == true ]]; then
      continue
    fi
    seen+=("$source")
    if ! source_dependencies="$(lake env lean --src-deps "$source")"; then
      echo "failed to collect Lean source dependencies for ${source}" >&2
      return 1
    fi
    if [[ -z "$source_dependencies" ]]; then
      echo "Lean reported no source dependencies for ${source}" >&2
      return 1
    fi
    while IFS= read -r source_dependency; do
      case "$source_dependency" in
        "$project_root"/*.lean)
          relative_dependency="${source_dependency#"$project_root"/}"
          queue+=("$relative_dependency")
          ;;
      esac
    done <<< "$source_dependencies"
  done

  printf '%s\n' "${seen[@]}"
}

trusted_source_closure=""
if ! trusted_source_closure="$(collect_project_source_closure \
    A12Kernel.lean A12Kernel/Proofs.lean A12Kernel/Conformance.lean)"; then
  echo "failed to collect the trusted Lean source closure" >&2
  exit 1
fi
while IFS= read -r trusted_source; do
  case "$trusted_source" in
    A12Kernel/Qualification/*|A12Kernel/Differential/*|A12Kernel/Process/*|A12Kernel/EvidenceMain.lean|A12Kernel/ReferenceMain.lean|A12Kernel/ReferenceProcessTestMain.lean|A12Kernel/CandidateConformanceMain.lean|A12Kernel/FlatHandoverMain.lean|A12Kernel/MutationQualificationMain.lean|A12Kernel/GeneratedDifferentialMain.lean|A12Kernel/ProcessTestMain.lean)
      echo "trusted Lean roots transitively reach IO or qualification driver ${trusted_source}" >&2
      exit 1
      ;;
  esac
done <<< "$trusted_source_closure"

theorem_sources="${proof_files}"$'\n'A12Kernel/Proofs.lean
theorem_names=""
while IFS= read -r proof_source; do
  source_theorem_names=""
  if ! source_theorem_names="$(sed -nE \
      's/^[[:space:]]*(protected[[:space:]]+)?theorem ([A-Za-z0-9_]+).*/\2/p' \
      "$proof_source")"; then
    echo "failed to inspect theorem declarations in ${proof_source}" >&2
    exit 1
  fi
  if [[ -n "$source_theorem_names" ]]; then
    theorem_names+="${source_theorem_names}"$'\n'
  fi
done <<< "$theorem_sources"
theorem_names="${theorem_names%$'\n'}"
if [[ -z "$theorem_names" ]]; then
  echo "trusted theorem inventory is empty" >&2
  exit 1
fi

missing_theorem=false
while IFS= read -r theorem_name; do
  if ! checked_grep -Eq -- \
      "^#print axioms [A-Za-z0-9_.]+\\.${theorem_name}$" A12Kernel/TrustAudit.lean; then
    echo "trust audit does not cover theorem ${theorem_name}" >&2
    missing_theorem=true
  fi
done <<< "$theorem_names"

if [[ "$missing_theorem" == true ]]; then
  exit 1
fi

trusted_scan_files=(
  A12Kernel/Basic.lean
  A12Kernel/Core.lean
  A12Kernel/Cell.lean
  A12Kernel/Document.lean
  A12Kernel/Proofs.lean
)
trusted_semantics_files=""
if ! trusted_semantics_files="$(find A12Kernel/Elaboration A12Kernel/Semantics \
    -type f -name '*.lean' -print | sort)"; then
  echo "failed to enumerate trusted elaboration and semantics modules" >&2
  exit 1
fi
if [[ -n "$trusted_semantics_files" ]]; then
  while IFS= read -r trusted_source; do
    trusted_scan_files+=("$trusted_source")
  done <<< "$trusted_semantics_files"
fi
while IFS= read -r proof_file; do
  trusted_scan_files+=("$proof_file")
done <<< "$proof_files"

if checked_grep -En -- \
    '(^|[^[:alnum:]_])(sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool|Lean\.trustCompiler)([^[:alnum:]_]|$)|^[[:space:]]*(private[[:space:]]+)?(axiom|unsafe|partial)([[:space:]]|$)' \
    "${trusted_scan_files[@]}"; then
  echo "trusted Lean proof sources contain a banned trust mechanism" >&2
  exit 1
fi

audit=""
if ! audit="$(lake env lean A12Kernel/TrustAudit.lean 2>&1)"; then
  printf '%s\n' "$audit" >&2
  echo "failed to elaborate the trusted theorem audit" >&2
  exit 1
fi
printf '%s\n' "$audit"

if [[ "$audit" == *sorryAx* ]]; then
  echo "trusted Lean theorem roots depend on sorryAx" >&2
  exit 1
fi

unexpected_axioms=false
while IFS= read -r axiom_line; do
  case "$axiom_line" in
    *"depends on axioms:"*) ;;
    *) continue ;;
  esac
  axiom_list="${axiom_line##*\[}"
  axiom_list="${axiom_list%\]}"
  IFS=',' read -r -a axiom_items <<< "$axiom_list"
  for axiom_name in "${axiom_items[@]}"; do
    axiom_name="${axiom_name#"${axiom_name%%[![:space:]]*}"}"
    axiom_name="${axiom_name%"${axiom_name##*[![:space:]]}"}"
    case "$axiom_name" in
      propext|Classical.choice|Quot.sound) ;;
      *)
        echo "$axiom_line" >&2
        unexpected_axioms=true
        ;;
    esac
  done
done <<< "$audit"

if [[ "$unexpected_axioms" == true ]]; then
  echo "trusted Lean theorem roots depend on non-standard axioms" >&2
  exit 1
fi
