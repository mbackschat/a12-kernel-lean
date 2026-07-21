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

collect_project_source_closure() {
  local queue=("$@")
  local seen_sources=""
  local seen_index=$'\n'
  local index=0
  local line
  local module_name
  local relative_dependency

  while (( index < ${#queue[@]} )); do
    local source="${queue[$index]}"
    index=$((index + 1))
    case "$seen_index" in
      *$'\n'"$source"$'\n'*) continue ;;
    esac
    seen_sources+="${source}"$'\n'
    seen_index+="${source}"$'\n'
    while IFS= read -r line; do
      if [[ "$line" =~ ^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+([A-Za-z_][A-Za-z0-9_.]*)[[:space:]]*$ ]]; then
        module_name="${BASH_REMATCH[2]}"
        case "$module_name" in
          A12Kernel)
            relative_dependency="A12Kernel.lean"
            ;;
          A12Kernel.*)
            relative_dependency="${module_name//./\/}.lean"
            ;;
          *)
            continue
            ;;
        esac
        if [[ ! -f "$relative_dependency" ]]; then
          echo "project import ${module_name} from ${source} has no source file ${relative_dependency}" >&2
          return 1
        fi
        queue+=("$relative_dependency")
      elif [[ "$line" =~ ^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+ ]]; then
        echo "trusted source uses a noncanonical import declaration: ${source}: ${line}" >&2
        return 1
      fi
    done < "$source"
  done

  printf '%s' "$seen_sources"
}

source_zone() {
  case "$1" in
    A12Kernel.lean)
      printf '%s\n' "library-root"
      ;;
    A12Kernel/Basic.lean|A12Kernel/Core.lean|A12Kernel/Cell.lean|A12Kernel/Document.lean|A12Kernel/Semantics/*|A12Kernel/Elaboration/*|A12Kernel/Proofs.lean|A12Kernel/Proofs/*)
      printf '%s\n' "logical"
      ;;
    A12Kernel/Conformance.lean|A12Kernel/Conformance/*)
      printf '%s\n' "conformance"
      ;;
    A12Kernel/Evidence/*)
      printf '%s\n' "evidence"
      ;;
    A12Kernel/Reference/*)
      printf '%s\n' "reference"
      ;;
    A12Kernel/Process/*)
      printf '%s\n' "process"
      ;;
    A12Kernel/Trust/*|A12Kernel/TrustAudit.lean)
      printf '%s\n' "trust-driver"
      ;;
    A12Kernel/EvidenceMain.lean|A12Kernel/ReferenceMain.lean|A12Kernel/ReferenceProcessTestMain.lean|A12Kernel/CandidateConformanceMain.lean|A12Kernel/ProcessTestMain.lean)
      printf '%s\n' "io-driver"
      ;;
    *)
      return 1
      ;;
  esac
}

expect_source_zone() {
  local source="$1"
  local expected="$2"
  local actual
  if ! actual="$(source_zone "$source")"; then
    echo "trusted source-zone classifier rejects ${expected} source ${source}" >&2
    exit 1
  fi
  if [[ "$actual" != "$expected" ]]; then
    echo "trusted source-zone classifier assigns ${source} to ${actual}, expected ${expected}" >&2
    exit 1
  fi
}

expect_unclassified_source() {
  local source="$1"
  local actual
  if actual="$(source_zone "$source")"; then
    echo "trusted source-zone classifier admits retired or unknown source ${source} as ${actual}" >&2
    exit 1
  fi
}

expect_source_zone A12Kernel.lean library-root
expect_source_zone A12Kernel/Basic.lean logical
expect_source_zone A12Kernel/Semantics/Future.lean logical
expect_source_zone A12Kernel/Elaboration/Future.lean logical
expect_source_zone A12Kernel/Proofs/Future.lean logical
expect_source_zone A12Kernel/Conformance/Future.lean conformance
expect_source_zone A12Kernel/Evidence/Future.lean evidence
expect_source_zone A12Kernel/Reference/Future.lean reference
expect_source_zone A12Kernel/Process/Future.lean process
expect_source_zone A12Kernel/Trust/Future.lean trust-driver
expect_source_zone A12Kernel/EvidenceMain.lean io-driver

expect_unclassified_source A12Kernel/Future/Unexpected.lean

project_source_files="A12Kernel.lean"
enumerated_project_sources=""
if ! enumerated_project_sources="$(find A12Kernel -type f -name '*.lean' -print | sort)"; then
  echo "failed to enumerate project Lean sources" >&2
  exit 1
fi
if [[ -n "$enumerated_project_sources" ]]; then
  project_source_files+=$'\n'"${enumerated_project_sources}"
fi
while IFS= read -r project_source; do
  if ! source_zone "$project_source" >/dev/null; then
    echo "project Lean source has no explicit trust zone: ${project_source}" >&2
    exit 1
  fi
done <<< "$project_source_files"

logical_source_closure=""
if ! logical_source_closure="$(collect_project_source_closure \
    A12Kernel/Basic.lean A12Kernel/Proofs.lean)"; then
  echo "failed to collect the trusted logical source closure" >&2
  exit 1
fi
while IFS= read -r logical_source; do
  if [[ "$(source_zone "$logical_source")" != "logical" ]]; then
    echo "trusted logical roots transitively reach nonlogical source ${logical_source}" >&2
    exit 1
  fi
done <<< "$logical_source_closure"

conformance_source_closure=""
if ! conformance_source_closure="$(collect_project_source_closure A12Kernel/Conformance.lean)"; then
  echo "failed to collect the executable conformance source closure" >&2
  exit 1
fi
while IFS= read -r conformance_source; do
  conformance_zone="$(source_zone "$conformance_source")"
  if [[ "$conformance_zone" != "logical" && "$conformance_zone" != "conformance" ]]; then
    echo "executable conformance root transitively reaches disallowed source ${conformance_source}" >&2
    exit 1
  fi
done <<< "$conformance_source_closure"

library_source_closure=""
if ! library_source_closure="$(collect_project_source_closure A12Kernel.lean)"; then
  echo "failed to collect the library source closure" >&2
  exit 1
fi
while IFS= read -r library_source; do
  library_zone="$(source_zone "$library_source")"
  if [[ "$library_zone" != "library-root" && "$library_zone" != "logical" &&
      "$library_zone" != "conformance" ]]; then
    echo "library root transitively reaches disallowed source ${library_source}" >&2
    exit 1
  fi
done <<< "$library_source_closure"

theorem_source_files=()
while IFS= read -r proof_source; do
  theorem_source_files+=("$proof_source")
done <<< "$proof_files"
theorem_source_files+=(A12Kernel/Proofs.lean)

theorem_names=""
if ! theorem_names="$(sed -nE \
    "s/^[[:space:]]*(@\\[[^]]+\\][[:space:]]*)*((protected|public|noncomputable|meta)[[:space:]]+)*theorem[[:space:]]+([A-Za-z0-9_']+).*/\\4/p" \
    "${theorem_source_files[@]}")"; then
  echo "failed to inspect trusted theorem declarations" >&2
  exit 1
fi
if [[ -z "$theorem_names" ]]; then
  echo "trusted theorem inventory is empty" >&2
  exit 1
fi

sorted_theorem_names=""
if ! sorted_theorem_names="$(printf '%s\n' "$theorem_names" | sort)"; then
  echo "failed to sort the trusted theorem inventory" >&2
  exit 1
fi
previous_theorem_name=""
theorem_count=0
while IFS= read -r theorem_name; do
  theorem_count=$((theorem_count + 1))
  if [[ -n "$previous_theorem_name" && "$theorem_name" == "$previous_theorem_name" ]]; then
    echo "trusted theorem basename is ambiguous across namespaces: ${theorem_name}" >&2
    exit 1
  fi
  previous_theorem_name="$theorem_name"
done <<< "$sorted_theorem_names"

registered_theorem_names=""
if ! registered_theorem_names="$(sed -nE \
    "s/^#print axioms [A-Za-z0-9_.']+\\.([A-Za-z0-9_']+)$/\\1/p" \
    A12Kernel/TrustAudit.lean | sort)"; then
  echo "failed to inspect the human-readable theorem audit registry" >&2
  exit 1
fi

if [[ "$registered_theorem_names" != "$sorted_theorem_names" ]]; then
  echo "trust audit theorem registry differs from the trusted theorem inventory" >&2
  while IFS= read -r theorem_name; do
    if ! checked_grep -Fqx -- "$theorem_name" <<< "$registered_theorem_names"; then
      echo "trust audit does not cover theorem ${theorem_name}" >&2
    fi
  done <<< "$sorted_theorem_names"
  while IFS= read -r theorem_name; do
    if ! checked_grep -Fqx -- "$theorem_name" <<< "$sorted_theorem_names"; then
      echo "trust audit registers unknown theorem basename ${theorem_name}" >&2
    fi
  done <<< "$registered_theorem_names"
  exit 1
fi

trusted_scan_files=(A12Kernel.lean)
while IFS= read -r trusted_source; do
  trusted_scan_files+=("$trusted_source")
done <<< "$logical_source_closure"

banned_trust_pattern='(^|[^[:alnum:]_])(sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool|Lean\.trustCompiler)([^[:alnum:]_]|$)|^[[:space:]]*(@\[[^]]+\][[:space:]]*)*((private|protected|public|noncomputable|meta)[[:space:]]+)*(axiom|unsafe|partial)([[:space:]]|$)'

if checked_grep -En -- "$banned_trust_pattern" \
    "${trusted_scan_files[@]}"; then
  echo "trusted Lean proof sources contain a banned trust mechanism" >&2
  exit 1
fi

if ! lake build A12Kernel A12Kernel.Trust.Environment >/dev/null; then
  echo "failed to refresh the elaborated environment under audit" >&2
  exit 1
fi

adversarial_probe_output=""
if ! adversarial_probe_output="$(lake env lean A12Kernel/Trust/Adversarial.lean 2>&1)"; then
  printf '%s\n' "$adversarial_probe_output" >&2
  echo "environment trust adversarial probes failed" >&2
  exit 1
fi

audit=""
if ! audit="$(lake env lean A12Kernel/TrustAudit.lean 2>&1)"; then
  printf '%s\n' "$audit" >&2
  echo "failed to elaborate the trusted theorem audit" >&2
  exit 1
fi

environment_summary="$(sed -nE \
    '/^environment trust audit passed: [1-9][0-9]* declarations in [1-9][0-9]* modules$/p' \
    <<< "$audit")"
if [[ ! "$environment_summary" =~ ^environment[[:space:]]trust[[:space:]]audit[[:space:]]passed:[[:space:]]([1-9][0-9]*)[[:space:]]declarations[[:space:]]in[[:space:]]([1-9][0-9]*)[[:space:]]modules$ ]]; then
  printf '%s\n' "$audit" >&2
  echo "trusted environment audit did not report a non-empty project inventory" >&2
  exit 1
fi
declaration_count="${BASH_REMATCH[1]}"
module_count="${BASH_REMATCH[2]}"

if [[ "$audit" == *sorryAx* ]]; then
  printf '%s\n' "$audit" >&2
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
        unexpected_axioms=true
        ;;
    esac
  done
done <<< "$audit"

if [[ "$unexpected_axioms" == true ]]; then
  printf '%s\n' "$audit" >&2
  echo "trusted Lean theorem roots depend on non-standard axioms" >&2
  exit 1
fi

printf 'trusted theorem audit passed: %s theorem roots; %s declarations in %s modules\n' \
  "$theorem_count" "$declaration_count" "$module_count"
