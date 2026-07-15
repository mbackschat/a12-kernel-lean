#!/usr/bin/env bash
set -euo pipefail

missing_import=false
while IFS= read -r proof_file; do
  proof_module="${proof_file%.lean}"
  proof_module="${proof_module//\//.}"
  if ! rg -q "^import ${proof_module}$" A12Kernel/Proofs.lean; then
    echo "trusted theorem root does not import ${proof_module}" >&2
    missing_import=true
  fi
done < <(find A12Kernel/Proofs -type f -name '*.lean' | sort)

if [[ "$missing_import" == true ]]; then
  exit 1
fi

project_root="$(pwd -P)"

collect_project_source_closure() {
  local queue=("$@")
  local seen=()
  local index=0
  local source_dependency
  local relative_dependency

  while (( index < ${#queue[@]} )); do
    local source="${queue[$index]}"
    index=$((index + 1))
    if printf '%s\n' "${seen[@]}" | rg -Fxq "$source"; then
      continue
    fi
    seen+=("$source")
    while IFS= read -r source_dependency; do
      case "$source_dependency" in
        "$project_root"/*.lean)
          relative_dependency="${source_dependency#"$project_root"/}"
          queue+=("$relative_dependency")
          ;;
      esac
    done < <(lake env lean --src-deps "$source")
  done

  printf '%s\n' "${seen[@]}"
}

trusted_source_closure="$(collect_project_source_closure \
  A12Kernel.lean A12Kernel/Proofs.lean A12Kernel/Conformance.lean)"
if printf '%s\n' "$trusted_source_closure" | rg -n \
    'A12Kernel/(Qualification|Process)/|A12Kernel/(EvidenceMain|ReferenceMain|ReferenceProcessTestMain|CandidateConformanceMain|FlatHandoverMain|MutationQualificationMain)\.lean$'; then
  echo "trusted Lean roots transitively reach an IO or qualification driver" >&2
  exit 1
fi

missing_theorem=false
while IFS= read -r theorem_name; do
  if ! rg -q "^#print axioms [A-Za-z0-9_.]+\\.${theorem_name}$" A12Kernel/TrustAudit.lean; then
    echo "trust audit does not cover theorem ${theorem_name}" >&2
    missing_theorem=true
  fi
done < <(rg --no-filename -o --replace '$1' '^[[:space:]]*(?:protected[[:space:]]+)?theorem ([A-Za-z0-9_]+)' \
  A12Kernel/Proofs A12Kernel/Proofs.lean)

if [[ "$missing_theorem" == true ]]; then
  exit 1
fi

if rg -n '\b(sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool|Lean\.trustCompiler)\b|^[[:space:]]*(private[[:space:]]+)?(axiom|unsafe|partial)([[:space:]]|$)' \
    A12Kernel/Basic.lean A12Kernel/Core.lean A12Kernel/Cell.lean A12Kernel/Document.lean \
    A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Proofs A12Kernel/Proofs.lean; then
  echo "trusted Lean proof sources contain a banned trust mechanism" >&2
  exit 1
fi

audit="$(lake env lean A12Kernel/TrustAudit.lean 2>&1)"
printf '%s\n' "$audit"

if printf '%s\n' "$audit" | rg -n 'sorryAx'; then
  echo "trusted Lean theorem roots depend on sorryAx" >&2
  exit 1
fi

unexpected_axioms=false
while IFS= read -r axiom_line; do
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
done < <(printf '%s\n' "$audit" | rg 'depends on axioms:' || true)

if [[ "$unexpected_axioms" == true ]]; then
  echo "trusted Lean theorem roots depend on non-standard axioms" >&2
  exit 1
fi
