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

theorem_sources="${proof_files}"$'\n'A12Kernel/Proofs.lean
theorem_names=""
while IFS= read -r proof_source; do
  source_theorem_names=""
  if ! source_theorem_names="$(sed -nE \
      's/^[[:space:]]*(@\[[^]]+\][[:space:]]*)*((protected|public|noncomputable|meta)[[:space:]]+)*theorem[[:space:]]+([A-Za-z0-9_]+).*/\4/p' \
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

sorted_theorem_names=""
if ! sorted_theorem_names="$(printf '%s\n' "$theorem_names" | sort)"; then
  echo "failed to sort the trusted theorem inventory" >&2
  exit 1
fi
previous_theorem_name=""
while IFS= read -r theorem_name; do
  if [[ -n "$previous_theorem_name" && "$theorem_name" == "$previous_theorem_name" ]]; then
    echo "trusted theorem basename is ambiguous across namespaces: ${theorem_name}" >&2
    exit 1
  fi
  previous_theorem_name="$theorem_name"
done <<< "$sorted_theorem_names"

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

if ! lake build A12Kernel.Trust.Environment >/dev/null; then
  echo "failed to build the elaborated-environment trust audit" >&2
  exit 1
fi

expect_environment_rejection() {
  local label="$1"
  local expected="$2"
  local source="$3"
  local output
  if output="$(printf '%s\n' "$source" | lake env lean --stdin 2>&1)"; then
    echo "environment trust probe unexpectedly passed: ${label}" >&2
    exit 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    printf '%s\n' "$output" >&2
    echo "environment trust probe failed for the wrong reason: ${label}" >&2
    exit 1
  fi
}

expect_environment_acceptance() {
  local label="$1"
  local source="$2"
  local output
  if ! output="$(printf '%s\n' "$source" | lake env lean --stdin 2>&1)"; then
    printf '%s\n' "$output" >&2
    echo "environment trust control unexpectedly failed: ${label}" >&2
    exit 1
  fi
}

expect_environment_rejection "attributed public axiom" \
  "project axiom TrustFixture.hidden" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\n@[simp] public axiom hidden : True\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "macro-generated axiom" \
  "project axiom TrustFixture.hidden" \
  $'import A12Kernel.Trust.Environment\nsyntax "constant " ident " : " term : command\nmacro_rules\n  | `(constant $name:ident : $type:term) => `(axiom $name : $type)\nnamespace TrustFixture\nconstant hidden : True\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "public unsafe definition" \
  "unsafe declaration TrustFixture.hidden" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\npublic unsafe def hidden : Nat := 0\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "attributed partial definition" \
  "unclassified opaque declaration TrustFixture.hidden" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\n@[inline] public partial def hidden (n : Nat) : Nat := hidden n\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "late implemented_by substitution" \
  "implemented_by substitution TrustFixture.target -> FixtureSupport.impl" \
  $'import A12Kernel.Trust.Environment\nnamespace FixtureSupport\nunsafe def impl (n : Nat) : Nat := n + 1\nend FixtureSupport\nnamespace TrustFixture\ndef target (n : Nat) : Nat := n\nend TrustFixture\nattribute [implemented_by FixtureSupport.impl] TrustFixture.target\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.target]'

expect_environment_rejection "late extern declaration" \
  "extern declaration TrustFixture.target" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\ndef target (n : Nat) : Nat := n\nend TrustFixture\nattribute [extern "a12_trust_probe"] TrustFixture.target\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.target]'

expect_environment_rejection "sorry dependency" \
  "on axiom sorryAx" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\ntheorem hidden : True := by sorry\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "native_decide dependency" \
  "on axiom TrustFixture.hidden._native.native_decide" \
  $'import A12Kernel.Trust.Environment\nimport Std.Tactic\nnamespace TrustFixture\ntheorem hidden : (List.range 4).length = 4 := by native_decide\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "bodyless opaque declaration" \
  "unclassified opaque declaration TrustFixture.hidden" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\nopaque hidden : Nat\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.hidden]'

expect_environment_rejection "empty imported-module selection" \
  "environment trust audit selected no project modules" \
  $'import A12Kernel.Trust.Environment\nopen Lean Elab Command\nrun_cmd discard <| A12Kernel.Trust.auditImportedModules (fun _ => false)'

expect_environment_rejection "generated recursor with unsafe parent" \
  "partial declaration TrustFixture.parent._unsafe_rec" \
  $'import A12Kernel\nimport A12Kernel.Trust.Environment\nnamespace TrustFixture\nunsafe def parent : Nat := 0\nend TrustFixture\nopen Lean Lean.Elab Lean.Elab.Command\nrun_cmd do\n  let env ← getEnv\n  let some (.defnInfo template) := env.find? `A12Kernel.FlatCondition.evalSelected._unsafe_rec\n    | throwError "missing partial helper template"\n  let name := `TrustFixture.parent._unsafe_rec\n  liftCoreM <| Lean.addDecl (.defnDecl {\n    name := name\n    levelParams := []\n    type := mkConst ``Nat\n    value := mkNatLit 0\n    hints := .regular 0\n    safety := template.safety\n    all := [name]\n  })\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.parent._unsafe_rec]'

expect_environment_rejection "generated recursor with mismatched parent type" \
  "partial declaration TrustFixture.parent._unsafe_rec" \
  $'import A12Kernel\nimport A12Kernel.Trust.Environment\nnamespace TrustFixture\ndef parent : String := ""\nend TrustFixture\nopen Lean Lean.Elab Lean.Elab.Command\nrun_cmd do\n  let env ← getEnv\n  let some (.defnInfo template) := env.find? `A12Kernel.FlatCondition.evalSelected._unsafe_rec\n    | throwError "missing partial helper template"\n  let name := `TrustFixture.parent._unsafe_rec\n  liftCoreM <| Lean.addDecl (.defnDecl {\n    name := name\n    levelParams := []\n    type := mkConst ``Nat\n    value := mkNatLit 0\n    hints := .regular 0\n    safety := template.safety\n    all := [name]\n  })\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.parent._unsafe_rec]'

expect_environment_acceptance "ordinary attributed definitions and allowed logical axioms" \
  $'import A12Kernel.Trust.Environment\nnamespace TrustFixture\n@[inline] def target : String := "axiom extern implemented_by unsafe partial sorry"\nnoncomputable def chosen : True := Classical.choice (show Nonempty True from ⟨True.intro⟩)\nend TrustFixture\nopen Lean Elab Command\nrun_cmd A12Kernel.Trust.auditNames #[`TrustFixture.target, `TrustFixture.chosen]'

audit=""
if ! audit="$(lake env lean A12Kernel/TrustAudit.lean 2>&1)"; then
  printf '%s\n' "$audit" >&2
  echo "failed to elaborate the trusted theorem audit" >&2
  exit 1
fi
printf '%s\n' "$audit"

if ! checked_grep -Eq \
    '^environment trust audit passed: [1-9][0-9]* declarations in [1-9][0-9]* modules$' \
    <<< "$audit"; then
  echo "trusted environment audit did not report a non-empty project inventory" >&2
  exit 1
fi

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
