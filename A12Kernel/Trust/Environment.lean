import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.Command
import Lean.Util.CollectAxioms

namespace A12Kernel.Trust

open Lean Lean.Elab Lean.Elab.Command

private def isAllowedLogicalAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

private def isGeneratedTotalRecursor (env : Environment) (info : ConstantInfo) : Bool :=
  info.name.isStr && info.name.getString! == "_unsafe_rec" &&
    match env.find? info.name.getPrefix with
    | some (.defnInfo parent) => parent.safety == .safe && info.type == parent.type
    | _ => false

/--
Audit an elaborated declaration rather than guessing its meaning from source spelling.
The one admitted partial constant shape is Lean's compiler-generated `_unsafe_rec`
helper with the same type as a kernel-visible safe total definition; source `partial`
wrappers are opaque and therefore rejected independently.
-/
def auditConstant (env : Environment) (info : ConstantInfo) : CommandElabM Unit := do
  match info with
  | .axiomInfo _ =>
      throwError "environment trust audit rejects project axiom {info.name}"
  | .opaqueInfo _ =>
      throwError "environment trust audit rejects unclassified opaque declaration {info.name}"
  | _ => pure ()

  if info.isUnsafe then
    throwError "environment trust audit rejects unsafe declaration {info.name}"

  if info.isPartial && !isGeneratedTotalRecursor env info then
    throwError "environment trust audit rejects partial declaration {info.name}"

  if let some implementation := Lean.Compiler.getImplementedBy? env info.name then
    throwError "environment trust audit rejects implemented_by substitution {info.name} -> {implementation}"

  if (Lean.getExternAttrData? env info.name).isSome then
    throwError "environment trust audit rejects extern declaration {info.name}"

  for axiomName in (← Lean.collectAxioms info.name) do
    unless isAllowedLogicalAxiom axiomName do
      throwError "environment trust audit rejects dependency of {info.name} on axiom {axiomName}"

/-- Audit every declaration owned by imported modules selected by `acceptModule`. -/
def auditImportedModules (acceptModule : Name → Bool) : CommandElabM (Nat × Nat) := do
  let env ← getEnv
  let mut moduleCount := 0
  let mut declarationCount := 0
  for (moduleName, moduleData) in env.header.moduleNames.zip env.header.moduleData do
    if acceptModule moduleName then
      moduleCount := moduleCount + 1
      for info in moduleData.constants do
        auditConstant env info
        declarationCount := declarationCount + 1
  if moduleCount == 0 then
    throwError "environment trust audit selected no project modules"
  if declarationCount == 0 then
    throwError "environment trust audit selected no project declarations"
  pure (moduleCount, declarationCount)

/-- Audit exact names in the current environment; used by adversarial guard probes. -/
def auditNames (names : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for name in names do
    match env.find? name with
    | none => throwError "environment trust audit cannot find probe declaration {name}"
    | some info => auditConstant env info

end A12Kernel.Trust
