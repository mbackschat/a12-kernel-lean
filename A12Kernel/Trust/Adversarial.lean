import A12Kernel
import A12Kernel.Trust.Environment
import Std.Tactic

/-!
One-process guard suite for the elaborated-environment trust audit. The deliberately
untrusted declarations below remain in this trust-driver source and outside every
logical, conformance, and library root.
-/

open Lean Lean.Elab Lean.Elab.Command

namespace TrustFixture

@[simp] public axiom attributedAxiom : True

syntax "trust_constant " ident " : " term : command

macro_rules
  | `(trust_constant $name:ident : $type:term) => `(axiom $name : $type)

trust_constant macroAxiom : True

public unsafe def unsafeDefinition : Nat := 0

@[inline] public partial def partialDefinition (n : Nat) : Nat := partialDefinition n

unsafe def implementedByImplementation (n : Nat) : Nat := n + 1

def implementedByTarget (n : Nat) : Nat := n

attribute [implemented_by TrustFixture.implementedByImplementation] implementedByTarget

def externTarget (n : Nat) : Nat := n

attribute [extern "a12_trust_probe"] externTarget

theorem sorryTheorem : True := by sorry

theorem nativeTheorem : (List.range 4).length = 4 := by native_decide

opaque bodylessOpaque : Nat

unsafe def unsafeParent : Nat := 0

def mismatchedParent : String := ""

@[inline] def acceptedText : String := "axiom extern implemented_by unsafe partial sorry"

noncomputable def acceptedChoice : True :=
  Classical.choice (show Nonempty True from ⟨True.intro⟩)

end TrustFixture

private def expectRejection
    (label expected : String)
    (action : CommandElabM Unit) : CommandElabM Unit := do
  let failure ← try
    action
    pure none
  catch error =>
    pure (some (← error.toMessageData.toString))
  match failure with
  | none => throwError "environment trust probe unexpectedly passed: {label}"
  | some message =>
      unless message.contains expected do
        throwError "environment trust probe failed for the wrong reason: {label}: {message}"

run_cmd do
  let env ← getEnv
  let some (.defnInfo template) := env.find? `A12Kernel.FlatCondition.evalSelected._unsafe_rec
    | throwError "missing partial helper template"
  for (name, type) in #[
      (`TrustFixture.unsafeParent._unsafe_rec, mkConst ``Nat),
      (`TrustFixture.mismatchedParent._unsafe_rec, mkConst ``Nat)] do
    liftCoreM <| Lean.addDecl (.defnDecl {
      name := name
      levelParams := []
      type := type
      value := mkNatLit 0
      hints := .regular 0
      safety := template.safety
      all := [name]
    })

run_cmd do
  expectRejection "attributed public axiom"
    "project axiom TrustFixture.attributedAxiom"
    (A12Kernel.Trust.auditNames #[`TrustFixture.attributedAxiom])

run_cmd do
  expectRejection "macro-generated axiom"
    "project axiom TrustFixture.macroAxiom"
    (A12Kernel.Trust.auditNames #[`TrustFixture.macroAxiom])

run_cmd do
  expectRejection "public unsafe definition"
    "unsafe declaration TrustFixture.unsafeDefinition"
    (A12Kernel.Trust.auditNames #[`TrustFixture.unsafeDefinition])

run_cmd do
  expectRejection "attributed partial definition"
    "unclassified opaque declaration TrustFixture.partialDefinition"
    (A12Kernel.Trust.auditNames #[`TrustFixture.partialDefinition])

run_cmd do
  expectRejection "late implemented_by substitution"
    "implemented_by substitution TrustFixture.implementedByTarget -> TrustFixture.implementedByImplementation"
    (A12Kernel.Trust.auditNames #[`TrustFixture.implementedByTarget])

run_cmd do
  expectRejection "late extern declaration"
    "extern declaration TrustFixture.externTarget"
    (A12Kernel.Trust.auditNames #[`TrustFixture.externTarget])

run_cmd do
  expectRejection "sorry dependency"
    "on axiom sorryAx"
    (A12Kernel.Trust.auditNames #[`TrustFixture.sorryTheorem])

run_cmd do
  expectRejection "native_decide dependency"
    "on axiom TrustFixture.nativeTheorem._native.native_decide"
    (A12Kernel.Trust.auditNames #[`TrustFixture.nativeTheorem])

run_cmd do
  expectRejection "bodyless opaque declaration"
    "unclassified opaque declaration TrustFixture.bodylessOpaque"
    (A12Kernel.Trust.auditNames #[`TrustFixture.bodylessOpaque])

run_cmd do
  expectRejection "empty imported-module selection"
    "environment trust audit selected no project modules"
    (discard <| A12Kernel.Trust.auditImportedModules (fun _ => false))

run_cmd do
  expectRejection "generated recursor with unsafe parent"
    "partial declaration TrustFixture.unsafeParent._unsafe_rec"
    (A12Kernel.Trust.auditNames #[`TrustFixture.unsafeParent._unsafe_rec])

run_cmd do
  expectRejection "generated recursor with mismatched parent type"
    "partial declaration TrustFixture.mismatchedParent._unsafe_rec"
    (A12Kernel.Trust.auditNames #[`TrustFixture.mismatchedParent._unsafe_rec])

run_cmd do
  A12Kernel.Trust.auditNames #[`TrustFixture.acceptedText, `TrustFixture.acceptedChoice]
