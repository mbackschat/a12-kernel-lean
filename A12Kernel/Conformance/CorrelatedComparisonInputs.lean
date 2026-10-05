import A12Kernel.Elaboration.Correlation
import A12Kernel.Semantics.ScalarEquality

namespace A12Kernel.Conformance.CorrelatedComparisonInputs
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def textPair : FlatComparison := .textFields .equal (.string { id := 1 }) (.string { id := 1 })
private def text (value : String) : CheckedCell := formalCheck { kind := .string } (.parsed (.str value))
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def emptyRequired : CheckedCell := { rawPresent := true, parsed := none, findings := [.required] }

private def validation {α : Type} (holds : α → α → Bool)
    (left : Except String (SimpleComparisonOperand α))
    (right : Unit → Except String (SimpleComparisonOperand α)) : Except String Verdict := do
  let left ← left
  let right ← right ()
  pure (evalSymmetricComparison holds left right)

example : textPair.foldSimpleReads .validation (fun _ => .ok (text "candidate"))
    (fun _ => .ok (text "captured")) validation = some (.ok .notFired) := by native_decide

example : textPair.foldSimpleReads .computation (fun _ => .ok invalid)
    (fun _ => .error "unbound captured row") evalComputationComparisonExcept =
      some (Except.ok (ε := String) (.poison .malformed)) ∧
    textPair.foldSimpleReads .validation (fun _ => .ok invalid)
    (fun _ => .error "unbound captured row") validation = some (.error "unbound captured row") := by native_decide

example : textPair.foldSimpleReads .computation (fun _ => .ok emptyRequired)
    (fun _ => .ok (text "present")) evalComputationComparisonExcept =
      some (Except.ok (ε := String) .notTrue) ∧
    textPair.foldSimpleReads .validation (fun _ => .ok emptyRequired)
    (fun _ => .ok (text "present")) validation = some (.ok .unknown) := by native_decide

example : textPair.foldSimpleReads .computation (fun _ => .ok emptyRequired)
    (fun _ => .ok invalid) evalComputationComparisonExcept =
      some (Except.ok (ε := String) (.poison .malformed)) := by native_decide

private def pair : CorrelatedHaving := .leaf (.simpleComparison .inner .outer textPair)
private def frame : CorrelationFrame := { innerEnv := [(0, 1)], outerEnv := [(0, 2)] }
private def context : CorrelationContext := {
  read := fun env _ => text (if env == frame.innerEnv then "candidate" else "captured") }

example : pair.evalTruthIn context frame = .fls ∧
    pair.evalComputationIn context frame = .notTrue ∧
    pair.fieldIds = [1] ∧ pair.markedFieldIds = [1] := by native_decide

private def model : FlatModel := {
  fields := [{
    id := 1, groupPath := ["Form", "Rows"], name := "Tag",
    policy := { kind := .string }, repeatableScope := [10] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

example : pair.wellFormedForEnvironments model [10] [10] = true ∧
    pair.wellFormedForEnvironments model [10] [] = false ∧
    pair.wellFormedForEnvironments model [] [10] = false ∧
    pair.reachesReopenedLevel model [10] = true ∧
    pair.reachesReopenedLevel model [20] = false := by native_decide

example : CorrelatedHaving.wellFormedForEnvironments (.leaf (.simpleComparison .inner .outer
    (.booleanFields .equal (.boolean { id := 1 }) (.boolean { id := 1 }))))
      model [10] [10] = false := by native_decide

end A12Kernel.Conformance.CorrelatedComparisonInputs
