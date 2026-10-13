import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # Authored Boolean and Confirm comparisons

The authored reader admits Boolean and Confirm comparisons at the scope the rule's iteration binds:
a field against `True`, and two same-kind fields under the pair arm that computation guards share
(`elaborateScalarFieldComparisonWith`). Each lock names what it separates from a realistic wrong account.
-/

namespace A12Kernel.Dm.BooleanComparisonLocks
open Lean

private def number : FieldKind := .number { scale := 0, signed := true }

private def model : FlatModel := {
  fields := [
    { id := 1, name := "B1", groupPath := ["Form"], policy := { kind := .boolean } },
    { id := 2, name := "B2", groupPath := ["Form"], policy := { kind := .boolean } },
    { id := 3, name := "C1", groupPath := ["Form"], policy := { kind := .confirm } },
    { id := 4, name := "C2", groupPath := ["Form"], policy := { kind := .confirm } },
    { id := 5, name := "N", groupPath := ["Form"], policy := { kind := number } },
    { id := 6, name := "RB1", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 7, name := "RB2", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 8, name := "RC1", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 9, name := "RC2", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 10, name := "RN", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := number } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }

/-- A rule reports at its error field and must read it, so the compared body follows the generated
rules' shape: the error field's presence, then the comparison under test. -/
private def guarded (errorField body : String) : String := "FieldFilled(" ++ errorField ++ ") And (" ++ body ++ ")"

/-- A rule declared at the root reporting at the fixed field `N`. -/
private def fixedRule (body : String) : DmRule := {
  group := ["Form"], name := "Fixed", errorCode := "BOOL", severity := "ERROR"
  errorEntityRelPath := "../N", condition := guarded "N" body }

/-- A rule declared in the repeatable group, so its iteration is the group's own. -/
private def rowRule (body : String) : DmRule := {
  group := ["Form", "Rows"], name := "Row", errorCode := "BOOL", severity := "ERROR"
  errorEntityRelPath := "../RN", condition := guarded "RN" body }

/-- A root-declared rule whose repeatable error field alone derives the iteration. -/
private def derivedRule (body : String) : DmRule := {
  group := ["Form"], name := "Derived", errorCode := "BOOL", severity := "ERROR"
  errorEntityRelPath := "../Rows/RN", condition := guarded "Rows/RN" body }

/-- A rule comparing its own error field, which is the shape of a Boolean computation's generated check. -/
private def ownRule (group : GroupPath) (field : String) (condition : String) : DmRule := {
  group, name := "Own", errorCode := "BOOL", severity := "ERROR"
  errorEntityRelPath := "../" ++ field, condition }

/-- Every row carries `RN`, so the content gate never hides the comparison under test. -/
private def document (fixed : List (String × String)) (rows : List (List (String × String))) :
    Option (CheckedDocument model) := do
  let text (entries : List (String × String)) := entries.map fun (key, value) => (key, Json.str value)
  let row (entries : List (String × String)) := Json.mkObj (text (entries ++ [("RN", "1")]))
  let input ← (readDocument dm (.mkObj [("Form", .mkObj (text (fixed ++ [("N", "1")]) ++
    [("Rows", .arr (rows.map row).toArray)]))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

/-- The fired messages as `pointer:polarity`. -/
private def run (definition : DmRule) (fixed : List (String × String) := [])
    (rows : List (List (String × String)) := []) : Option (List String) := do
  let checked ← (checkRule dm .english definition).toOption
  let document ← document fixed rows
  pure ((← (runRule world document checked).toOption).map fun message =>
    let observed := observe model message
    observed.pointer ++ ":" ++ observed.messageType)

private def admitted (definition : DmRule) : Bool := (checkRule dm .english definition).toOption.isSome

example : model.validate.isOk = true := by native_decide

/-- A Boolean pair fires on its own polarity: `==` on equal values, `!=` on different ones. -/
example :
    run (fixedRule "[B1] == [B2]") [("B1", "true"), ("B2", "true")] = some ["Form/N:VALUE_ERROR"] ∧
    run (fixedRule "[B1] == [B2]") [("B1", "true"), ("B2", "false")] = some [] ∧
    run (fixedRule "[B1] != [B2]") [("B1", "true"), ("B2", "false")] = some ["Form/N:VALUE_ERROR"] ∧
    run (fixedRule "[B1] != [B2]") [("B1", "false"), ("B2", "false")] = some [] := by native_decide

/-- Two Confirm fields compare under `!=`; a different pair of values fires and equal ones stay silent. -/
example :
    run (fixedRule "[C1] != [C2]") [("C1", "true"), ("C2", "true")] = some [] ∧
    run (fixedRule "[C1] != [C2]") [("C1", "true")] = some ["Form/N:OMISSION_ERROR"] := by native_decide

/-- An empty Boolean is not evaluated, while an empty Confirm reads as false: the same pair shape stays
silent on Boolean and fires, with omission polarity, on Confirm. -/
example :
    run (fixedRule "[B1] != [B2]") [("B1", "true")] = some [] ∧
    run (fixedRule "[C1] != [C2]") [("C1", "true")] = some ["Form/N:OMISSION_ERROR"] ∧
    run (fixedRule "[C1] != [C2]") [] = some [] := by native_decide

/-- A row-bound Boolean pair reads both fields at the bound row. -/
example :
    run (rowRule "[RB1] == [RB2]") [] [[("RB1", "true"), ("RB2", "true")], [("RB1", "true"), ("RB2", "false")]] =
      some ["Form/Rows/RN:VALUE_ERROR"] ∧
    run (rowRule "[RB1] != [RB2]") [] [[("RB1", "true"), ("RB2", "true")], [("RB1", "true"), ("RB2", "false")]] =
      some ["Form/Rows[2]/RN:VALUE_ERROR"] := by native_decide

/-- A row-bound Confirm pair under `!=`, with the empty operand of the second row read as false. -/
example :
    run (rowRule "[RC1] != [RC2]") [] [[("RC1", "true"), ("RC2", "true")], [("RC1", "true")]] =
      some ["Form/Rows[2]/RN:OMISSION_ERROR"] := by native_decide

/-- A fixed field beside a row field is read once for every row: the fixed value never varies and only
the row's own operand does. -/
example :
    run (derivedRule "[Rows/RB1] == [B1]") [("B1", "true")] [[("RB1", "true")], [("RB1", "false")]] =
      some ["Form/Rows/RN:VALUE_ERROR"] ∧
    run (derivedRule "[B1] != [Rows/RB1]") [("B1", "true")] [[("RB1", "true")], [("RB1", "false")]] =
      some ["Form/Rows[2]/RN:VALUE_ERROR"] := by native_decide

/-- A row-bound field against `True` follows the bound row, for Boolean and for Confirm alike. -/
example :
    run (rowRule "[RB1] != True") [] [[("RB1", "true")], [("RB1", "false")]] =
      some ["Form/Rows[2]/RN:VALUE_ERROR"] ∧
    run (rowRule "[RB1] == True") [] [[("RB1", "true")], [("RB1", "false")]] =
      some ["Form/Rows/RN:VALUE_ERROR"] ∧
    run (rowRule "[RC1] != True") [] [[("RC1", "true")], []] = some ["Form/Rows[2]/RN:OMISSION_ERROR"] := by
  native_decide

/-- The iteration derives from the error field when the rule is declared at the root. -/
example :
    run (derivedRule "[Rows/RB1] != True") []
      [[("RB1", "true")], [("RB1", "false")]] = some ["Form/Rows[2]/RN:VALUE_ERROR"] ∧
    run (derivedRule "[Rows/RB1] != [Rows/RB2]") []
      [[("RB1", "true"), ("RB2", "true")], [("RB1", "true"), ("RB2", "false")]] =
      some ["Form/Rows[2]/RN:VALUE_ERROR"] := by native_decide

/-- A rule that compares its own error field binds that field's row, whether it is declared in the
repeatable group or at the root. -/
example :
    run (ownRule ["Form", "Rows"] "RB1" "FieldFilled(RB1) And [RB1] != True") []
      [[("RB1", "true")], [("RB1", "false")]] = some ["Form/Rows[2]/RB1:VALUE_ERROR"] ∧
    run (ownRule ["Form"] "Rows/RB1" "FieldFilled(Rows/RB1) And [Rows/RB1] != True") []
      [[("RB1", "false")], [("RB1", "true")]] = some ["Form/Rows/RB1:VALUE_ERROR"] := by native_decide

/-- A repeatable operand is admitted only where the rule's iteration binds its level: the identical
condition is refused at a fixed error field and admitted at a repeatable one. -/
example :
    admitted (derivedRule "[Rows/RB1] != [Rows/RB2]") = true ∧
    admitted (fixedRule "[Rows/RB1] != [Rows/RB2]") = false ∧
    admitted (derivedRule "[Rows/RB1] != True") = true ∧
    admitted (fixedRule "[Rows/RB1] != True") = false := by native_decide

/-- Confirm `==` between fields is refused beside its admitted `!=` twin, at both scopes. -/
example :
    admitted (fixedRule "[C1] != [C2]") = true ∧ admitted (fixedRule "[C1] == [C2]") = false ∧
    admitted (rowRule "[RC1] != [RC2]") = true ∧ admitted (rowRule "[RC1] == [RC2]") = false := by native_decide

/-- A Boolean against a field of another kind is refused beside its same-kind twin, and so is a
Confirm against a Boolean, in either order. -/
example :
    admitted (fixedRule "[B1] == [B2]") = true ∧ admitted (fixedRule "[B1] == [N]") = false ∧
    admitted (fixedRule "[N] == [B1]") = false ∧
    admitted (fixedRule "[B1] != [C1]") = false ∧ admitted (fixedRule "[C1] != [B1]") = false ∧
    admitted (rowRule "[RB1] == [RB2]") = true ∧ admitted (rowRule "[RB1] == [RC1]") = false := by native_decide

/-- The Kernel class the carrier refuses one comparison with, `some none` when it admits it, and `none`
when it refuses without a class or never reaches the kind arm. -/
private def kindArm (body : String) (declaringGroup : GroupPath := ["Form"])
    (bindingGroup : GroupPath := declaringGroup) : Option (Option KernelStaticDiagnostic) := do
  let parsed ← (parseText .english body).toOption
  let surface ← lowerFlat model declaringGroup parsed.body
  match BoundBooleanComparison.elaborate model declaringGroup bindingGroup surface with
  | .ok _ => some none
  | .error (.pair (.admission diagnostic)) => some (some diagnostic)
  | .error _ => none

/-- The refusal class is the Confirm class for a Confirm pair under `==` and for a Confirm against any
other kind, and the Boolean class for a Boolean against any other kind, each beside its admitted twin;
ordering draws the comparison gate before any kind arm. -/
example :
    kindArm "[C1] != [C2]" = some none ∧ kindArm "[C1] == [C2]" = some (some .invalidCompareToYes) ∧
    kindArm "[B1] == [B2]" = some none ∧ kindArm "[B1] == [N]" = some (some .invalidCompareToYesNo) ∧
    kindArm "[N] != [B1]" = some (some .invalidCompareToYesNo) ∧
    kindArm "[B1] != [C1]" = some (some .invalidCompareToYes) ∧
    kindArm "[C1] != [B1]" = some (some .invalidCompareToYes) ∧
    kindArm "[B1] < [B2]" = some (some .invalidTypeForComparison) := by native_decide

/-- The carrier's classes agree with the rule diagnostic projection, which derives them from the pair's
declared kinds alone, so the two accounts cannot drift apart unnoticed. -/
example :
    kindArm "[C1] == [C2]" = some ((ruleComparisonKindArm? .confirm .confirm).map (·.diagnostic)) ∧
    kindArm "[B1] == [N]" = some ((ruleComparisonKindArm? .boolean .number).map (·.diagnostic)) ∧
    kindArm "[B1] == [C1]" = some ((ruleComparisonKindArm? .boolean .confirm).map (·.diagnostic)) := by
  native_decide

/-- The same classes hold for row-bound operands. -/
example :
    kindArm "[Rows/RC1] != [Rows/RC2]" ["Form"] ["Form", "Rows"] = some none ∧
    kindArm "[Rows/RC1] == [Rows/RC2]" ["Form"] ["Form", "Rows"] = some (some .invalidCompareToYes) ∧
    kindArm "[Rows/RB1] == [Rows/RB2]" ["Form"] ["Form", "Rows"] = some none ∧
    kindArm "[Rows/RB1] == [Rows/RN]" ["Form"] ["Form", "Rows"] = some (some .invalidCompareToYesNo) := by
  native_decide

/-- A Confirm field admits only the literal `True`, beside its admitted twin, at the row scope too. -/
example :
    admitted (rowRule "[RC1] != True") = true ∧ admitted (rowRule "[RC1] != False") = false ∧
    admitted (rowRule "[RB1] != False") = true := by native_decide

end A12Kernel.Dm.BooleanComparisonLocks
