import A12Kernel.Elaboration.StringNumberComputationRunApplication

/-! # Family-separated String and Number application locks -/

namespace A12Kernel.Conformance.StringNumberComputationRunApplication

open A12Kernel

private def storedString (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

private def storedNumber (amount : Int) : StoredNumber :=
  { unscaled := amount, scale := 0 }

private def stringEntry (target : Nat) (text : String)
    (nonempty : text ≠ "") : SourcedStringTargetOutcome Nat := {
  targetField := target
  outcome := .accepted (storedString text nonempty)
  source := .absent
}

private def numberEntry (target : Nat) (amount : Int) :
    SourcedNumericTargetOutcome Nat := {
  targetField := target
  outcome := .accepted (storedNumber amount)
  source := .absent
}

private def emptyStringDestination : StringComputationDestination Nat :=
  fun _ => .absent

private def emptyNumberDestination : NumericComputationDestination Nat :=
  fun _ => .absent

private def changedView : StringNumberComputationRunView Unit Unit Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [] [
    stringEntry 1 "NEW" (by decide)]
  number := NumericComputationRunView.fromPartitionedSourceOutcomes [] [
    numberEntry 2 7]
}

private def duplicateStringView : StringNumberComputationRunView Unit Unit Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [] [
    stringEntry 1 "ONE" (by decide),
    stringEntry 1 "TWO" (by decide)]
  number := NumericComputationRunView.fromPartitionedSourceOutcomes [] [
    numberEntry 2 7]
}

private def duplicateNumberView : StringNumberComputationRunView Unit Unit Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [] [
    stringEntry 1 "NEW" (by decide)]
  number := NumericComputationRunView.fromPartitionedSourceOutcomes [] [
    numberEntry 2 7,
    numberEntry 2 8]
}

private def stringState?
    (application : StringNumberComputationRunApplication Nat)
    (target : Nat) : Option StringTargetState :=
  application.string.toOption.map fun destination => destination target

private def numberState?
    (application : StringNumberComputationRunApplication Nat)
    (target : Nat) : Option NumericTargetState :=
  application.number.toOption.map fun destination => destination target

private def stringDuplicate?
    (application : StringNumberComputationRunApplication Nat) : Option Nat :=
  match application.string with
  | .error (.duplicateActionTarget target) => some target
  | .ok _ => none

private def numberDuplicate?
    (application : StringNumberComputationRunApplication Nat) : Option Nat :=
  match application.number with
  | .error (.duplicateActionTarget target) => some target
  | .ok _ => none

/- Both family actions remain typed and apply to their own destination projections. -/
example :
    let applied := changedView.applyTo
      emptyStringDestination emptyNumberDestination
    stringState? applied 1 =
        some (.presentValue (storedString "NEW" (by decide))) ∧
      numberState? applied 2 =
        some (.presentValue (.decimal (storedNumber 7))) := by
  native_decide

/- A malformed String action list does not hide the independent successful Number application. -/
example :
    let applied := duplicateStringView.applyTo
      emptyStringDestination emptyNumberDestination
    stringDuplicate? applied = some 1 ∧
      numberState? applied 2 =
        some (.presentValue (.decimal (storedNumber 7))) := by
  native_decide

/- The symmetric malformed Number list likewise leaves the String application observable. -/
example :
    let applied := duplicateNumberView.applyTo
      emptyStringDestination emptyNumberDestination
    stringState? applied 1 =
        some (.presentValue (storedString "NEW" (by decide))) ∧
      numberDuplicate? applied = some 2 := by
  native_decide

end A12Kernel.Conformance.StringNumberComputationRunApplication
