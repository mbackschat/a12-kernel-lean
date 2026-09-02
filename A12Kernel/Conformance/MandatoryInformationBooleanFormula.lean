import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information Boolean-formula locks

These cases cover the measured pure negative-field CNF, DNF, and flat three-way disjunction cells while keeping unmeasured arity, duplicates, and shared-field positions fail-closed.
-/

namespace A12Kernel.Conformance.MandatoryInformationBooleanFormula

open A12Kernel

private def derive (formula : MandatoryNegativeFieldFormula String) :
    Option (MandatoryInformation String String) :=
  deriveCheckedMandatoryInformation (fun _ => "Form") [
    .negativeFieldFormula formula
  ]

private def result (fields : List String) : Option (MandatoryInformation String String) :=
  some {
    mandatory := fields
    mandatoryForRootGroup := fields
    mandatoryRootGroups := ["Form"]
  }

private def cnfShared : MandatoryNegativeFieldFormula String :=
  .conjunctionOfDisjunctions [["A", "B"], ["A", "C"]]

private def cnfDisjoint : MandatoryNegativeFieldFormula String :=
  .conjunctionOfDisjunctions [["A", "B"], ["C"]]

private def dnfShared : MandatoryNegativeFieldFormula String :=
  .disjunctionOfConjunctions [["A", "B"], ["A", "C"]]

private def flatTriple : MandatoryNegativeFieldFormula String :=
  .flatDisjunction ["A", "B", "C"]

example :
    derive cnfShared = result ["A"] ∧
      derive cnfDisjoint = result [] ∧
      derive dnfShared = result [] ∧
      derive flatTriple = result ["A", "B", "C"] := by
  native_decide

example :
    derive (.flatDisjunction ["A", "B", "C", "D"]) = none ∧
      derive (.flatDisjunction ["A", "A", "B"]) = none ∧
      derive (.conjunctionOfDisjunctions [["B", "A"], ["A", "C"]]) = none ∧
      derive (.conjunctionOfDisjunctions [["A", "B"]]) = none ∧
      derive (.disjunctionOfConjunctions [["A"], ["A", "B"]]) = none ∧
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .negativeFieldFormula flatTriple,
        .fieldNotFilled "D"
      ] = none := by
  native_decide

end A12Kernel.Conformance.MandatoryInformationBooleanFormula
