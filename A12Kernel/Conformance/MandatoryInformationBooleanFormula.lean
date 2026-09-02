import A12Kernel.Semantics.MandatoryInformation

/-! # Mandatory-information Boolean-formula locks

These cases cover the measured pure negative-field CNF, DNF, and flat three-way disjunction cells, including every shared-field position in the exact two-clause, width-two matrices, while keeping unmeasured arity, clause-local duplicates, other shared-field multiplicities, and wider clause shapes fail-closed.
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
    derive (.conjunctionOfDisjunctions [["A", "B"], ["C", "A"]]) = result ["A"] ∧
      derive (.conjunctionOfDisjunctions [["B", "A"], ["A", "C"]]) = result ["A"] ∧
      derive (.conjunctionOfDisjunctions [["B", "A"], ["C", "A"]]) = result ["A"] ∧
      derive (.disjunctionOfConjunctions [["A", "B"], ["C", "A"]]) = result [] ∧
      derive (.disjunctionOfConjunctions [["B", "A"], ["A", "C"]]) = result [] ∧
      derive (.disjunctionOfConjunctions [["B", "A"], ["C", "A"]]) = result [] := by
  native_decide

example :
    derive (.flatDisjunction ["A", "B", "C", "D"]) = none ∧
      derive (.flatDisjunction ["A", "A", "B"]) = none ∧
      derive (.conjunctionOfDisjunctions [["A", "B"], ["C", "D"]]) = none ∧
      derive (.conjunctionOfDisjunctions [["A", "A"], ["B", "C"]]) = none ∧
      derive (.disjunctionOfConjunctions [["A", "B"], ["C", "C"]]) = none ∧
      derive (.disjunctionOfConjunctions [["A", "B"], ["B", "A"]]) = none ∧
      derive (.conjunctionOfDisjunctions [["A", "B"]]) = none ∧
      derive (.disjunctionOfConjunctions [["A"], ["A", "B"]]) = none ∧
      deriveCheckedMandatoryInformation (fun _ : String => "Form") [
        .negativeFieldFormula flatTriple,
        .fieldNotFilled "D"
      ] = none := by
  native_decide

end A12Kernel.Conformance.MandatoryInformationBooleanFormula
