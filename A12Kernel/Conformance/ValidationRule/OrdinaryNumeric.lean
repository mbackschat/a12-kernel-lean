import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime

/-! # Ordinary repeatable numeric whole-rule locks -/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryNumeric

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def ordinaryNumericData (stored : String) (raw : Option RawCell) : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }]
    cells := match raw with
      | none => []
      | some cell => [{
          address := { field := outerAmount.id, path := [1] }
          stored
          raw := cell
        }] }

private def evalOrdinaryNumeric? (stored : String) (raw : Option RawCell) :
    Option (Verdict × Option CellAddr) :=
  ordinaryRepeatableNumericRule?.bind fun rule =>
    (evalOrdinaryRule? rule (ordinaryNumericData stored raw)).bind fun outcomes =>
      (outcomes.map (fun entry =>
        (entry.2.verdict, entry.2.message?.map (·.errorAddress)))).head?

/- Addressed ordinary Number evaluation preserves the established nested arithmetic and direct-comparison empty polarity at the selected row: present zero is a value firing, absence is an omission firing, and malformed input stays semantic UNKNOWN. -/
example :
    evalOrdinaryNumeric? "2" (some (.parsed (.num 2))) =
        some (.fired .value,
          some { field := outerAmount.id, path := [1] }) ∧
      evalOrdinaryNumeric? "0" (some (.parsed (.num 0))) =
        some (.fired .value,
          some { field := outerAmount.id, path := [1] }) ∧
      evalOrdinaryNumeric? "" none =
        some (.fired .omission,
          some { field := outerAmount.id, path := [1] }) ∧
      evalOrdinaryNumeric? "bad" (some (.rejected .malformed)) =
        some (.unknown, none) := by
  native_decide

/- A nested direct Number keeps the complete outer/inner environment and emits at the exact two-level error address. -/
example :
    (nestedRepeatableNumericRule?.bind fun rule =>
      (evalOrdinaryRule? rule {
        instantiatedRows := [
          { group := 10, path := [1] },
          { group := 10, path := [2] },
          { group := 20, path := [2, 1] }]
        cells := [{
          address := { field := innerAmount.id, path := [2, 1] }
          stored := "3"
          raw := .parsed (.num 3)
        }]
      }).map fun outcomes => outcomes.map fun entry =>
        (entry.1, entry.2.verdict,
          entry.2.message?.map (·.errorAddress))) =
      some [(
        [(10, 2), (20, 1)],
        .fired .value,
        some { field := innerAmount.id, path := [2, 1] })] := by
  native_decide

/- One checked composite may read an ancestor and current-row Number through their declaration-owned scopes. Execute preserves the full target environment, while Transform/Explain recover both certified declarations from the same tree. -/
example :
    ((ancestorCurrentNumericRule?.bind fun rule =>
      (evalOrdinaryRule? rule {
        instantiatedRows := [
          { group := 10, path := [1] },
          { group := 20, path := [1, 1] }]
        cells := [
          classifiedCell outerAmount.id [1] "2" (.parsed (.num 2)),
          classifiedCell innerAmount.id [1, 1] "3" (.parsed (.num 3))]
      }).map fun outcomes =>
        (rule.condition.core.ordinaryRepeatableFields.map (·.id),
          outcomes.map fun entry =>
            (entry.1, entry.2.verdict,
              entry.2.message?.map (·.errorAddress)))) ==
      some (
        [outerAmount.id, innerAmount.id],
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerAmount.id, path := [1, 1] })])) = true := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryNumeric
