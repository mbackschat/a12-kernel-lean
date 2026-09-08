import A12Kernel.Elaboration.ComputationNormalForm

/-! # Locks on the generated normalized computation

The bridge theorem says the joiner's output always passes. These cases pin the two things that would make that theorem worthless: that the joiner emits what the Kernel's joiner emits, and that the checker rejects anything at all.

The admitted structured computations are measured through `computation add --dry-run`; the shapes the checker rejects are hand-built, because the joiner cannot produce them ([checkpoint](../../docs/SOURCES.md#src-computation-normal-form-generation)).
-/

namespace A12Kernel.Conformance.ComputationNormalForm

open A12Kernel

/-- The measured single-alternative computation. -/
private def sole : StructuredComputation :=
  { computedField := "/C/N", alternatives := [{ operation := "[/C/P] + 1" }] }

/-- The measured two-alternative computation with a common precondition, which exercises the
alternation branch and the precondition member together. -/
private def branching : StructuredComputation :=
  { computedField := "/C/N", commonPrecondition := some "FieldFilled(/C/P)",
    alternatives := [{ operation := "[/C/P] + 1" },
                     { precondition := "FieldFilled(/C/A)", operation := "2" }] }

/- The joiner's output for one alternative: the gate, then the branch, and no alternation. A
   consumer wrapping a sole alternative in a one-element alternation emits a different condition —
   the Kernel's joiner does not, and the difference is visible to anything reading the tree. -/
example :
    joinAlternatives sole =
      some { gateField := some "/C/N",
             members := [.branch { field := "/C/N", spelling := .notEqual,
                                   operation := "[/C/P] + 1" }] } := by
  native_decide

/- With several alternatives the members are the common precondition and one alternation, in that
   order, and each alternative keeps its own precondition inside its branch rather than being
   hoisted. -/
example :
    joinAlternatives branching =
      some { gateField := some "/C/N",
             members := [.precondition "FieldFilled(/C/P)",
                         .alternation
                           [{ field := "/C/N", spelling := .notEqual,
                              operation := "[/C/P] + 1" },
                            { precondition := some "FieldFilled(/C/A)", field := "/C/N",
                              spelling := .notEqual, operation := "2" }]] } := by
  native_decide

/- Both measured computations pass the checker, which is the bridge theorem's content on the two
   shapes that were actually observed admitted. -/
example :
    (joinAlternatives sole).all (normalizedFormRefusal "/C/N" · == none) ∧
      (joinAlternatives branching).all (normalizedFormRefusal "/C/N" · == none) := by
  native_decide

/- A tolerance range changes the emitted comparison and nothing else, and it is the only thing that
   does. This is the pair the rounding-mode law rests on. -/
example :
    emittedSpelling { operation := "x" } = .notEqual ∧
      emittedSpelling { operation := "x", toleranceRange := some .five } =
        .differsWithTolerance .five ∧
      alternativeRounding { operation := "x" } = .exact ∧
      alternativeRounding { operation := "x", toleranceRange := some .five } = .inexact .five := by
  native_decide

/- The rounding check is not vacuous: the combination it exists to catch is expressible and caught,
   it is simply never emitted. Without this case the law proving it never fires would be satisfied
   by a check that never fires at all. -/
example :
    roundingRefusal .notEqual (.inexact .one) = some .wrongRoundingMode ∧
      roundingRefusal .notEqual .exact = none ∧
      roundingRefusal (.differsWithTolerance .one) (.inexact .one) = none ∧
      roundingRefusal (.differsWithTolerance .one) .exact = none := by
  native_decide

/- The checker rejects, and rejects the right things: an ungated condition, a gate on the wrong
   field, a branch comparing a different field, and a second gate where a member belongs. -/
example :
    normalizedFormRefusal "/C/N" { gateField := none, members := [] } =
        some .invalidFieldGate ∧
      normalizedFormRefusal "/C/N" { gateField := some "/C/P", members := [] } =
        some .invalidFieldGate ∧
      normalizedFormRefusal "/C/N"
          { gateField := some "/C/N",
            members := [.branch { field := "/C/P", spelling := .notEqual, operation := "1" }] } =
        some .invalidComparison ∧
      normalizedFormRefusal "/C/N"
          { gateField := some "/C/N", members := [.strayGate "/C/N"] } =
        some .invalidComparison := by
  native_decide

/- A malformed branch inside an alternation is caught too, so the alternation is not a hole in the
   checker — which matters because the alternation is the only place the joiner puts more than one
   branch. -/
example :
    normalizedFormRefusal "/C/N"
        { gateField := some "/C/N",
          members := [.alternation
            [{ field := "/C/N", spelling := .notEqual, operation := "1" },
             { field := "/C/P", spelling := .notEqual, operation := "2" }]] } =
      some .invalidComparison := by
  native_decide

/- An empty alternative list emits no condition at all, which is a different answer from emitting
   one that fails. A consumer treating the two alike reports a refusal the Kernel does not. -/
example :
    joinAlternatives { computedField := "/C/N", alternatives := [] } = none := by
  native_decide

/- Twelve distinct keys. The two that break the family's `MVK_ERROR_` prefix are the ones a consumer
   assembling a key by concatenation gets wrong. -/
example :
    (CalculationRefusal.all.map (·.catalogKey)).eraseDups.length = 12 ∧
      CalculationRefusal.calcInvalidActionType.catalogKey = "MVK_CALC_INVALID_ACTION_TYPE" ∧
      (CalculationRefusal.all.filter fun r =>
          r.catalogKey.startsWith "MVK_ERROR_").length = 11 := by
  native_decide

end A12Kernel.Conformance.ComputationNormalForm
