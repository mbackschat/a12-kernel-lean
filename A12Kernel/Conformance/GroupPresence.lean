import A12Kernel.Semantics.GroupPresence

/-! # Group-presence conformance separators

These cases begin after descendant scope and group relevance have been resolved. They
separate formal admission from error propagation and lock the consumers that must not
collapse the resulting product state to one Boolean.
-/

namespace A12Kernel

private def numberPolicy : FieldPolicy := { kind := .number { scale := 1, signed := false } }

private def valid : CheckedCell := formalCheck numberPolicy (.parsed (.num 7))
private def malformed : CheckedCell := formalCheck numberPolicy (.rejected .malformed)
private def duplicate : CheckedCell := valid.withFinding .duplicateIndex
private def empty : CheckedCell := formalCheck numberPolicy .empty

private def state (cells : List CheckedCell) (rowContent structuralError : Bool)
    (relevance : GroupRelevance := .fullyRelevant) : GroupPresenceState :=
  ({ descendantCells := cells
     hasInstantiatedRow := rowContent
     structuralError
     relevance } : ResolvedGroupPresenceInput).derive

private def cleanEmpty : GroupPresenceState := state [empty] false false
private def cleanFilled : GroupPresenceState := state [valid] false false
private def malformedOnly : GroupPresenceState := state [malformed] false false
private def admittedAndErroneous : GroupPresenceState := state [valid, malformed] false false

example : malformedOnly = { content := false, erroneous := true, relevance := .fullyRelevant } := by native_decide
example : malformedOnly.groupFilled = .notFired := by native_decide
example : malformedOnly.groupNotFilled = .unknown := by native_decide

example : admittedAndErroneous = { content := true, erroneous := true, relevance := .fullyRelevant } := by native_decide
example : admittedAndErroneous.groupFilled = .fired .value := by native_decide
example : admittedAndErroneous.groupNotFilled = .unknown := by native_decide

-- A duplicate-index value was admitted before uniqueness marked it erroneous.
example : state [duplicate] false false =
    { content := true, erroneous := true, relevance := .fullyRelevant } := by native_decide

-- Instantiated rows are structural content independently of their cells and diagnostics.
example : state [empty] true false =
    { content := true, erroneous := false, relevance := .fullyRelevant } := by native_decide
example : state [empty] true true =
    { content := true, erroneous := true, relevance := .fullyRelevant } := by native_decide

example : (state [valid] false false .partlyRelevant).groupFilled = .fired .value := by native_decide
example : (state [empty] false false .partlyRelevant).groupNotFilled = .unknown := by native_decide
example : cleanEmpty.groupNotFilled = .fired .omission := by native_decide

-- Group-list predicates skip unavailable groups but retain independent decisive buckets.
example : GroupPresenceTally.ofStates [malformedOnly, cleanEmpty] =
    { filled := 0, empty := 1, unavailable := 1 } := by native_decide
example : GroupFillQuantifier.noGroupFilled.evalValidation [malformedOnly, cleanEmpty] =
    .falseOrUnknown := by native_decide
example : GroupFillQuantifier.notAllGroupsFilled.evalValidation [malformedOnly, cleanEmpty] =
    .fired .omission := by native_decide
example : GroupFillQuantifier.allGroupsFilled.evalValidation [admittedAndErroneous, cleanFilled] =
    .fired .value := by native_decide

-- The plain numeric count is stricter than the list tally.
example : numberOfFilledGroups [admittedAndErroneous, cleanFilled] = .unknown := by native_decide
example : numberOfFilledGroups [cleanFilled, cleanEmpty] = .value 1 := by native_decide
example : numberOfFilledGroups [state [valid] false false .partlyRelevant] = .unknown := by native_decide

example : malformedOnly.activatesRelativeRequiredness = false := by native_decide
example : (state [duplicate] false false).activatesRelativeRequiredness = true := by native_decide
example : (state [empty] true true).activatesRelativeRequiredness = true := by native_decide

end A12Kernel
