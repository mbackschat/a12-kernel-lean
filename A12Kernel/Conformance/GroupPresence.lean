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
example : GroupListPresenceTally.ofGroupStates [malformedOnly, cleanEmpty] =
    { filled := 0, empty := 1, unavailable := 1 } := by native_decide
example : GroupFillQuantifier.noGroupFilled.evalValidation [malformedOnly, cleanEmpty] =
    .falseOrUnknown := by native_decide
example : GroupFillQuantifier.notAllGroupsFilled.evalValidation [malformedOnly, cleanEmpty] =
    .fired .omission := by native_decide
example : GroupFillQuantifier.allGroupsFilled.evalValidation [admittedAndErroneous, cleanFilled] =
    .fired .value := by native_decide

-- Field and group operands enter one shared presence classification without treating formal unavailability as empty.
example : (observeCell .validation valid).asGroupListPresence = .filled := by native_decide
example : (observeCell .validation empty).asGroupListPresence = .empty := by native_decide
example : (observeCell .validation malformed).asGroupListPresence = .unavailable := by native_decide

-- The computation arm reads the same cells and answers the malformed one differently: it is
-- present there and unavailable above. The empty and admitted cells are classified alike, so
-- formal invalidity is the only cell-level dimension the two arms disagree on.
example : (observeCell .computation valid).presentForComputation = true := by native_decide
example : (observeCell .computation empty).presentForComputation = false := by native_decide
example : (observeCell .computation malformed).presentForComputation = true := by native_decide

-- A required-and-empty cell is erroneous for validation yet absent for the computing
-- instance, because computation does not read the validation-scoped required finding.
example : (observeCell .validation (empty.withFinding .required)).asGroupListPresence =
    .unavailable := by native_decide
example : (observeCell .computation (empty.withFinding .required)).presentForComputation =
    false := by native_decide

-- One malformed-only descendant makes its group present for computation while the same
-- group is neither filled nor empty for validation, and the count cannot answer unknown.
example : groupPresentForComputation [observeCell .computation malformed] = true := by
  native_decide
example : groupPresentForComputation [observeCell .computation empty] = false := by
  native_decide
example :
    numberOfFilledGroupsForComputation
      [[observeCell .computation malformed], [observeCell .computation valid]] = 2 ∧
      numberOfFilledGroupsForComputation
        [[observeCell .computation empty], [observeCell .computation empty]] = 0 := by
  native_decide
example :
    (GroupFillQuantifier.allGroupsFilled.evalPresence [.filled, .filled],
      GroupFillQuantifier.noGroupFilled.evalPresence [.empty, .empty],
      GroupFillQuantifier.atLeastOneGroupFilled.evalPresence [.unavailable, .filled],
      GroupFillQuantifier.notAllGroupsFilled.evalPresence [.unavailable, .empty],
      GroupFillQuantifier.groupsNotCollectivelyFilled.evalPresence [.filled, .empty]) =
    (.fired .value, .fired .omission, .fired .value,
      .fired .omission, .fired .omission) := by
  native_decide

/- The count reads each operand through the same decided-presence projection the group-list
   predicates use, so it cannot be stricter than `AllGroupsFilled` over the same states. An error
   blocks only the *negative* answer: an already admitted content decides the group filled however
   its siblings failed, while a group whose sole non-empty descendant is malformed leaves presence
   undecided and takes the whole count with it. Measured on both codegen strategies at the
   [unavailability checkpoint](../../docs/SOURCES.md#src-group-count-unavailability), where the
   threshold rule fires with the invalid sibling present and goes silent when the invalid cell
   stands alone. -/
example : numberOfFilledGroups [admittedAndErroneous, cleanFilled] = .value 2 := by native_decide
example : numberOfFilledGroups [malformedOnly, cleanFilled] = .unknown := by native_decide

/- The same pair on the second operand. The kernel repeats both answers there, so neither operand
   position nor a document-global error is the cause; only the erroneous group's own content is. -/
example : numberOfFilledGroups [cleanFilled, admittedAndErroneous] = .value 2 := by native_decide
example : numberOfFilledGroups [cleanFilled, malformedOnly] = .unknown := by native_decide

example : numberOfFilledGroups [cleanFilled, cleanEmpty] = .value 1 := by native_decide

/- Coverage is the other dimension and is *not* what the checkpoint measured. Visible content still
   decides a partly covered group, matching `groupFilled` above; invisible absence does not. -/
example : numberOfFilledGroups [state [valid] false false .partlyRelevant] = .value 1 := by
  native_decide
example : numberOfFilledGroups [state [empty] false false .partlyRelevant] = .unknown := by
  native_decide

/- A fixed group is one declared entity, not one entity per descendant. One filled descendant makes
   a half-filled group count as given; exhausting both declared group operands makes the count fixed. -/
example :
    let counted := numberOfFilledGroups [state [valid, empty] false false, cleanFilled]
    counted = .value 2 ∧ counted.availableWithFillability? 2 = some (2, .fixed) := by
  native_decide

example : malformedOnly.activatesRelativeRequiredness = false := by native_decide
example : (state [duplicate] false false).activatesRelativeRequiredness = true := by native_decide
example : (state [empty] true true).activatesRelativeRequiredness = true := by native_decide

end A12Kernel
