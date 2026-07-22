import A12Kernel.Elaboration.StarEnumerationValueList

/-! # Checked nested Enumeration-star literal value-list locks -/

namespace A12Kernel.Conformance.StarEnumerationValueList

open A12Kernel

private def priority : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Sections", "Items"]
    name := "Priority"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["STANDARD", "EXPRESS", "OVERNIGHT"]
      categories := [{ name := "SpeedClass", tokens := ["NORMAL", "FAST", "FAST"] }] }
    repeatableScope := [10, 20] }

private def amount : FlatFieldDecl :=
  { priority with
    id := 8
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    enumeration := none }

private def service : FlatFieldDecl :=
  { id := 9
    groupPath := ["Shop"]
    name := "Service"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["NEXT_DAY", "ECONOMY"]
      categories := [{ name := "ServiceClass", tokens := ["FAST", "SLOW"] }] } }

private def model : FlatModel :=
  { fields := [priority, amount, service]
    repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"], repeatability := some 2 },
      { level := 10, path := ["Shop", "Sections"], repeatability := some 2 }] }

private def starPath (field : String := "Priority") : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Shop" }, { name := "Sections", starred := true },
      { name := "Items", starred := true }]
    field }

private def authored (quantifier : ValueListQuantifier)
    (projectionRef : EnumerationProjectionRef := .stored)
    (values : List String := ["EXPRESS"])
    (field : String := "Priority")
    (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceStarEnumerationValueListSource :=
  { quantifier, fields := starPath field, projectionRef, values, having }

private def fieldPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Shop"], field }

private def directOperand (field : String := "Service")
    (projectionRef : EnumerationProjectionRef := .stored) : SurfaceTextFieldOperand :=
  match projectionRef with
  | .stored => .direct (fieldPath field)
  | .category name => .category (fieldPath field) name

private def starValuesAuthored (quantifier : ValueListQuantifier)
    (fieldProjection : EnumerationProjectionRef := .stored)
    (valuesProjection : EnumerationProjectionRef := .stored)
    (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceEnumerationValueListStarValuesSource :=
  { quantifier
    field := directOperand "Service" fieldProjection
    values := starPath
    valuesProjectionRef := valuesProjection
    having }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def sparseRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] }]

private def fullRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] },
  { group := 20, path := [1, 2] }, { group := 10, path := [2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def firstThen (first rest : RawCell) (environment : Env)
    (_ : FieldId) : RawCell :=
  if environment == [(10, 1), (20, 1)] then first else rest

private def unusedFilterRead (_ : Env) (_ : FieldId) : CheckedCell :=
  malformedCheckedCell

private def verdictOf (surface : SurfaceStarEnumerationValueListSource)
    (rows : List RowAddr) (read : Env → FieldId → RawCell)
    (outer : Env := []) : Option Verdict :=
  match elaborateStarEnumerationValueListSource model priority.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull (document rows) outer unusedFilterRead read with
      | .error _ => none
      | .ok verdict => some verdict

private def directRead (raw : RawCell) : RawFlatContext where
  read id := if id == service.id then raw else .empty

private def starValuesVerdictOf
    (surface : SurfaceEnumerationValueListStarValuesSource)
    (rows : List RowAddr) (direct : RawFlatContext)
    (read : Env → FieldId → RawCell) (outer : Env := []) : Option Verdict :=
  match elaborateEnumerationValueListStarValuesSource model priority.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull (document rows) outer direct unusedFilterRead read with
      | .error _ => none
      | .ok verdict => some verdict

private def partialStarValuesResultOf
    (surface : SurfaceEnumerationValueListStarValuesSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (direct : RawFlatContext) (read : Env → FieldId → RawCell) :
    Option PartialHavingValueListResult :=
  match elaborateEnumerationValueListStarValuesSource model priority.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartial (document rows) [] scope direct read with
      | .ok result => some result
      | .error _ => none

private def partialResultOf (surface : SurfaceStarEnumerationValueListSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Option PartialHavingValueListResult :=
  match elaborateStarEnumerationValueListSource model priority.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartial (document rows) [] scope read with
      | .ok result => some result
      | .error _ => none

private def partialVerdictOf (surface : SurfaceStarEnumerationValueListSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Option Verdict :=
  match partialResultOf surface rows scope read with
  | some (.evaluated verdict) => some verdict
  | _ => none

private def errorOf (surface : SurfaceStarEnumerationValueListSource) :
    Option StarEnumerationValueListElabError :=
  match elaborateStarEnumerationValueListSource model priority.groupPath surface with
  | .ok _ => none
  | .error error => some error

private def starValuesErrorOf
    (surface : SurfaceEnumerationValueListStarValuesSource) :
    Option StarEnumerationValueListElabError :=
  match elaborateEnumerationValueListStarValuesSource model priority.groupPath surface with
  | .ok _ => none
  | .error error => some error

private def repetition (origin : HavingOrigin) (groups : List String) :
    SurfaceHavingRepetitionRef :=
  { origin, group := { base := .absolute, groups } }

private def earlierSibling : SurfaceCorrelatedHaving :=
  .and
    (.compareRepetitions .equal
      (repetition .inner ["Shop", "Sections"])
      (repetition .outer ["Shop", "Sections"]))
    (.compareRepetitions .less
      (repetition .inner ["Shop", "Sections", "Items"])
      (repetition .outer ["Shop", "Sections", "Items"]))

/- Category projection stays positional and many-to-one across a starred stream. -/
example :
    verdictOf (authored .atLeastOne (.category "SpeedClass") ["FAST"])
        fullRows (firstThen (.parsed (.enum "EXPRESS")) (.parsed (.enum "OVERNIGHT"))) =
      some (.fired .value) := by
  native_decide

/- An empty category cell stays empty: `No` fires OMISSION while `NotAll` does not fire. -/
example :
    verdictOf (authored .no (.category "SpeedClass") ["FAST"])
        fullRows (firstThen .empty (.parsed (.enum "STANDARD"))) =
      some (.fired .omission) ∧
    verdictOf (authored .notAll (.category "SpeedClass") ["FAST"])
        sparseRows (firstThen .empty .empty) = some .notFired := by
  native_decide

/- An out-of-domain stored token remains a formal failure and poisons `No`. -/
example :
    verdictOf (authored .no (.category "SpeedClass") ["FAST"])
        fullRows (firstThen (.parsed (.enum "INVALID")) (.parsed (.enum "STANDARD"))) =
      some .unknown := by
  native_decide

/- Hierarchical omitted tails affect fired `No`, but not fired `NotAll`. -/
example :
    verdictOf (authored .no .stored ["EXPRESS"]) sparseRows
        (firstThen (.parsed (.enum "STANDARD")) .empty) = some (.fired .omission) ∧
    verdictOf (authored .notAll .stored ["EXPRESS"]) sparseRows
        (firstThen (.parsed (.enum "STANDARD")) .empty) = some (.fired .value) := by
  native_decide

/- A checked filter selects before projection and escalates a resulting fire. -/
example :
    verdictOf
        (authored .atLeastOne (.category "SpeedClass") ["FAST"]
          (having := some earlierSibling)) fullRows
        (firstThen (.parsed (.enum "EXPRESS")) (.parsed (.enum "STANDARD")))
        [(10, 1), (20, 2)] = some (.fired .omission) := by
  native_decide

/- Direct and starred category projections compare their projected tokens without a domain-containment gate. -/
example :
    starValuesVerdictOf
        (starValuesAuthored .atLeastOne (.category "ServiceClass")
          (.category "SpeedClass")) fullRows
        (directRead (.parsed (.enum "NEXT_DAY")))
        (firstThen (.parsed (.enum "EXPRESS")) (.parsed (.enum "STANDARD"))) =
      some (.fired .value) := by
  native_decide

/- Empty starred values retain the values-side `No`/`NotAll` OMISSION polarity. -/
example :
    starValuesVerdictOf (starValuesAuthored .no) sparseRows
        (directRead (.parsed (.enum "NEXT_DAY"))) (firstThen .empty .empty) =
      some (.fired .omission) ∧
    starValuesVerdictOf (starValuesAuthored .notAll) sparseRows
        (directRead (.parsed (.enum "NEXT_DAY"))) (firstThen .empty .empty) =
      some (.fired .omission) := by
  native_decide

/- An invalid stored value on the starred values side poisons `NotAll`. -/
example :
    starValuesVerdictOf (starValuesAuthored .notAll) fullRows
        (directRead (.parsed (.enum "NEXT_DAY")))
        (firstThen (.parsed (.enum "INVALID")) (.parsed (.enum "STANDARD"))) =
      some .unknown := by
  native_decide

/- Partial validation skips a checked filter before malformed topology or Enumeration reads. -/
example :
    partialResultOf
        (authored .atLeastOne (.category "SpeedClass") ["FAST"]
          (having := some earlierSibling))
        [{ group := 20, path := [1, 1] }] .full
        (firstThen (.parsed (.enum "INVALID")) (.rejected .malformed)) =
      some .skippedHaving := by
  native_decide

private def firstPriorityOnly : ValidationRelevanceScope :=
  .partialSet [{
    path := priority.path
    indices := [.concrete 1, .concrete 1, .concrete 1, .concrete 1] }]

private def firstPriorityAndService : ValidationRelevanceScope :=
  .partialSet [
    { path := service.path, indices := [.concrete 1, .concrete 1] },
    { path := priority.path,
      indices := [.concrete 1, .concrete 1, .concrete 1, .concrete 1] }]

/- Partial validation projects only relevant cells; masked invalid tokens are never checked. -/
example :
    partialVerdictOf
        (authored .atLeastOne (.category "SpeedClass") ["FAST"])
        fullRows firstPriorityOnly
        (firstThen (.parsed (.enum "EXPRESS")) (.parsed (.enum "INVALID"))) =
      some (.fired .value) := by
  native_decide

/- A concrete relevant starred member can witness `AtLeastOne`, while its unknown extent suppresses `NotAll`. -/
example :
    partialStarValuesResultOf
        (starValuesAuthored .atLeastOne (.category "ServiceClass")
          (.category "SpeedClass")) fullRows firstPriorityAndService
        (directRead (.parsed (.enum "NEXT_DAY")))
        (firstThen (.parsed (.enum "EXPRESS")) (.parsed (.enum "INVALID"))) =
      some (.evaluated (.fired .value)) ∧
    partialStarValuesResultOf
        (starValuesAuthored .notAll (.category "ServiceClass")
          (.category "SpeedClass")) fullRows firstPriorityAndService
        (directRead (.parsed (.enum "ECONOMY")))
        (firstThen (.parsed (.enum "EXPRESS")) (.parsed (.enum "INVALID"))) =
      some (.evaluated .unknown) := by
  native_decide

/- A values-side filter skips partial validation before the direct field, topology, or projected reads. -/
example :
    partialStarValuesResultOf
        (starValuesAuthored .atLeastOne (.category "ServiceClass")
          (.category "SpeedClass") (some earlierSibling))
        [{ group := 20, path := [1, 1] }] .full
        (directRead (.parsed (.enum "INVALID")))
        (firstThen (.parsed (.enum "INVALID")) (.rejected .malformed)) =
      some .skippedHaving := by
  native_decide

/- Static admission is projection-specific and rejects the wrong kind. -/
example :
    errorOf (authored .atLeastOne .stored []) = some .emptyValues ∧
    errorOf (authored .atLeastOne (.category "SpeedClass") ["EXPRESS"]) =
      some (.enumerationOperand priority.path (.invalidLiteral "EXPRESS")) ∧
    errorOf (authored .atLeastOne (.category "Unknown") ["FAST"]) =
      some (.enumerationOperand priority.path (.unknownCategory "Unknown")) ∧
    errorOf (authored .atLeastOne .stored ["1"] "Amount") =
      some (.fieldNotEnumeration amount.path .number) := by
  native_decide

/- Both projections are checked against their own exact declarations. -/
example :
    starValuesErrorOf
        (starValuesAuthored .atLeastOne (.category "SpeedClass")) =
      some (.enumerationOperand service.path (.unknownCategory "SpeedClass")) := by
  native_decide

end A12Kernel.Conformance.StarEnumerationValueList
