import A12Kernel.Elaboration.EnumerationFirstFilledComputation

/-! # Checked Enumeration-target `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.EnumerationFirstFilledComputation

open A12Kernel

private def enumField (id : FieldId) (path : List String)
    (enumeration : EnumerationDeclaration)
    (repeatableScope : List GroupId := []) : FlatFieldDecl :=
  {
    id
    groupPath := path.dropLast
    name := path.getLast!
    policy := { kind := .enumeration }
    enumeration := some enumeration
    repeatableScope
  }

private def targetDomain : EnumerationDeclaration :=
  { storedTokens := ["A", "B"] }

private def compatibleDomain : EnumerationDeclaration :=
  { storedTokens := ["A", "B"] }

private def widerDomain : EnumerationDeclaration :=
  { storedTokens := ["A", "C"] }

private def displayedDomain : EnumerationDeclaration :=
  {
    storedTokens := ["A", "B"]
    displayFacts := [
      { locale := "en", stored := "A", display := "Alpha" },
      { locale := "en", stored := "B", display := "Beta" }
    ]
  }

private def projectedDomain : EnumerationDeclaration :=
  {
    storedTokens := ["X", "Y"]
    displayFacts := [
      { locale := "en", stored := "X", display := "Ex" },
      { locale := "en", stored := "Y", display := "Why" }
    ]
    categories := [{ name := "Target", tokens := ["A", "B"] }]
  }

private def target := enumField 0 ["Form", "Target"] targetDomain
private def compatible := enumField 1 ["Form", "Compatible"] compatibleDomain
private def wider := enumField 2 ["Form", "Wider"] widerDomain
private def displayed := enumField 3 ["Form", "Displayed"] displayedDomain
private def projected := enumField 4 ["Form", "Projected"] projectedDomain
private def repeated :=
  enumField 5 ["Form", "Rows", "Repeated"] projectedDomain [10]
private def plainString : FlatFieldDecl :=
  {
    id := 6
    groupPath := ["Form"]
    name := "PlainString"
    policy := { kind := .string }
  }

private def filterLeft : FlatFieldDecl :=
  {
    id := 7
    groupPath := ["Form", "Rows"]
    name := "FilterLeft"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10]
  }

private def filterRight : FlatFieldDecl :=
  {
    id := 8
    groupPath := ["Form", "Rows"]
    name := "FilterRight"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10]
  }

private def model : FlatModel :=
  {
    fields := [target, compatible, wider, displayed, projected, repeated,
      plainString, filterLeft, filterRight]
    repeatableGroups := [{
      level := 10
      path := ["Form", "Rows"]
      repeatability := some 3
    }]
  }

private def directPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form"], field := name }

private def starPath : SurfaceStarFieldPath :=
  {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Repeated"
  }

private def source (first : SurfaceEnumerationFirstFilledOperand)
    (rest : List SurfaceEnumerationFirstFilledOperand) :
    SurfaceEnumerationFirstFilledSource :=
  { first, rest }

private def number (value : Rat) : RawCell :=
  .parsed (.num value)

private def direct (name : String) : SurfaceEnumerationFirstFilledOperand :=
  .field (.direct (directPath name))

private def category (name categoryName : String) :
    SurfaceEnumerationFirstFilledOperand :=
  .field (.category (directPath name) categoryName)

private def categoryStar : SurfaceEnumerationFirstFilledOperand :=
  .star starPath (.category "Target")

private def rowPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field := name }

private def filterRef (name : String) : SurfaceHavingNumberRef :=
  { origin := .inner, field := rowPath name }

private def equalFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal (filterRef "FilterLeft") (filterRef "FilterRight")

private def filteredCategoryStar : SurfaceEnumerationFirstFilledOperand :=
  .star starPath (.category "Target") (some equalFilter)

private def document (rows : List RowIndex) : Document :=
  {
    instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none
  }

private def directRead (compatibleCell projectedCell : RawCell) :
    RawFlatContext where
  read field :=
    if field == compatible.id then compatibleCell
    else if field == projected.id then projectedCell
    else .empty

private def starRead (first second third : RawCell)
    (environment : Env) (field : FieldId) : RawCell :=
  if field != repeated.id then
    .empty
  else
    match environment with
    | [(10, 1)] => first
    | [(10, 2)] => second
    | [(10, 3)] => third
    | _ => .empty

private def emptyFilterRead : Env → FieldId → CheckedCell :=
  fun _ _ => formalCheck filterLeft.policy .empty

private def filterRead (left right : List RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  let row := match environment with
    | [(10, current)] => current
    | _ => 0
  let raw :=
    if field == filterLeft.id then left[row - 1]?.getD .empty
    else if field == filterRight.id then right[row - 1]?.getD .empty
    else .empty
  formalCheck filterLeft.policy raw

private def errorOf (authored : SurfaceEnumerationFirstFilledSource) :
    Option EnumerationFirstFilledComputationElabError :=
  match elaborateEnumerationFirstFilledComputation model ["Form"] target.id authored with
  | .ok _ => none
  | .error error => some error

private def outcomeOf (authored : SurfaceEnumerationFirstFilledSource)
    (rows : List RowIndex) (directContext : RawFlatContext)
    (rowRead : Env → FieldId → RawCell)
    (rowFilterRead : Env → FieldId → CheckedCell := emptyFilterRead) :
    Option StringTargetOutcome :=
  match elaborateEnumerationFirstFilledComputation model ["Form"] target.id authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate (document rows) [] directContext rowFilterRead rowRead with
      | .error _ => none
      | .ok outcome => some outcome

/- Direct stored/category operands preserve authored order and exact projected tokens. -/
example :
    outcomeOf (source (direct "Compatible") [category "Projected" "Target"]) []
        (directRead .empty (.parsed (.enum "X"))) (starRead .empty .empty .empty) =
      some (.accepted { text := "A", nonempty := by decide }) := by
  native_decide

/- Exhaustion stays no-value; a first formal error poisons before a later token. -/
example :
    outcomeOf (source (direct "Compatible") [category "Projected" "Target"]) []
        (directRead .empty .empty) (starRead .empty .empty .empty) =
        some .noValue ∧
      outcomeOf (source (direct "Compatible") [category "Projected" "Target"]) []
        (directRead (.rejected .declaredConstraint) (.parsed (.enum "X")))
        (starRead .empty .empty .empty) =
        some (.poison .declaredConstraint) := by
  native_decide

/- A category star projects positionally, and a no-row reached star falls through to a direct fallback. -/
example :
    outcomeOf (source categoryStar []) [1]
        (directRead .empty .empty) (starRead (.parsed (.enum "Y")) .empty .empty) =
        some (.accepted { text := "B", nonempty := by decide }) ∧
      outcomeOf (source categoryStar [direct "Compatible"]) []
        (directRead (.parsed (.enum "A")) .empty)
        (starRead .empty .empty .empty) =
        some (.accepted { text := "A", nonempty := by decide }) := by
  native_decide

/- A terminal direct token prevents malformed later star topology from being resolved. -/
example :
    outcomeOf (source (direct "Compatible") [categoryStar]) [2]
        (directRead (.parsed (.enum "A")) .empty)
        (starRead .empty .empty .empty) =
      some (.accepted { text := "A", nonempty := by decide }) := by
  native_decide

/- Computation `Having` prefetches one kept successor before consuming the current target. An invalid filter while searching for that successor therefore poisons before the first filled token is returned. -/
example :
    outcomeOf (source filteredCategoryStar []) [1, 2]
        (directRead .empty .empty)
        (starRead (.parsed (.enum "X")) .empty .empty)
        (filterRead [number 1, .rejected .malformed] [number 1, number 1]) =
      some (.poison .malformed) := by
  native_decide

/- Once the successor itself is kept, a target-terminal current row prevents any filter beyond that prefetched successor from being read. -/
example :
    outcomeOf (source filteredCategoryStar []) [1, 2, 3]
        (directRead .empty .empty)
        (starRead (.parsed (.enum "Y")) .empty .empty)
        (filterRead [number 1, number 2, .rejected .malformed]
          [number 1, number 2, number 3]) =
      some (.accepted { text := "B", nonempty := by decide }) := by
  native_decide

/- A false row is traversed while searching for the successor, so an invalid filter after it still precedes the current target read. -/
example :
    outcomeOf (source filteredCategoryStar []) [1, 2, 3]
        (directRead .empty .empty)
        (starRead (.parsed (.enum "X")) .empty .empty)
        (filterRead [number 1, number 2, .rejected .malformed]
          [number 1, number 9, number 3]) =
      some (.poison .malformed) := by
  native_decide

/- Operand-level prefix termination remains stronger than filter lookahead: a later filtered slot is never resolved after a direct terminal token. -/
example :
    outcomeOf (source (direct "Compatible") [filteredCategoryStar]) [1, 2]
        (directRead (.parsed (.enum "A")) .empty)
        (starRead .empty .empty .empty)
        (filterRead [.rejected .malformed, number 1] [number 1, number 1]) =
      some (.accepted { text := "A", nonempty := by decide }) := by
  native_decide

/- Whole-domain containment and direct display compatibility are independent per-source gates; categories bypass the latter. -/
example :
    errorOf (source (direct "Wider") [direct "Compatible"]) =
        some (.sourceIncompatible wider.path target.path) ∧
      errorOf (source (direct "Displayed") [direct "Compatible"]) =
        some (.sourceIncompatible displayed.path target.path) ∧
      errorOf (source (category "Projected" "Target") [direct "Compatible"]) =
        none := by
  native_decide

/- Shared entity-list shape, Enumeration kind, and target-reference gates remain static. -/
example :
    errorOf (source (direct "Compatible") []) =
        some (.shape .tooFewFields) ∧
      errorOf (source (direct "Compatible") [direct "Compatible"]) =
        some (.shape (.duplicateOperand compatible.id)) ∧
      errorOf (source (direct "PlainString") [direct "Compatible"]) =
        some (.directSource (.textFieldOperandKindMismatch plainString.path .string)) ∧
      errorOf (source (direct "Target") [direct "Compatible"]) =
        some (.targetSelfReference target.id) := by
  native_decide

end A12Kernel.Conformance.EnumerationFirstFilledComputation
