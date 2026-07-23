import A12Kernel.Elaboration.TokenValueCount

/-! # Checked String/Enumeration value-count conformance locks -/

namespace A12Kernel

private def directString : FlatFieldDecl :=
  { id := 1
    groupPath := ["Form"]
    name := "Code"
    policy := { kind := .string }
    stringPolicy := { lineBreaksPermitted := true } }

private def directEnumeration : FlatFieldDecl :=
  { id := 2
    groupPath := ["Form"]
    name := "Priority"
    policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["A", "B", "A\nB"] } }

private def directString2 : FlatFieldDecl :=
  { id := 3
    groupPath := ["Form"]
    name := "OtherCode"
    policy := { kind := .string } }

private def repeatedString : FlatFieldDecl :=
  { id := 4
    groupPath := ["Form", "Rows"]
    name := "Label"
    policy := { kind := .string }
    repeatableScope := [10] }

private def repeatedEnumeration : FlatFieldDecl :=
  { id := 5
    groupPath := ["Form", "Rows"]
    name := "Kind"
    policy := { kind := .enumeration }
    enumeration := directEnumeration.enumeration
    repeatableScope := [10] }

private def repeatedGuard : FlatFieldDecl :=
  { id := 6
    groupPath := ["Form", "Rows"]
    name := "Guard"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [directString, directEnumeration, directString2,
      repeatedString, repeatedEnumeration, repeatedGuard]
    repeatableGroups := [{
      level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def directPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form"], field }

private def mixedDirectSource : SurfaceTokenEntitySource :=
  { first := .field (directPath "Code")
    rest := [.field (directPath "Priority")] }

private def directStringsSource : SurfaceTokenEntitySource :=
  { first := .field (directPath "Code")
    rest := [.field (directPath "OtherCode")] }

private def starPath (field : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field }

private def repeatedPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field }

private def selfFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := repeatedPath "Guard" }
    { origin := .inner, field := repeatedPath "Guard" }

private def stringStar (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceTokenEntitySource :=
  match having with
  | none => { first := .star (starPath "Label"), rest := [] }
  | some filter =>
      { first := .starHaving (starPath "Label") filter, rest := [] }

private def enumerationStar : SurfaceTokenEntitySource :=
  { first := .star (starPath "Kind"), rest := [] }

private def checkedError (expected : String) :
    Option TokenValueCountElabError :=
  match elaborateTokenValueCountSource model ["Form"] expected mixedDirectSource with
  | .ok _ => none
  | .error error => some error

private def sourceError (expected : String)
    (authored : SurfaceTokenValueCountSource) :
    Option TokenValueCountElabError :=
  match elaborateTokenValueCountSource model ["Form"] expected authored with
  | .ok _ => none
  | .error error => some error

private def sourceReferences (expected : String)
    (authored : SurfaceTokenValueCountSource) :
    Option (Bool × Bool) :=
  match elaborateTokenValueCountSource model ["Form"] expected authored with
  | .error _ => none
  | .ok checked =>
      some (checked.referencesField repeatedString.id,
        checked.referencesField repeatedGuard.id)

/- A String token is unrestricted while every selected Enumeration must admit the same stored token. -/
example :
    checkedError "A" = none ∧
      checkedError "C" =
        some (.literalOutsideEnumerationDomain directEnumeration.path "C") := by
  native_decide

private def document (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

private def directRead (code enumeration otherCode : RawCell) :
    FieldId → CheckedCell
  | id =>
      if id == directString.id then directString.checkRaw code
      else if id == directEnumeration.id then
        directEnumeration.checkRaw enumeration
      else if id == directString2.id then directString2.checkRaw otherCode
      else malformedCheckedCell

private def rowCell (a b c : RawCell) (environment : Env) : RawCell :=
  match environment with
  | [(10, 1)] => a
  | [(10, 2)] => b
  | [(10, 3)] => c
  | _ => .empty

private def starRead
    (stringCells enumerationCells guardCells : RawCell × RawCell × RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  if field == repeatedString.id then
    repeatedString.checkRaw
      (rowCell stringCells.1 stringCells.2.1 stringCells.2.2 environment)
  else if field == repeatedEnumeration.id then
    repeatedEnumeration.checkRaw
      (rowCell enumerationCells.1 enumerationCells.2.1 enumerationCells.2.2
        environment)
  else if field == repeatedGuard.id then
    repeatedGuard.checkRaw
      (rowCell guardCells.1 guardCells.2.1 guardCells.2.2 environment)
  else
    malformedCheckedCell

private def emptyCells : RawCell × RawCell × RawCell :=
  (.empty, .empty, .empty)

private def evaluatedValidationOf (expected : String)
    (authored : SurfaceTokenValueCountSource) (rows : List RowIndex)
    (code enumeration otherCode : RawCell)
    (stringCells enumerationCells guardCells :
      RawCell × RawCell × RawCell) : Option NumericOperand :=
  match elaborateTokenValueCountSource model ["Form"] expected authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateValidation (document rows) []
          (directRead code enumeration otherCode)
          (starRead stringCells enumerationCells guardCells) with
      | .ok result => some result
      | .error _ => none

private def evaluatedComputationOf (expected : String)
    (authored : SurfaceTokenValueCountSource) (rows : List RowIndex)
    (stringCells enumerationCells guardCells :
      RawCell × RawCell × RawCell) : Option NumericOperand :=
  match elaborateTokenValueCountSource model ["Form"] expected authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateComputation (document rows) []
          (directRead .empty .empty .empty)
          (starRead emptyCells emptyCells guardCells)
          (starRead stringCells enumerationCells guardCells) with
      | .ok result => some result
      | .error _ => none

private def evaluatedPartialOf (expected : String)
    (authored : SurfaceTokenValueCountSource) (rows : List RowIndex)
    (scope : ValidationRelevanceScope)
    (stringCells enumerationCells guardCells :
      RawCell × RawCell × RawCell) :
    Option PartialValidationAggregateResult :=
  match elaborateTokenValueCountSource model ["Form"] expected authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartialValidation (document rows) [] scope
          (directRead .empty .empty .empty)
          (starRead stringCells enumerationCells guardCells) with
      | .ok result => some result
      | .error _ => none

/- String and ordinary Enumeration share exact runtime token identity after declaration-owned checking. -/
example :
    evaluatedValidationOf "A" mixedDirectSource []
      (.parsed (.str "A")) (.parsed (.enum "A")) .empty
      emptyCells emptyCells emptyCells =
        some (.value 2 .fixed) ∧
      evaluatedValidationOf "a" mixedDirectSource []
        (.parsed (.str "A")) (.parsed (.enum "A")) .empty
        emptyCells emptyCells emptyCells = none := by
  native_decide

/- Unrestricted String literals still use exact, case-sensitive token identity. -/
example :
    evaluatedValidationOf "a" directStringsSource []
      (.parsed (.str "A")) .empty (.parsed (.str "A"))
      emptyCells emptyCells emptyCells =
        some (.value 0 .fixed) := by
  native_decide

/- Evaluated String CRLF normalization occurs before comparison with the already-decoded literal and stored Enumeration token. -/
example :
    evaluatedValidationOf "A\nB" mixedDirectSource []
      (.parsed (.str "A\r\nB")) (.parsed (.enum "A\nB")) .empty
      emptyCells emptyCells emptyCells =
        some (.value 2 .fixed) := by
  native_decide

/- Empty cells never match even an empty String constant and retain only growth potential. -/
example :
    evaluatedValidationOf "" directStringsSource []
      .empty .empty (.parsed (.str "X"))
      emptyCells emptyCells emptyCells =
        some (.value 0 .growOnly) := by
  native_decide

/- A complete star counts exact matches, while an omitted declared row can add a future match. -/
example :
    evaluatedValidationOf "A" (stringStar) [1, 2, 3]
        .empty .empty .empty
        ((.parsed (.str "A")), (.parsed (.str "B")),
          (.parsed (.str "A"))) emptyCells emptyCells =
      some (.value 2 .fixed) ∧
    evaluatedValidationOf "A" (stringStar) [1, 2]
        .empty .empty .empty
        ((.parsed (.str "A")), (.parsed (.str "A")), .empty)
        emptyCells emptyCells =
      some (.value 2 .growOnly) := by
  native_decide

/- Filter provenance remains per selected cell in validation and computation: only a selected current match can later shrink the count. -/
example :
    let allSelected : RawCell × RawCell × RawCell :=
      ((.parsed (.num 1)), (.parsed (.num 1)), (.parsed (.num 1)))
    sourceReferences "A" (stringStar (some selfFilter)) =
        some (true, true) ∧
    evaluatedValidationOf "A" (stringStar (some selfFilter)) [1]
        .empty .empty .empty
        ((.parsed (.str "A")), .empty, .empty) emptyCells allSelected =
      some (.value 1 .both) ∧
    evaluatedValidationOf "A" (stringStar (some selfFilter)) [1]
        .empty .empty .empty
        ((.parsed (.str "B")), .empty, .empty) emptyCells allSelected =
      some (.value 0 .growOnly) ∧
    evaluatedComputationOf "A" (stringStar (some selfFilter)) [1]
        ((.parsed (.str "A")), .empty, .empty) emptyCells allSelected =
      some (.value 1 .both) ∧
    evaluatedComputationOf "A" (stringStar (some selfFilter)) [1]
        ((.parsed (.str "B")), .empty, .empty) emptyCells allSelected =
      some (.value 0 .growOnly) := by
  native_decide

/- Computation retains the shared one-kept-successor traversal: poison while seeking the successor precedes the pending selected target. -/
example :
    let guarded : RawCell × RawCell × RawCell :=
      ((.parsed (.num 1)), (.rejected .declaredConstraint), .empty)
    evaluatedComputationOf "A" (stringStar (some selfFilter)) [1, 2]
      ((.parsed (.str "A")), .empty, .empty) emptyCells guarded =
        some (.unknown .declaredConstraint) := by
  native_decide

/- The first reached formal failure owns the result before later matching cells. -/
example :
    evaluatedComputationOf "A" (stringStar) [1, 2, 3]
      ((.rejected .declaredConstraint), (.parsed (.str "A")),
        (.rejected .malformed)) emptyCells emptyCells =
        some (.unknown .declaredConstraint) := by
  native_decide

/- Partial evaluation requires wildcard/ancestor extent and skips a filtered rule before target reads. -/
example :
    let cells : RawCell × RawCell × RawCell :=
      ((.parsed (.str "A")), (.parsed (.str "B")), (.parsed (.str "A")))
    let concrete := ValidationRelevanceScope.partialSet [
      { path := repeatedString.path,
        indices := [.concrete 1, .concrete 1, .concrete 1] }]
    let wildcard := ValidationRelevanceScope.partialSet [
      { path := repeatedString.path,
        indices := [.concrete 1, .all, .concrete 1] }]
    evaluatedPartialOf "A" (stringStar) [1, 2, 3] concrete
        cells emptyCells emptyCells = some .nonRelevant ∧
      evaluatedPartialOf "A" (stringStar) [1, 2, 3] wildcard
        cells emptyCells emptyCells =
          some (.evaluated (.value 2 .fixed)) ∧
      evaluatedPartialOf "A" (stringStar (some selfFilter)) [2]
        .full emptyCells emptyCells emptyCells =
          some .skippedHaving := by
  native_decide

/- A stored-Enumeration star uses exact token identity and still rejects an authored literal outside its declaration domain. -/
example :
    evaluatedValidationOf "A" enumerationStar [1, 2, 3]
        .empty .empty .empty emptyCells
        ((.parsed (.enum "A")), (.parsed (.enum "B")),
          (.parsed (.enum "A"))) emptyCells =
      some (.value 2 .fixed) ∧
    sourceError "C" enumerationStar =
      some (.literalOutsideEnumerationDomain repeatedEnumeration.path "C") := by
  native_decide

end A12Kernel
