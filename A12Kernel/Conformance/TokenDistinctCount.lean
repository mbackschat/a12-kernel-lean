import A12Kernel.Elaboration.TokenDistinctCount

/-! # Token distinct-count conformance locks -/

namespace A12Kernel

private def tokenSide (cells : List (ValueListCell .token))
    (hasUninstantiatedTail : Bool := false) (hasHaving : Bool := false) :
    ResolvedValueListSide .token :=
  { cells, hasUninstantiatedTail, hasHaving }

/- String and ordinary stored-Enumeration values share exact token identity. -/
example : evalDistinctCountAggregate
    (tokenSide [.present "A", .present "B", .present "A"]) =
      .value 2 .fixed := by
  native_decide

/- Exact token identity does not case-fold String or Enumeration values. -/
example : evalDistinctCountAggregate
    (tokenSide [.present "A", .present "a"]) =
      .value 2 .fixed := by
  native_decide

/- Empty cells and an omitted tail can add a distinct value but cannot remove one. -/
example :
    evalDistinctCountAggregate (tokenSide [.present "A", .empty]) =
        .value 1 .growOnly ∧
      evalDistinctCountAggregate (tokenSide [.present "A"] true) =
        .value 1 .growOnly := by
  native_decide

/- A reached filter makes the current cardinality movable in both directions. -/
example : evalDistinctCountAggregate
    (tokenSide [.present "A", .present "B"] false true) =
      .value 2 .both := by
  native_decide

/- The first formally unavailable selected cell suppresses the aggregate. -/
example : evalDistinctCountAggregate
    (tokenSide [.present "A", .unknown .declaredConstraint, .present "B"]) =
      .unknown .declaredConstraint := by
  native_decide

private def directString : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Code",
    policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true } }

private def directEnumeration : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Priority",
    policy := { kind := .enumeration },
    enumeration := some { storedTokens := ["A", "B", "A\nB"] } }

private def directNumber : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } } }

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

private def repeatedNumber : FlatFieldDecl :=
  { id := 6
    groupPath := ["Form", "Rows"]
    name := "Guard"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [directString, directEnumeration, directNumber, repeatedString,
      repeatedEnumeration, repeatedNumber]
    repeatableGroups := [{
      level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def directPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form"], field }

private def starPath (field : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field }

private def repeatedPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field }

private def source (first : SurfaceTokenDistinctCountOperand)
    (rest : List SurfaceTokenDistinctCountOperand) :
    SurfaceTokenDistinctCountSource :=
  { first, rest }

private def selfFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := repeatedPath "Guard" }
    { origin := .inner, field := repeatedPath "Guard" }

private def document (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

private def directRead (stringCell enumerationCell : RawCell) :
    FieldId → CheckedCell
  | id =>
      if id == directString.id then directString.checkRaw stringCell
      else if id == directEnumeration.id then
        directEnumeration.checkRaw enumerationCell
      else malformedCheckedCell

private def rowCell (a b c : RawCell) (environment : Env) : RawCell :=
  match environment with
  | [(10, 1)] => a
  | [(10, 2)] => b
  | [(10, 3)] => c
  | _ => .empty

private def starRead (stringCells enumerationCells numberCells : RawCell × RawCell × RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  if field == repeatedString.id then
    repeatedString.checkRaw (rowCell stringCells.1 stringCells.2.1 stringCells.2.2 environment)
  else if field == repeatedEnumeration.id then
    repeatedEnumeration.checkRaw
      (rowCell enumerationCells.1 enumerationCells.2.1 enumerationCells.2.2 environment)
  else if field == repeatedNumber.id then
    repeatedNumber.checkRaw (rowCell numberCells.1 numberCells.2.1 numberCells.2.2 environment)
  else
    malformedCheckedCell

private def emptyCells : RawCell × RawCell × RawCell :=
  (.empty, .empty, .empty)

private def checkedErrorOf (authored : SurfaceTokenDistinctCountSource) :
    Option TokenDistinctCountElabError :=
  match elaborateTokenDistinctCountSource model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def evaluatedOf (authored : SurfaceTokenDistinctCountSource)
    (rows : List RowIndex) (stringCell enumerationCell : RawCell)
    (stringCells enumerationCells numberCells : RawCell × RawCell × RawCell) :
    Option NumericOperand :=
  match elaborateTokenDistinctCountSource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateDistinctValidation (document rows) []
          (directRead stringCell enumerationCell)
          (starRead stringCells enumerationCells numberCells) with
      | .ok result => some result
      | .error _ => none

private def partialOf (authored : SurfaceTokenDistinctCountSource)
    (rows : List RowIndex) (scope : ValidationRelevanceScope)
    (stringCells enumerationCells numberCells : RawCell × RawCell × RawCell) :
    Option PartialValidationAggregateResult :=
  match elaborateTokenDistinctCountSource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartialDistinctValidation (document rows) [] scope
          (directRead .empty .empty)
          (starRead stringCells enumerationCells numberCells) with
      | .ok result => some result
      | .error _ => none

private def directMixed : SurfaceTokenDistinctCountSource :=
  source (.field (directPath "Code")) [.field (directPath "Priority")]

private def stringStar (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceTokenDistinctCountSource :=
  match having with
  | none => source (.star (starPath "Label")) []
  | some filter => source (.starHaving (starPath "Label") filter) []

private def enumerationStar : SurfaceTokenDistinctCountSource :=
  source (.star (starPath "Kind")) []

/- String and ordinary Enumeration share stored-token identity after declaration-owned checking. -/
example : evaluatedOf directMixed [] (.parsed (.str "A")) (.parsed (.enum "A"))
    emptyCells emptyCells emptyCells = some (.value 1 .fixed) := by
  native_decide

/- Evaluated String CRLF normalization happens once before exact token identity. -/
example : evaluatedOf directMixed [] (.parsed (.str "A\r\nB"))
    (.parsed (.enum "A\nB")) emptyCells emptyCells emptyCells =
      some (.value 1 .fixed) := by
  native_decide

/- A complete String star counts exact representatives; an omitted row leaves only grow potential. -/
example :
    evaluatedOf (stringStar) [1, 2, 3] .empty .empty
        ((.parsed (.str "A")), (.parsed (.str "B")), (.parsed (.str "A")))
        emptyCells emptyCells = some (.value 2 .fixed) ∧
      evaluatedOf (stringStar) [1, 2] .empty .empty
        ((.parsed (.str "A")), (.parsed (.str "A")), .empty)
        emptyCells emptyCells = some (.value 1 .growOnly) := by
  native_decide

/- Stored Enumeration uses the same exact-token count without category remapping. -/
example : evaluatedOf enumerationStar [1, 2, 3] .empty .empty emptyCells
    ((.parsed (.enum "A")), (.parsed (.enum "A")), (.parsed (.enum "B")))
    emptyCells = some (.value 2 .fixed) := by
  native_decide

/- A reached formal failure wins in authored cell order. -/
example : evaluatedOf (stringStar) [1, 2, 3] .empty .empty
    ((.parsed (.str "A")), (.rejected .declaredConstraint),
      (.rejected .malformed)) emptyCells emptyCells =
    some (.unknown .declaredConstraint) := by
  native_decide

/- A checked filter selects through the shared route and makes an available count both-directionally fillable. -/
example : evaluatedOf (stringStar (some selfFilter)) [1, 2, 3] .empty .empty
    ((.parsed (.str "A")), (.parsed (.str "B")), (.parsed (.str "A")))
    emptyCells
    ((.parsed (.num 1)), (.parsed (.num 1)), (.parsed (.num 1))) =
      some (.value 2 .both) := by
  native_decide

/- Partial all-rows evaluation requires wildcard/ancestor extent, not enumeration of current rows. -/
example :
    let cells : RawCell × RawCell × RawCell :=
      ((.parsed (.str "A")), (.parsed (.str "B")), (.parsed (.str "A")))
    let concrete := ValidationRelevanceScope.partialSet [
      { path := repeatedString.path,
        indices := [.concrete 1, .concrete 1, .concrete 1] },
      { path := repeatedString.path,
        indices := [.concrete 1, .concrete 2, .concrete 1] },
      { path := repeatedString.path,
        indices := [.concrete 1, .concrete 3, .concrete 1] }]
    let wildcard := ValidationRelevanceScope.partialSet [
      { path := repeatedString.path,
        indices := [.concrete 1, .all, .concrete 1] }]
    partialOf (stringStar) [1, 2, 3] concrete cells emptyCells emptyCells =
        some .nonRelevant ∧
      partialOf (stringStar) [1, 2, 3] wildcard cells emptyCells emptyCells =
        some (.evaluated (.value 2 .fixed)) := by
  native_decide

/- Partial validation skips a locally visible filter before malformed topology or reads. -/
example : partialOf (stringStar (some selfFilter)) [2] .full
    emptyCells emptyCells emptyCells = some .skippedHaving := by
  native_decide

/- Shared shape checking rejects a singleton direct field and repeated direct references; family certification rejects Number. -/
example :
    checkedErrorOf (source (.field (directPath "Code")) []) =
        some (.shape .tooFewFields) ∧
      checkedErrorOf (source (.field (directPath "Code"))
        [.field (directPath "Code")]) =
        some (.shape (.duplicateOperand directString.id)) ∧
      checkedErrorOf (source (.field (directPath "Amount"))
        [.field (directPath "Code")]) =
        some (.fieldKindMismatch directNumber.path .number) := by
  native_decide

/- Wildcard occurrences remain independent authored slots, while the distinct set itself absorbs repeated values. -/
example : evaluatedOf
    (source (.star (starPath "Label")) [.star (starPath "Label")])
    [1, 2, 3] .empty .empty
    ((.parsed (.str "A")), (.parsed (.str "B")), (.parsed (.str "A")))
    emptyCells emptyCells = some (.value 2 .fixed) := by
  native_decide

/- The result scale is exactly integral 0. -/
example :
    (match elaborateTokenDistinctCountSource model ["Form"] directMixed with
    | .ok checked => checked.distinctScaleSummary
    | .error _ => { scale := .unknown, canExpandScale := false }) =
      { scale := .exact 0, canExpandScale := false } := by
  native_decide

end A12Kernel
