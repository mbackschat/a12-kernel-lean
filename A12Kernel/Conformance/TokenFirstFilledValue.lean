import A12Kernel.Elaboration.TokenFirstFilledValue

/-! # Token `FirstFilledValue` conformance locks -/

namespace A12Kernel

private def tokenSide (cells : List (ValueListCell .token))
    (hasUninstantiatedTail : Bool := false) (hasHaving : Bool := false) :
    ResolvedValueListSide .token :=
  { cells, hasUninstantiatedTail, hasHaving }

/- The first exact token wins and hides the suffix. -/
example : evalFirstFilledToken
    (tokenSide [.present "A", .unknown .malformed]) =
      .value "A" false := by
  native_decide

/- An empty prefix is retained on a later selected token. -/
example : evalFirstFilledToken
    (tokenSide [.empty, .present "A"]) =
      .value "A" true := by
  native_decide

/- A first formal failure terminates before a later token. -/
example : evalFirstFilledToken
    (tokenSide [.unknown .declaredConstraint, .present "A"]) =
      .unavailable .declaredConstraint := by
  native_decide

/- Unlike Number, an exhausted token family has no synthetic value. -/
example :
    evalFirstFilledToken (tokenSide [.empty]) = .noValue ∧
      evalFirstFilledToken (tokenSide [] true) = .noValue := by
  native_decide

/- Validation retains prefix polarity while computation retains only the selected token. -/
example :
    (evalFirstFilledToken
      (tokenSide [.empty, .present "A"])).asValidationOperand =
        .value "A" false ∧
      (evalFirstFilledToken
        (tokenSide [.empty, .present "A"])).asComputationResult =
        .value "A" := by
  native_decide

/- A reached filter marks a later token not-given; a terminal earlier token hides a later filter. -/
example :
    evalFirstFilledTokenOperands {
      first := tokenSide [] false true
      rest := [tokenSide [.present "A"]] } = .value "A" true ∧
    evalFirstFilledTokenOperands {
      first := tokenSide [.present "A"]
      rest := [tokenSide [.present "B"] false true] } = .value "A" false := by
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

private def repeatedNumber : FlatFieldDecl :=
  { id := 5
    groupPath := ["Form", "Rows"]
    name := "Guard"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [directString, directEnumeration, directNumber, repeatedString,
      repeatedNumber]
    repeatableGroups := [{
      level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def directPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form"], field }

private def repeatedPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field }

private def starPath (field : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field }

private def source (first : SurfaceFirstFilledTokenOperand)
    (rest : List SurfaceFirstFilledTokenOperand) :
    SurfaceFirstFilledTokenSource :=
  { first, rest }

private def directMixed : SurfaceFirstFilledTokenSource :=
  source (.field (directPath "Code")) [.field (directPath "Priority")]

private def stringStar (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceFirstFilledTokenSource :=
  match having with
  | none => source (.star (starPath "Label")) []
  | some filter => source (.starHaving (starPath "Label") filter) []

private def starThenEnumeration : SurfaceFirstFilledTokenSource :=
  source (.star (starPath "Label")) [.field (directPath "Priority")]

private def directThenStar : SurfaceFirstFilledTokenSource :=
  source (.field (directPath "Code")) [.star (starPath "Label")]

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

private def starRead (stringCells numberCells : RawCell × RawCell × RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  if field == repeatedString.id then
    repeatedString.checkRaw
      (rowCell stringCells.1 stringCells.2.1 stringCells.2.2 environment)
  else if field == repeatedNumber.id then
    repeatedNumber.checkRaw
      (rowCell numberCells.1 numberCells.2.1 numberCells.2.2 environment)
  else
    malformedCheckedCell

private def emptyCells : RawCell × RawCell × RawCell :=
  (.empty, .empty, .empty)

private def checkedErrorOf (authored : SurfaceFirstFilledTokenSource) :
    Option FirstFilledTokenElabError :=
  match elaborateFirstFilledTokenSource model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def evaluatedOf (authored : SurfaceFirstFilledTokenSource)
    (rows : List RowIndex) (scope : ValidationRelevanceScope)
    (stringCell enumerationCell : RawCell)
    (stringCells numberCells : RawCell × RawCell × RawCell) :
    Option PartialValidationFirstFilledTokenResult :=
  match elaborateFirstFilledTokenSource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartialFirstFilledValidation (document rows) [] scope
          (directRead stringCell enumerationCell) (starRead stringCells numberCells) with
      | .ok result => some result
      | .error _ => none

/- The checked boundary admits mixed String/stored-Enumeration slots and preserves an empty prefix on the selected token. -/
example : evaluatedOf directMixed [] .full .empty (.parsed (.enum "A"))
    emptyCells emptyCells = some (.evaluated (.value "A" true)) := by
  native_decide

/- A first token hides malformed later input, and evaluated String normalization occurs before selection. -/
example :
    evaluatedOf directMixed [] .full (.parsed (.str "A\r\nB"))
        (.rejected .malformed) emptyCells emptyCells =
      some (.evaluated (.value "A\nB" false)) := by
  native_decide

/- A reached formal failure terminates before a later stored token. -/
example : evaluatedOf directMixed [] .full (.rejected .declaredConstraint)
    (.parsed (.enum "A")) emptyCells emptyCells =
      some (.evaluated (.unavailable .declaredConstraint)) := by
  native_decide

/- Exhausting checked direct token slots produces no synthetic token. -/
example : evaluatedOf directMixed [] .full .empty .empty emptyCells emptyCells =
    some (.evaluated .noValue) := by
  native_decide

/- Star rows are scanned in encounter order; a cell-free reached star remains an empty prefix before a later direct token. -/
example :
    evaluatedOf (stringStar) [1, 2] .full .empty .empty
        (.empty, .parsed (.str "B"), .empty) emptyCells =
      some (.evaluated (.value "B" true)) ∧
    evaluatedOf starThenEnumeration [] .full .empty (.parsed (.enum "A"))
        emptyCells emptyCells = some (.evaluated (.value "A" true)) := by
  native_decide

/- A terminal direct token hides malformed later star topology; after an empty prefix that same topology is reached and fails closed. -/
example :
    evaluatedOf directThenStar [2] .full (.parsed (.str "A")) .empty
        emptyCells emptyCells = some (.evaluated (.value "A" false)) ∧
      evaluatedOf directThenStar [2] .full .empty .empty
        emptyCells emptyCells = none := by
  native_decide

/- A reached filter contributes not-given polarity to its selected token. -/
example : evaluatedOf (stringStar (some selfFilter)) [1] .full .empty .empty
    (.parsed (.str "A"), .empty, .empty)
    (.parsed (.num 1), .empty, .empty) =
      some (.evaluated (.value "A" true)) := by
  native_decide

/- Partial relevance is checked before classifying the reached target cell. -/
example : evaluatedOf (stringStar) [1] (.partialSet []) .empty .empty
    (.rejected .malformed, .empty, .empty) emptyCells =
      some .nonRelevant := by
  native_decide

/- Shared entity-list shape rejects a singleton direct field and duplicate direct references; token certification rejects Number. -/
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

end A12Kernel
