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
    enumeration := some {
      storedTokens := ["A", "B", "A\nB"]
      categories := [{ name := "Band", tokens := ["HIGH", "LOW", "MULTI"] }] } }

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

private def rawString : FlatFieldDecl :=
  { id := 6
    groupPath := ["Form"]
    name := "Raw"
    policy := { kind := .string }
    stringValueMode := .raw
    stringPolicy := { lineBreaksPermitted := true } }

private def rawGroupString : FlatFieldDecl :=
  { rawString with id := 7, groupPath := ["Form", "RawMixed"] }

private def rawGroupNumber : FlatFieldDecl :=
  { directNumber with id := 8, groupPath := ["Form", "RawMixed"] }

private def repeatedEnumeration : FlatFieldDecl :=
  { id := 9
    groupPath := ["Form", "Rows"]
    name := "Kind"
    policy := { kind := .enumeration }
    enumeration := directEnumeration.enumeration
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [directString, directEnumeration, directNumber, repeatedString,
      repeatedNumber, rawString, rawGroupString, rawGroupNumber,
      repeatedEnumeration]
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

private def fixedGroup (groups : GroupPath) : SurfaceFirstFilledTokenSource :=
  source (.group (.path { base := .absolute, groups })) []

private def directMixed : SurfaceFirstFilledTokenSource :=
  source (.field (directPath "Code")) [.field (directPath "Priority")]

private def stringStar (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceFirstFilledTokenSource :=
  match having with
  | none => source (.star (starPath "Label")) []
  | some filter => source (.starHaving (starPath "Label") filter) []

private def starThenEnumeration : SurfaceFirstFilledTokenSource :=
  source (.star (starPath "Label")) [.field (directPath "Priority")]

private def enumerationStar : SurfaceFirstFilledTokenSource :=
  source (.star (starPath "Kind")) []

private def directThenStar : SurfaceFirstFilledTokenSource :=
  source (.field (directPath "Code")) [.star (starPath "Label")]

private def selfFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := repeatedPath "Guard" }
    { origin := .inner, field := repeatedPath "Guard" }

private def allRowsFilter : SurfaceCorrelatedHaving :=
  let group : SurfaceGroupReference := .path {
    base := .absolute
    groups := ["Form", "Rows"] }
  .compareRepetitions .equal
    { origin := .inner, group }
    { origin := .inner, group }

private def filteredStarThenEnumeration : SurfaceFirstFilledTokenSource :=
  source (.starHaving (starPath "Label") allRowsFilter)
    [.field (directPath "Priority")]

private def projectedCategorySource : SurfaceProjectedTokenEntitySource :=
  { first := .field (.category (directPath "Priority") "Band")
    rest := [.field (.direct (directPath "Code"))] }

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

private def checkedPrepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def checkedRow (index : Nat) : RowAddr :=
  { group := 10, path := [index] }

private def checkedDirectEnumerationCell (value : String) : ClassifiedCellInput :=
  { address := { field := directEnumeration.id, path := [] }
    stored := value
    raw := .parsed (.enum value) }

private def checkedDirectStringCell (value : String) : ClassifiedCellInput :=
  { address := { field := directString.id, path := [] }
    stored := value
    raw := .parsed (.str value) }

private def checkedRepeatedStringCell
    (index : Nat) (raw : RawCell) (stored : String) : ClassifiedCellInput :=
  { address := { field := repeatedString.id, path := [index] }
    stored
    raw }

private def checkedRepeatedEnumerationCell
    (index : Nat) (value : String) : ClassifiedCellInput :=
  { address := { field := repeatedEnumeration.id, path := [index] }
    stored := value
    raw := .parsed (.enum value) }

private def evaluatedCheckedOf (authored : SurfaceFirstFilledTokenSource)
    (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (Option FirstFilledTokenResult) := do
  let checked ← (elaborateFirstFilledTokenSource model ["Form"] authored).toOption
  let document ← (checkDocument checkedPrepared "en_US" {
    instantiatedRows := (List.range rowCount).map fun index =>
      checkedRow (index + 1)
    cells }).toOption
  (checked.evaluateCheckedDirectStarFirstFilledValidation? document []).toOption

private def projectedCategorySupport : Option Bool := do
  let checked ←
    (elaborateProjectedTokenEntitySource model ["Form"]
      projectedCategorySource).toOption
  pure checked.supportsCheckedDirectStarFirstFilledValidation

private def checkedErrorOf (authored : SurfaceFirstFilledTokenSource) :
    Option FirstFilledTokenElabError :=
  match elaborateFirstFilledTokenSource model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def diagnosticOf (authored : SurfaceFirstFilledTokenSource) :
    Option KernelStaticDiagnostic :=
  match elaborateFirstFilledTokenSource model ["Form"] authored with
  | .ok _ => none
  | .error error => error.diagnostic?

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

/- Checked full validation excludes the over-limit-only token before the lazy scan, reaches the
   direct fallback with not-given polarity, and still lets an in-capacity token hide that fallback. -/
example :
    evaluatedCheckedOf starThenEnumeration 4 [
      checkedDirectEnumerationCell "B",
      checkedRepeatedStringCell 4 (.parsed (.str "A")) "A"] =
        some (some (.value "B" true)) ∧
      evaluatedCheckedOf starThenEnumeration 4 [
        checkedDirectEnumerationCell "B",
        checkedRepeatedStringCell 1 (.parsed (.str "A")) "A"] =
          some (some (.value "A" false)) := by
  native_decide

/- The route admits a stored Enumeration star, keeps capacity exclusion distinct from semantic
   exhaustion, and rejects a category-projected source before evaluation. -/
example :
    evaluatedCheckedOf enumerationStar 4 [
      checkedRepeatedEnumerationCell 4 "A"] =
        some (some .noValue) ∧
      evaluatedCheckedOf enumerationStar 4 [
        checkedRepeatedEnumerationCell 1 "A"] =
          some (some (.value "A" false)) ∧
      projectedCategorySupport = some false := by
  native_decide

/- A cell-independent true filter proves the over-limit token was selected before capacity removes
   it; the in-capacity control proves the same filter can still select a deciding token. -/
example :
    evaluatedCheckedOf filteredStarThenEnumeration 4 [
      checkedDirectEnumerationCell "B",
      checkedRepeatedStringCell 4 (.parsed (.str "A")) "A"] =
        some (some (.value "B" true)) ∧
      evaluatedCheckedOf filteredStarThenEnumeration 4 [
        checkedDirectEnumerationCell "B",
        checkedRepeatedStringCell 1 (.parsed (.str "A")) "A"] =
          some (some (.value "A" true)) := by
  native_decide

/- A terminal direct value hides a later checked star failure; removing that prefix reaches the
   same formal cell and keeps it distinct from clean exhaustion. -/
example :
    evaluatedCheckedOf directThenStar 1 [
      checkedDirectStringCell "A",
      checkedRepeatedStringCell 1 (.rejected .malformed) "bad"] =
        some (some (.value "A" false)) ∧
      evaluatedCheckedOf directThenStar 1 [
        checkedRepeatedStringCell 1 (.rejected .malformed) "bad"] =
          some (some (.unavailable .malformed)) := by
  native_decide

/- Partial relevance is checked before classifying the reached target cell. -/
example : evaluatedOf (stringStar) [1] (.partialSet []) .empty .empty
    (.rejected .malformed, .empty, .empty) emptyCells =
      some .nonRelevant := by
  native_decide

/- Shared entity-list shape rejects a singleton direct field and duplicate direct references; only
   the measured direct String/Number order receives `FirstFilledValue`'s heterogeneous-list refusal. -/
example :
    checkedErrorOf (source (.field (directPath "Code")) []) =
        some (.source (.shape .tooFewFields)) ∧
      checkedErrorOf (source (.field (directPath "Code"))
        [.field (directPath "Code")]) =
        some (.source (.shape (.duplicateOperand directString.id))) ∧
      checkedErrorOf (source (.field (directPath "Code"))
        [.field (directPath "Amount")]) =
        some (.stringNumberPair directString.path directNumber.path) := by
  native_decide

/- The measured direct-field projection does not transfer to the reverse order or to starred
   carriers merely because their flattened declaration kinds are the same. -/
example :
    checkedErrorOf (source (.field (directPath "Amount"))
      [.field (directPath "Code")]) =
        some (.source (.fieldKindMismatch directNumber.path .number)) ∧
    diagnosticOf (source (.field (directPath "Amount"))
      [.field (directPath "Code")]) = none ∧
    checkedErrorOf (source (.star (starPath "Label"))
      [.star (starPath "Guard")]) =
        some (.source (.fieldKindMismatch repeatedNumber.path .number)) ∧
    diagnosticOf (source (.star (starPath "Label"))
      [.star (starPath "Guard")]) = none := by
  native_decide

/- A raw String shares the String surface kind but has no readable stored-token value, so neither
   the direct pair nor the equivalent fixed-group carrier borrows the ordinary String diagnostic. -/
example :
    checkedErrorOf (source (.field (directPath "Raw"))
      [.field (directPath "Amount")]) =
        some (.source (.rawStringValue rawString.path)) ∧
    diagnosticOf (source (.field (directPath "Raw"))
      [.field (directPath "Amount")]) = none ∧
    checkedErrorOf (fixedGroup ["Form", "RawMixed"]) =
        some (.source (.group (.expansionNotToken ["Form", "RawMixed"]))) ∧
    diagnosticOf (fixedGroup ["Form", "RawMixed"]) = none := by
  native_decide

end A12Kernel
