import A12Kernel.Elaboration.StringPattern

/-! # Checked authored String-pattern conformance locks -/

namespace A12Kernel.Conformance.StringPatternElaboration

open A12Kernel

private def stringDeclaration : FlatFieldDecl :=
  { id := 1
    groupPath := ["Claim"]
    name := "Code"
    policy := { kind := .string } }

private def numberDeclaration : FlatFieldDecl :=
  { id := 2
    groupPath := ["Claim"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } } }

private def model : FlatModel :=
  { fields := [stringDeclaration, numberDeclaration] }

private def lineBreakModel : FlatModel :=
  { fields := [{
      stringDeclaration with
      stringPolicy := { lineBreaksPermitted := true } }] }

private def fieldPath (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def exactUpper (value : String) : Bool := value == "ABC"

private def compilePattern (source : String) : Option (String → Bool) :=
  if source == "[A-Z]{3}" then some exactUpper
  else if source == "(" then none
  else some fun _ => false

private def compileNormalized (source : String) : Option (String → Bool) :=
  if source == "AB\\sCD" then some fun value => value == "AB\nCD" else none

private def compileDeclared (source : String) : Option (String → Bool) :=
  if source == "[A-Z]+" then
    some fun value => !value.isEmpty && value.toList.all (fun character =>
      'A' ≤ character && character ≤ 'Z')
  else if source == "[0-9]+" then
    some matchesAsciiDigitsPattern
  else if source == "A" then
    some fun value => value == "A"
  else if source == "B" then
    some fun value => value == "B"
  else
    none

private def condition (source : String := "[A-Z]{3}")
    (op : StringPatternOp := .matched) : SurfaceStringPatternCondition :=
  { op, field := fieldPath "Code", source }

private def raw (value : RawCell) : RawFlatContext where
  read id := if id == 1 then value else .empty

private def normalizedResult : Option Verdict :=
  match elaborateStringPatternCondition compileNormalized lineBreakModel ["Claim"]
      (condition "AB\\sCD") with
  | .error _ => none
  | .ok checked =>
      some (checked.evalFull (raw (.parsed (.str "AB\r\nCD"))) true)

private def errorOf :
    Except StringPatternConditionElabError α → Option StringPatternConditionElabError
  | .ok _ => none
  | .error error => some error

private def verdictOf (cell : RawCell) (hasContent : Bool) :
    Except StringPatternConditionElabError
      (CheckedStringPatternCondition model compilePattern) → Option Verdict
  | .error _ => none
  | .ok checked => some (checked.evalFull (raw cell) hasContent)

example : verdictOf (.parsed (.str "ABC")) true
    (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition)) = some (.fired .value) := by native_decide

example : verdictOf (.parsed (.str "xyz")) true
    (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition (op := .violated))) = some (.fired .value) := by native_decide

/- Empty fields and all-empty rows cannot fire a pattern condition. -/
example :
    verdictOf .empty true
        (elaborateStringPatternCondition compilePattern model ["Claim"]
          (condition)) = some .notFired ∧
      verdictOf (.parsed (.str "ABC")) false
        (elaborateStringPatternCondition compilePattern model ["Claim"]
          (condition)) = some .notFired := by
  native_decide

/- The model-owned raw checker preserves formal unavailability before pattern execution. -/
example : verdictOf (.rejected .declaredConstraint) true
    (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition)) = some .unknown := by native_decide

/- Checked elaboration reaches the same once-normalized String cached by declaration-owned formal checking. -/
example : normalizedResult = some (.fired .value) := by native_decide

example :
    errorOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      { op := .matched, field := fieldPath "Amount", source := "[A-Z]{3}" }) =
        some (.fieldKind ["Claim", "Amount"] .number) ∧
    errorOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition "(")) =
        some (.pattern .javaSyntax) ∧
    errorOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition "a++")) =
        some (.pattern .kernelRestriction) := by
  native_decide

/- Raw, registered-custom, arbitrary declared-pattern, and repeatable fields remain explicit unchecked-context boundaries. -/
example :
    let rawDecl := {
      stringDeclaration with
      stringValueMode := .raw
      stringPolicy := { lineBreaksPermitted := true } }
    let customDecl := {
      stringDeclaration with customType := some { name := "ProjectCode" } }
    let patternDecl := {
      stringDeclaration with stringPatternSource := some "[A-Z]*" }
    let repeatableDecl := {
      stringDeclaration with
      groupPath := ["Claim", "Items"]
      repeatableScope := [10] }
    let repeatableModel : FlatModel := {
      fields := [repeatableDecl]
      repeatableGroups := [{ level := 10, path := ["Claim", "Items"] }] }
    errorOf (elaborateStringPatternCondition compilePattern
      { fields := [rawDecl] } ["Claim"] (condition)) =
        some (.rawStringValue ["Claim", "Code"]) ∧
    errorOf (elaborateStringPatternCondition compilePattern
      { fields := [customDecl] } ["Claim"] (condition)) =
        some (.preparedCustomFieldRequired ["Claim", "Code"]) ∧
    errorOf (elaborateStringPatternCondition compilePattern
      { fields := [patternDecl] } ["Claim"] (condition)) =
        some (.declaredPatternRequiresPreparation ["Claim", "Code"]) ∧
    errorOf (elaborateStringPatternCondition compilePattern
      repeatableModel ["Claim", "Items"] (condition)) =
        some (.fieldReference (.repeatableReference ["Claim", "Items", "Code"])) := by
  native_decide

private def preparedCell (model : FlatModel) (field : FieldId)
    (raw : RawCell) : Option CheckedCell :=
  match prepareDeclaredStringField compileDeclared model field with
  | .error _ => none
  | .ok prepared => some (prepared.checkRaw raw)

private def declaredPatternErrorOf :
    Except DeclaredStringPatternElabError α →
      Option DeclaredStringPatternElabError
  | .ok _ => none
  | .error error => some error

/- Arbitrary admitted declaration patterns now have one compiler-associated formal-check route. Pattern mismatch wins before both length directions. -/
example :
    let declaration := {
      stringDeclaration with
      stringPolicy := { minLength := some 3, maxLength := some 5 }
      stringPatternSource := some "[A-Z]+" }
    let declaredModel : FlatModel := { fields := [declaration] }
    preparedCell declaredModel 1 (.parsed (.str "ABC")) =
        some {
          rawPresent := true
          parsed := some (.str "ABC")
          findings := [] } ∧
      preparedCell declaredModel 1 (.parsed (.str "a")) =
        some {
          rawPresent := true
          parsed := none
          findings := [.declaredConstraint] } ∧
      preparedCell declaredModel 1 (.parsed (.str "abcdef")) =
        some {
          rawPresent := true
          parsed := none
          findings := [.declaredConstraint] } := by
  native_decide

/- Exact source association prevents the matcher prepared for one declaration from validating the other. -/
example :
    let declarationA := {
      stringDeclaration with
      stringPatternSource := some "A" }
    let declarationB := {
      stringDeclaration with
      id := 3
      name := "OtherCode"
      stringPatternSource := some "B" }
    let declaredModel : FlatModel := {
      fields := [declarationA, declarationB] }
    preparedCell declaredModel 1 (.parsed (.str "A")) =
        some {
          rawPresent := true
          parsed := some (.str "A")
          findings := [] } ∧
      preparedCell declaredModel 1 (.parsed (.str "B")) =
        some {
          rawPresent := true
          parsed := none
          findings := [.declaredConstraint] } ∧
      preparedCell declaredModel 3 (.parsed (.str "B")) =
        some {
          rawPresent := true
          parsed := some (.str "B")
          findings := [] } := by
  native_decide

/- An absent or empty declared source is an inactive field pattern. In particular, the empty declaration source does not invoke the injected compiler. -/
example :
    let plainModel : FlatModel := { fields := [stringDeclaration] }
    let emptyPatternModel : FlatModel := {
      fields := [{
        stringDeclaration with stringPatternSource := some "" }] }
    preparedCell plainModel 1 (.parsed (.str "anything")) =
        some {
          rawPresent := true
          parsed := some (.str "anything")
          findings := [] } ∧
      preparedCell emptyPatternModel 1 (.parsed (.str "anything")) =
        some {
          rawPresent := true
          parsed := some (.str "anything")
          findings := [] } := by
  native_decide

/- Model legality precedes compiler admission; valid ordinary fields retain the exact failed compiler/admission stage. -/
example :
    let rawPattern := {
      stringDeclaration with
      stringValueMode := .raw
      stringPolicy := { lineBreaksPermitted := true }
      stringPatternSource := some "A" }
    let invalidSource := {
      stringDeclaration with stringPatternSource := some "(" }
    let restrictedSource := {
      stringDeclaration with stringPatternSource := some "a++" }
    declaredPatternErrorOf
        (prepareDeclaredStringField compileDeclared
          { fields := [rawPattern] } 1) =
          some (.model (.rawStringForbidsPattern ["Claim", "Code"])) ∧
      declaredPatternErrorOf
        (prepareDeclaredStringField compileDeclared
          { fields := [invalidSource] } 1) =
          some (.pattern .javaSyntax) ∧
      declaredPatternErrorOf
        (prepareDeclaredStringField (fun _ => some fun _ => false)
          { fields := [restrictedSource] } 1) =
          some (.pattern .kernelRestriction) := by
  native_decide

/- The existing executable numeric specialization and the prepared general route agree on accepted and rejected cells. -/
example :
    let declaration := {
      stringDeclaration with stringPatternSource := some "[0-9]+" }
    let declaredModel : FlatModel := { fields := [declaration] }
    preparedCell declaredModel 1 (.parsed (.str "123")) =
        some (declaration.checkRaw (.parsed (.str "123"))) ∧
      preparedCell declaredModel 1 (.parsed (.str "12A")) =
        some (declaration.checkRaw (.parsed (.str "12A"))) := by
  native_decide

end A12Kernel.Conformance.StringPatternElaboration
