import A12Kernel.Elaboration.StringPattern
import A12Kernel.Elaboration.ValidationCondition.Assembly
import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.ValidationCondition.Reference

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

/-- The eighth left kind. DATE_RANGE was the one kind the 22-case admission matrix did not carry,
    and it draws the same class as the other seven — so the gate is total over the left kinds rather
    than a set of measured ones
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-pattern-comparison-left-kind-gate-is-total)). -/
private def dateRangeDeclaration : FlatFieldDecl :=
  { id := 3
    groupPath := ["Claim"]
    name := "Span"
    policy := { kind := .dateRange }
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def model : FlatModel :=
  { fields := [stringDeclaration, numberDeclaration, dateRangeDeclaration] }

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

private def uppercaseCases : List (String × Bool) := [
  ("", false), ("A", true), ("Z", true), ("AZBY", true), ("a", false),
  ("@", false), ("[", false), ("A1", false), ("1A", false), ("A Z", false),
  ("Å", false), ("Ａ", false), ("𝔄", false), ("A\n", false), ("A\r\n", false)]

example : (builtinStringPatternCompiler "[A-Z]+").map (fun matcher =>
    uppercaseCases.all fun (value, expected) => matcher value == expected) = some true := by native_decide

example : (builtinStringPatternCompiler "[0-9]+").map (fun matcher =>
    [("", false), ("0", true), ("9", true), ("0129", true), ("/", false),
      (":", false), ("١", false), ("１", false), ("1A", false)].all
      fun (value, expected) => matcher value == expected) = some true := by native_decide

example : ["[A-Z]*", "[A-Z]{3}", "[a-z]+", "[A-Za-z]+", "[A-Z]+$", "("].all
    (fun source => (builtinStringPatternCompiler source).isNone) = true := by native_decide

example : [StringPatternOp.matched, .violated].all (fun op =>
    ["ABC", "abc", ""].all fun value =>
      (elaborateAndEvalStringPatternFull builtinStringPatternCompiler model ["Claim"]
        (raw (.parsed (.str value))) true (condition "[A-Z]+" op)).toOption ==
      some (if value.isEmpty then Verdict.notFired else
        if op.acceptsMatchResult (value == "ABC") then .fired .value else .notFired)) = true := by native_decide

example : [StringPatternOp.matched, .violated].all (fun op =>
    (elaborateAndEvalStringPatternFull builtinStringPatternCompiler model ["Claim"]
      (raw (.rejected .declaredConstraint)) true (condition "[A-Z]+" op)).toOption ==
    some .unknown) = true := by native_decide

example :
    let declared : FlatModel := { fields := [{ stringDeclaration with stringPatternSource := some "[A-Z]+" }] }
    (elaborateAndEvalStringPatternFull builtinStringPatternCompiler declared ["Claim"]
      (raw (.parsed (.str "ABC"))) true (condition "[0-9]+" .violated)).toOption == some (.fired .value) &&
    (elaborateAndEvalStringPatternFull builtinStringPatternCompiler declared ["Claim"]
      (raw (.parsed (.str "123"))) true (condition "[0-9]+" .matched)).toOption == some .unknown = true := by native_decide

private def normalizedResult : Option Verdict :=
  match elaborateAndEvalStringPatternFull compileNormalized lineBreakModel ["Claim"]
      (raw (.parsed (.str "AB\r\nCD"))) true (condition "AB\\sCD") with
  | .error _ => none
  | .ok verdict => some verdict

private def errorOf :
    Except StringPatternConditionElabError α → Option StringPatternConditionElabError
  | .ok _ => none
  | .error error => some error

private def diagnosticOf :
    Except StringPatternConditionElabError α → Option KernelStaticDiagnostic
  | .ok _ => none
  | .error error => StringPatternConditionElabError.diagnostic? error

private def verdictOf (cell : RawCell) (hasContent : Bool) :
    Except StringPatternConditionElabError
      (CheckedStringPatternCondition model compilePattern) → Option Verdict
  | .error _ => none
  | .ok checked =>
      match prepareFlatStringContext { now := { epochMillis := 0 } } compilePattern model with
      | .error _ => none
      | .ok prepared =>
          some (checked.evalFull prepared (raw cell) hasContent)

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

/- Pattern-source stages share one exact Kernel class, the measured wrong-left-kind class stays
distinct, and a raw field is the field-value read's raw refusal
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)). -/
example :
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition)) = none ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      { op := .matched, field := fieldPath "Amount", source := "[A-Z]{3}" }) =
        some .invalidTypeForPatternComparison ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      { op := .violated, field := fieldPath "Amount", source := "[A-Z]{3}" }) =
        some .invalidTypeForPatternComparison ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition "(")) = some .invalidPattern ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      (condition "a++")) = some .invalidPattern ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      { op := .matched, field := fieldPath "Span", source := "[A-Z]{3}" }) =
        some .invalidTypeForPatternComparison ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern model ["Claim"]
      { op := .violated, field := fieldPath "Span", source := "[A-Z]{3}" }) =
        some .invalidTypeForPatternComparison ∧
    let rawDecl := {
      stringDeclaration with
      stringValueMode := .raw
      stringPolicy := { lineBreaksPermitted := true } }
    diagnosticOf (elaborateStringPatternCondition compilePattern
      { fields := [rawDecl] } ["Claim"] (condition)) = some .rawTypeOperandInvalid := by
  native_decide

/- The field operand's resolution owns its classes, as on every other carrier measured: a miss by the
   segment that missed, a walk above the root, and a bare name matching several fields
   ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)). -/
example :
    let tagIn (group : String) : FlatFieldDecl :=
      { stringDeclaration with id := if group == "Info" then 4 else 5
                               groupPath := ["Claim", group], name := "Tag" }
    let resolverModel : FlatModel :=
      { fields := [stringDeclaration, tagIn "Info", tagIn "Misc"]
        fieldRefByShortNameAllowed := true }
    let codeAt (base : PathBase) (groups : List String) (field : String) :=
      diagnosticOf (elaborateStringPatternCondition compilePattern resolverModel ["Claim"]
        { condition with field := { base, groups, field } })
    [codeAt .absolute ["Claim"] "Nope", codeAt .absolute ["Claim", "Nope"] "Code",
      codeAt .absolute ["Nope"] "Code", codeAt .absolute [] "Nope", codeAt (.relative 0) [] "Nope",
      codeAt (.relative 1) [] "Code", codeAt (.relative 0) [] "Tag", codeAt .absolute ["Claim"] "Code"] =
      [some .invalidEntity, some .invalidEntity, some .invalidRootGroup, some .invalidRootGroup,
        some .invalidEntity, some .tooManyParentGroups, some .fieldNameNotUnique, none] := by
  native_decide

/- A raw field is refused by the field-value read's raw gate, registered-custom and bound repeatable fields are admitted for prepared evaluation, and an ordinary declared-pattern field is admitted for prepared evaluation. A repeatable field is bound by its reading row; from an enclosing group without a row-bound error field it draws the Kernel's missing wildcard ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)). -/
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
        some (.fieldReference (.rawFieldValueRead ["Claim", "Code"])) ∧
    errorOf (elaborateStringPatternCondition compilePattern
      { fields := [customDecl] } ["Claim"] (condition)) =
        none ∧
    errorOf (elaborateStringPatternCondition compilePattern
      { fields := [patternDecl] } ["Claim"] (condition)) =
        none ∧
    errorOf (elaborateStringPatternCondition compilePattern
      repeatableModel ["Claim", "Items"] (condition)) =
        none ∧
    errorOf (elaborateStringPatternCondition compilePattern repeatableModel ["Claim"]
      { condition with field := { base := .relative 0, groups := ["Items"], field := "Code" } }) =
        some (.fieldReference (.unboundOperandLevel ["Claim", "Items", "Code"]
          { level := 10, placement := .contained, parallel := false, indexKeyed := false })) ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern
      repeatableModel ["Claim", "Items"] (condition)) = none ∧
    diagnosticOf (elaborateStringPatternCondition compilePattern repeatableModel ["Claim"]
      { condition with field := { base := .relative 0, groups := ["Items"], field := "Code" } }) =
        some .noWildcard := by
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

/- The injected test compiler and built-in declaration route independently classify both finite profiles. -/
example : ["[0-9]+", "[A-Z]+"].all (fun source =>
    let declaration := { stringDeclaration with stringPatternSource := some source }
    let declaredModel : FlatModel := { fields := [declaration] }
    ["123", "12A", "ABC", "AbC", "", " ABC "].all fun value =>
      preparedCell declaredModel 1 (.parsed (.str value)) ==
        some (declaration.checkRaw (.parsed (.str value)))) = true := by
  native_decide

private def multiPatternModel : FlatModel :=
  { fields := [{
      stringDeclaration with stringPatternSource := some "A" }, {
      stringDeclaration with
      id := 3
      name := "OtherCode"
      stringPatternSource := some "B" },
    numberDeclaration] }

private def multiPatternRaw (first second : String)
    (amount : RawCell := .parsed (.num 7)) : RawFlatContext where
  read id :=
    if id == 1 then .parsed (.str first)
    else if id == 3 then .parsed (.str second)
    else if id == 2 then amount
    else .empty

private def preparedModelCell (field : FieldId) (raw : RawFlatContext) :
    Option CheckedCell :=
  match prepareFlatStringPatterns compileDeclared multiPatternModel with
  | .error _ => none
  | .ok prepared => some ((prepared.checkContext raw).read field)

/- Model-complete preparation compiles every nonempty ordinary declared source in declaration order and keeps each matcher on its own field. -/
example :
    preparedModelCell 1 (multiPatternRaw "A" "B") =
        some {
          rawPresent := true
          parsed := some (.str "A")
          findings := [] } ∧
      preparedModelCell 3 (multiPatternRaw "A" "B") =
        some {
          rawPresent := true
          parsed := some (.str "B")
          findings := [] } ∧
      preparedModelCell 1 (multiPatternRaw "B" "A") =
        some {
          rawPresent := true
          parsed := none
          findings := [.declaredConstraint] } := by
  native_decide

/- A forged incomplete plan cannot silently fall back to the unprepared ordinary checker, while an unrelated declaration keeps its ordinary model-owned result. -/
example :
    let incomplete : PreparedFlatStringPatterns multiPatternModel compileDeclared := {
      fields := []
      modelWellFormed := by native_decide }
    (incomplete.checkContext (multiPatternRaw "A" "B")).read 1 =
        malformedCheckedCell ∧
      (incomplete.checkContext (multiPatternRaw "A" "B")).read 2 =
        (multiPatternModel.checkContext
          (multiPatternRaw "A" "B")).read 2 := by
  native_decide

private def preparedVerdict (model : FlatModel) (cell : RawCell) :
    Option Verdict :=
  match elaborateAndEvalStringPatternFull compileDeclared model ["Claim"]
      (raw cell) true (condition "A") with
  | .error _ => none
  | .ok verdict => some verdict

/- The existing checked pattern-condition consumer can now read a field whose own arbitrary declaration pattern was prepared first. A declaration mismatch remains formal unavailability, not a condition mismatch. -/
example :
    let declaredModel : FlatModel := {
      fields := [{
        stringDeclaration with stringPatternSource := some "[A-Z]+" }] }
    preparedVerdict declaredModel (.parsed (.str "A")) =
        some (.fired .value) ∧
      preparedVerdict declaredModel (.parsed (.str "1")) =
        some .unknown := by
  native_decide

private def preparedEvaluationErrorOf :
    Except PreparedStringPatternEvaluationError Verdict →
      Option PreparedStringPatternEvaluationError
  | .ok _ => none
  | .error error => some error

/- Preparation covers the complete model before the condition evaluates, so an unreferenced invalid declared source cannot leak through a partial plan. -/
example :
    let invalidModel : FlatModel := {
      fields := [stringDeclaration, {
        stringDeclaration with
        id := 3
        name := "OtherCode"
        stringPatternSource := some "(" }] }
    preparedEvaluationErrorOf
      (elaborateAndEvalStringPatternFull compileDeclared invalidModel ["Claim"]
        (raw (.parsed (.str "A"))) true (condition "A")) =
      some (.preparation (.pattern (.pattern .javaSyntax))) := by
  native_decide

/-! ## The pattern pair as validation leaves

Over a readable nonempty value the two operators are complements: their conjunction never fires and
their disjunction always does. An empty value fires neither, and a formally unavailable one leaves
both UNKNOWN, so the pair is not exhaustive there. The Kernel shows the first two regions on the
[negation pair grid](../../evidence/kernel-30.8.1/captures/negation-pair-grid-2026-10-02/request.json),
whose pattern rows this theory cannot replay without a host Java-pattern compiler; the grid holds no
formally unavailable String. -/

private def leafPair? (join : ValidationCondition model → ValidationCondition model →
    ValidationCondition model) (cell : RawCell) : Option (Verdict × Bool) := do
  let matched ← (CheckedValidationCondition.fromStringPattern model ["Claim"] compilePattern
    (condition)).toOption
  let violated ← (CheckedValidationCondition.fromStringPattern model ["Claim"] compilePattern
    (condition (op := .violated))).toOption
  let tree := join matched.core violated.core
  let context : ValidationEvaluationContext :=
    { fields := model.checkContext (raw cell), groups := GroupPresenceContext.unavailable }
  pure (ValidationCondition.evalSelected tree context (fun _ => true), tree.canFireOnEmpty)

example :
    [leafPair? .and (.parsed (.str "ABC")), leafPair? .and (.parsed (.str "xyz")),
     leafPair? .or (.parsed (.str "ABC")), leafPair? .or (.parsed (.str "xyz")),
     leafPair? .or .empty, leafPair? .or (.rejected .declaredConstraint)] =
      [some (.notFired, false), some (.notFired, false),
       some (.fired .value, false), some (.fired .value, false),
       some (.notFired, false), some (.unknown, false)] := by
  native_decide

/-! ## The pattern leaf on the addressed routes

The rule routes read the leaf through the checked document, not the scalar context: the full route
behind the content gate, the partial route through its call-local view. -/

private def checkedDocument? (cell : RawCell) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } compilePattern model).toOption
  let placed : ClassifiedCellInput := { address := { field := 1, path := [] }, stored := "ABC", raw := cell }
  (checkDocument prepared "en_US" { instantiatedRows := [], cells := [placed] }).toOption

private def addressedContext (document : CheckedDocument model)
    (input : AddressedValidationInput model) : AddressedValidationEvaluationContext model :=
  { scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := []
    input }

/-- The full route: the matched leaf, and the content gate's answer on an instance without content. -/
private def fullVerdicts? (cell : RawCell) : Option (Verdict × Verdict) := do
  let document ← checkedDocument? cell
  let checked ← (CheckedValidationCondition.fromStringPattern model ["Claim"] compilePattern
    condition).toOption
  let context := addressedContext document (.checked document)
  pure ((← (checked.core.evalAddressedFull context true).toOption),
    (← (checked.core.evalAddressedFull context false).toOption))

/-- The partial route, `covered` choosing whether the view reads the cell or reports it silent. -/
private def partialVerdict? (cell : RawCell) (covered : Bool) : Option Verdict := do
  let document ← checkedDocument? cell
  let checked ← (CheckedValidationCondition.fromStringPattern model ["Claim"] compilePattern
    condition).toOption
  let .leaf leaf := checked.core | none
  let context := addressedContext document (.partialView document fun environment field =>
    if covered then (document.validationAddressedCell environment field).map (some ·.cell)
    else pure none)
  (← ValidationConditionLeaf.evalAddressedPartial? context .full (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none leaf).toOption

/- A matching value fires on the full route and the gate keeps it silent without content, since the
pattern cannot fire on an empty field; the partial route reads a covered cell as the full one does
and an uncovered one as UNKNOWN. -/
example :
    fullVerdicts? (.parsed (.str "ABC")) = some (.fired .value, .notFired) ∧
    fullVerdicts? (.parsed (.str "xyz")) = some (.notFired, .notFired) ∧
    partialVerdict? (.parsed (.str "ABC")) true = some (.fired .value) ∧
    partialVerdict? (.parsed (.str "ABC")) false = some .unknown := by
  native_decide

private def customPatternVerdict (op : StringPatternOp) (value : String) (accept : Bool) :=
  let fixture : FlatModel := { fields := [
    { stringDeclaration with customType := some { name := "ProjectCode" } }] }
  let world : World := {
    now := { epochMillis := 0 }
    customFieldValidator? := fun name => if name == "ProjectCode" then
      some (fun _ _ => if accept then none else some { projectCode := "CUSTOM_REFUSAL" }) else none }
  (elaborateAndEvalStringPatternFull compilePattern fixture ["Claim"]
    (raw (.parsed (.str value))) true (condition (op := op)) world).toOption

example : customPatternVerdict .matched "ABC" true = some (.fired .value) ∧
    customPatternVerdict .violated "xyz" true = some (.fired .value) ∧
    customPatternVerdict .matched "ABC" false = some .unknown ∧
    customPatternVerdict .violated "xyz" false = some .unknown ∧
    customPatternVerdict .violated "" true = some .notFired := by native_decide

private def nestedPatternModel : FlatModel := {
  fields := [{ stringDeclaration with groupPath := ["Claim", "Items", "Details"], repeatableScope := [10, 20] }]
  repeatableGroups := [{ level := 10, path := ["Claim", "Items"] },
    { level := 20, path := ["Claim", "Items", "Details"] }] }

private def nestedPattern (parent : Nat) (op : StringPatternOp) (covered relevant : Bool := true)
    (bad : Bool := false) : Option (Verdict × Verdict × List MessagePointer × Bool × Bool) := do
  let fixture := nestedPatternModel
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } compilePattern fixture).toOption
  let checked ← (CheckedValidationCondition.fromStringPattern fixture ["Claim"] compilePattern
    { op, field := { base := .absolute, groups := ["Claim", "Items", "Details"], field := "Code" },
      source := "[A-Z]{3}" } ["Claim", "Items", "Details"]).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] }]
    cells := [{ address := { field := 1, path := [1, 1] }, stored := "xyz", raw := .parsed (.str "xyz") },
      { address := { field := 1, path := [2, 1] }, stored := "ABC",
        raw := if bad then .rejected .malformed else .parsed (.str "ABC") }] }).toOption
  let environment : Env := [(10, parent), (20, 1)]
  let context : AddressedValidationEvaluationContext fixture := {
    scalar := {
      fields := fixture.checkContext (raw (.parsed (.str "wrong scalar")))
      groups := GroupPresenceContext.unavailable }
    outer := environment, input := .checked document }
  let full ← (checked.core.evalAddressedFull context true).toOption
  let .leaf leaf := checked.core | none
  let partialContext : AddressedValidationEvaluationContext fixture := { context with input := .partialView document (fun row field =>
    if covered then (document.validationAddressedCell row field).map (fun (entry : CheckedAddressedCell) => some entry.cell) else pure none) }
  let partialVerdict ← (← leaf.evalAddressedPartial? partialContext .full (fun _ => relevant)
    (fun _ _ => .error (.checkedDocumentRequired [])) none).toOption
  let pointers ← (checked.core.referencePointers environment).toOption
  pure (full, partialVerdict, pointers, checked.core.requiresAddressedValidation,
    checked.core.wellFormedBool ["Claim"])

example : nestedPattern 2 .matched = some (.fired .value, .fired .value,
      [{ field := 1, coordinates := [.concrete 2, .concrete 1] }], true, false) := by native_decide

example : nestedPattern 1 .violated = some (.fired .value, .fired .value,
      [{ field := 1, coordinates := [.concrete 1, .concrete 1] }], true, false) := by native_decide

example : (nestedPattern 2 .matched false).map (fun (_, partialVerdict, _, _, _) => partialVerdict) = some .unknown := by native_decide

example : (nestedPattern 2 .matched true false).map (fun (_, partialVerdict, _, _, _) => partialVerdict) = some .unknown := by native_decide

example : (nestedPattern 2 .matched true true true).map (fun (full, partialVerdict, _, _, _) => (full, partialVerdict)) =
      some (.unknown, .unknown) := by native_decide

end A12Kernel.Conformance.StringPatternElaboration
