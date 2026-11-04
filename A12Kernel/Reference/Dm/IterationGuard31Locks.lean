import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # Kernel 31.1.1: a filtered entity's kind after its walk, and the widened iteration guard

Each list is the rows of one a12-dmkits laws class at `1124b523f`, kernel 31.1.1, checked through the
DM reader on a model that reproduces the fields its rows read. The first group fixes the order of a
`Having` clause's own gates: the filter body is walked first, then the operand's repetition walk, and
only then the filtered entity's kind, so a body's refused comparison, an unknown name or an unstarred
repeatable level draws its own class where kernel 30.8.1 drew the group class as `Having` was read. The
second group fixes the negative-condition guard: a comparison reading `CurrentRepetition` refuses
wherever the rule iterates, and a product sum meets the mixed-read refusal like every other aggregate.
The marked-filter negatives sit in `HavingGlobalAdmissionLocks` beside their 30.8.1 neighbours.
-/

namespace A12Kernel.Dm.IterationGuard31Locks

open A12Kernel

private def text (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope := scope, policy := { kind := .string } }

private def number (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat)
    (scale : Nat := 0) : FlatFieldDecl :=
  { text id groupPath name scope with policy := { kind := .number { scale, signed := true } } }

/-- A text enumeration whose single category `Band` maps its two values to `LOW` and `HIGH`. -/
private def band (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat)
    (stored : List String) : FlatFieldDecl :=
  { text id groupPath name scope with policy := { kind := .enumeration }, enumeration := some {
      storedTokens := stored, categories := [{ name := "Band", tokens := ["LOW", "HIGH"] }] } }

/-- The class this reader answers, `admitted`, or the refusal's detail when it carries no class, so a
refusal without a class fails a row rather than passing as any expected class. -/
private def verdict (flat : FlatModel) (group : GroupPath) (errorField condition : String) : String :=
  let dm : DmModel := { flat, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkValidationRule dm .english
      { group, name := "KindProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorField,
        condition, severity := "ERROR" } with
  | .ok _ => "admitted"
  | .error refusal => refusal.kernelClass?.getD refusal.detail

/-- Rows as `(error field, condition, class)`. With `reading`, the rule reads its error field first, as
the peer's rules do, so an admitted row is admitted and not refused for leaving it unreferenced. -/
private def mismatches (flat : FlatModel) (group : GroupPath) (reading : Bool)
    (rows : List (String × String × String)) : List (String × String × String) :=
  rows.filterMap fun (errorField, condition, expected) =>
    let actual := verdict flat group errorField
      (if reading then s!"FieldFilled({errorField}) And {condition}" else condition)
    if actual == expected then none else some (condition, expected, actual)

private def NO_GROUPS := "MVK_NO_GROUPS_ALLOWED"
private def NO_WILDCARD := "MVK_NO_WILDCARD"
private def WILDCARDS := "MVK_WILDCARDS_REQUIRED"
private def OUTER := "MVK_INVALID_OUTER_ITERATION"
private def EMPTY := "MVK_GROUP_IS_EMPTY"
private def NO_INDEX_FIELD := "MVK_NO_INDEX_FIELD"
private def TYPE := "MVK_INVALID_TYPE_FOR_COMPARISON"
private def NEG := "MVK_NEG_CONDITION_IN_ITERATION"

private def P : GroupPath := ["Policy"]

/-! ## The filtered entity's kind follows the walk -/

/-- `policy-filter` of `FilteredOperandGateOrderLawsTest`: a fixed insured party beside `Claims`, keyed
by `ClaimRef`. -/
private def policyFilter : FlatModel :=
  { fields := [text 1 P "Reference" [], text 2 (P ++ ["Insured"]) "InsuredName" [],
      text 3 (P ++ ["Claims"]) "ClaimRef" [10], number 4 (P ++ ["Claims"]) "Amount" [10] 2]
    repeatableGroups := [{ level := 10, path := P ++ ["Claims"], repeatability := some 20, indexField := some 3 }] }

example : policyFilter.validate.isOk = true := by native_decide

/-- Locked: a12-dmkits FilteredOperandGateOrderLawsTest (`whichGateAnswersOnAFilteredOperand` and
`whoseFilterAHavingAfterAnIndexKeyIs`) at 1124b523f, kernel 31.1.1. An unstarred filtered group draws
the walk's missing-star class where the rule does not iterate it; a starred one draws the kind. -/
private def gateOrderRows : List (String × String × String) :=
  let body := "[Claims/ClaimRef] == \"X\""
  [("Reference", s!"Sum(Claims*/Amount Having {body}) > 0", "admitted"),
   ("Reference", s!"Sum(Claims/Amount Having {body}) > 0", NO_WILDCARD),
   ("Reference", s!"NumberOfFilledGroups(Claims* Having {body}) > 0", NO_GROUPS),
   ("Reference", s!"Sum(Claims*/Amount For Reference Having {body}) > 0", WILDCARDS),
   ("Reference", s!"Sum(Claims/Amount For Reference Having {body}) > 0", WILDCARDS),
   ("Reference", "Sum(Claims*/Amount For Reference) > 0", "MVK_SEMANTIC_INDEX_AND_WILDCARD"),
   ("Reference", s!"NumberOfFilledGroups(Claims Having {body}) > 0", NO_WILDCARD),
   ("Reference", s!"NumberOfFilledGroups(Claims* For Reference Having {body}) > 0", WILDCARDS),
   ("Reference", "Sum(Claims*/Amount Having RepetitionNotUnique(Claims/ClaimRef)) > 0",
    "MVK_DISALLOWED_CONSTRUCT_IN_SET_EXPRESSION"),
   ("Reference", s!"Sum(Claims*/Amount Having ({body} And RepetitionNotUnique(Claims/ClaimRef))) > 0",
    "MVK_DISALLOWED_CONSTRUCT_IN_SET_EXPRESSION"),
   ("Reference", s!"Sum(Claims*/Amount For \"X\" Having {body}) > 0", "MVK_SEMANTIC_INDEX_AND_WILDCARD"),
   ("Reference", s!"Sum(Claims/Amount For \"X\" Having {body}) > 0", WILDCARDS),
   ("Reference", "Sum(Claims/Amount For \"X\") > 0", "MVK_PARAMSIZE_INVALIDN"),
   ("Reference", "Sum(Claims*/Amount For \"X\" Having [NoSuchField] == \"X\") > 0", "MVK_SEMANTIC_INDEX_AND_WILDCARD"),
   ("Reference", s!"NumberOfFilledGroups(Claims For \"X\" Having {body}) > 0", NO_GROUPS),
   ("Reference", "Sum(Claims*/Amount For Insured Having [Insured/InsuredName] == \"X\") > 0", NO_GROUPS),
   ("Reference", s!"Sum(Claims*/Amount For Claims*/ClaimRef Having {body}) > 0", "MVK_SEMANTIC_INDEX_WITH_WILDCARD"),
   ("Reference", "Sum(Claims*/Amount For Claims*/ClaimRef) > 0", "MVK_SEMANTIC_INDEX_WITH_WILDCARD")]

example : mismatches policyFilter P true gateOrderRows = [] := by native_decide

/-- Locked: a12-dmkits GroupOperandRepetitionScopeLawsTest (`aFilteredGroupIsRefusedAsAGroupOnceTheWalkPassesIt`)
at 1124b523f, kernel 31.1.1, on the peer's policy model, whose `Claims` is a repeatable group and
`Holder` a root field. The rows read `policyFilter`'s `Claims/Amount` and `Reference` in their place. -/
private def groupScopeRows : List (String × String × String) :=
  [("Reference", "AtLeastOneFieldFilled(Claims Having [Claims/Amount] > 0)", NO_WILDCARD),
   ("Reference", "AtLeastOneFieldFilled(Claims* Having [Claims/Amount] > 0)", NO_GROUPS),
   ("Reference", "Sum(Claims Having [Claims/Amount] > 0) > 0", NO_WILDCARD)]

example : mismatches policyFilter P true groupScopeRows = [] := by native_decide

/-- `claims-policy` of `FilterBodyComparisonLawsTest`, reduced to the fields the two grids below read:
`Claims` and `Parties` repeat, `Insured` is fixed, and `Orders` is keyed and holds `Lines`. -/
private def claimsPolicy : FlatModel :=
  { fields := [text 1 P "Reference" [],
      text 2 (P ++ ["Claims"]) "Notes" [10], number 3 (P ++ ["Claims"]) "Units" [10], number 4 (P ++ ["Claims"]) "Paid" [10] 2,
      text 5 (P ++ ["Insured"]) "Name" [], number 6 (P ++ ["Insured"]) "Count" [],
      text 7 (P ++ ["Parties"]) "Name" [11], number 8 (P ++ ["Parties"]) "Count" [11],
      text 9 (P ++ ["Orders"]) "OrderNo" [12], text 10 (P ++ ["Orders"]) "Note" [12], number 11 (P ++ ["Orders"]) "Units" [12],
      number 12 (P ++ ["Orders", "Lines"]) "Amount" [12, 13] 2, text 13 (P ++ ["Orders", "Lines"]) "Memo" [12, 13],
      number 14 (P ++ ["Orders", "Lines"]) "Qty" [12, 13]]
    repeatableGroups := [
      { level := 10, path := P ++ ["Claims"], repeatability := some 5 },
      { level := 11, path := P ++ ["Parties"], repeatability := some 4 },
      { level := 12, path := P ++ ["Orders"], repeatability := some 3, indexField := some 9 },
      { level := 13, path := P ++ ["Orders", "Lines"], repeatability := some 3 }] }

example : claimsPolicy.validate.isOk = true := by native_decide

/-- Locked: a12-dmkits FilterBodyComparisonLawsTest (`aFilterBodysComparisonOutranksTheFilteredSpecsOwnClass`
and `whereTheFilterChainRaisesAroundItsBody`) at 1124b523f, kernel 31.1.1. The filter's own chain,
the entity's kind included, is asked once the whole spec is read, so a body's refused comparison, a
name resolving to nothing and a broken token are named first; each has a sound body beside it. -/
private def filterBodyRows : List (String × String × String) :=
  let claims (condition : String) := ("Reference", condition)
  let rows : List (String × String) := [
   claims "Sum(Claims/Paid Having [Claims/Units] > 5) > 0",
   claims "Sum(Claims/Paid Having [Claims/Notes] < [Claims/Units]) > 0",
   claims "Sum(Claims*/Paid Having Sum(Claims*/Units Having [Claims/Units] > 5) > 0) > 0",
   claims "Sum(Claims*/Paid Having Sum(Claims*/Units Having [Claims/Notes] < [Claims/Units]) > 0) > 0",
   claims "Sum(Claims*/Paid Having Sum(Claims*/Units Having [Reference] > 5) > 0) > 0",
   claims "Sum(Claims*/Paid Having Sum(Claims/Units Having [Claims/Units] > 5) > 0) > 0",
   claims "Sum(Claims*/Paid Having Sum(Claims/Units Having [Claims/Notes] < [Claims/Units]) > 0) > 0",
   claims "Sum(Claims*/Paid* Having [Claims/Units] > 5) > 0",
   claims "Sum(Claims*/Paid* Having [Claims/Notes] < [Claims/Units]) > 0",
   claims "NumberOfFilledGroups(Claims* Having [Claims/Units] > 5) > 0",
   claims "NumberOfFilledGroups(Claims* Having [Claims/Notes] < [Claims/Units]) > 0",
   claims "NumberOfFilledGroups(Claims* Having [NoSuchField] == \"x\") > 0",
   claims "NumberOfFilledGroups(Claims* Having [Claims/Units] + ) > 0",
   claims "Sum(Claims*/Paid For Insured Having [Insured/Name] == \"x\") > 0",
   claims "Sum(Claims*/Paid For Insured Having [Insured/Name] < [Insured/Count]) > 0",
   claims "Sum(Claims*/Paid Having [Parties/Name] == \"x\") > 0",
   claims "Sum(Claims*/Paid Having [Parties/Name] < [Parties/Count]) > 0",
   claims "Sum(Claims*/Paid Having [Parties/Name] == [Parties/Count]) > 0",
   claims "Sum(Claims*/Paid Having [Parties/Count] == [Claims/Paid]) > 0",
   claims "Sum(Orders*/Units For Parties*/Name Having [Parties/Name] == \"x\") > 0",
   claims "Sum(Orders*/Units For Parties*/Name Having [Parties/Name] < [Parties/Count]) > 0",
   claims "Sum(Orders*/Units For Parties*/Name Having [Orders/Note] == \"x\") > 0",
   claims "Sum(Orders*/Units For Parties*/Name Having [Orders/Note] < [Orders/Units]) > 0",
   claims "Sum(Orders*/Units For Reference Having [Orders/Note] == \"x\") > 0",
   claims "Sum(Orders*/Units For Reference Having [Orders/Note] < [Orders/Units]) > 0",
   claims ("Sum(Orders*/Lines*/Amount Having Sum(Orders*/Units Having [Orders/Lines/Memo] < " ++
     "[Orders/Lines/Qty]) > 0) > 0"),
   claims ("Sum(Orders*/Units Having Sum(Orders*/Lines*/Amount Having [Orders/Lines/Memo] < " ++
     "[Orders/Lines/Qty]) > 0) > 0"),
   claims "Sum(Claims*/Paid Having Sum(Claims*/Units) > 0) > 0"]
  let expected := [NO_WILDCARD, TYPE, "MVK_DISALLOWED_CONSTRUCT_IN_SET_EXPRESSION", TYPE, TYPE, NO_WILDCARD, TYPE,
    "MVK_INVALID_WILDCARD", "MVK_INVALID_WILDCARD", NO_GROUPS, TYPE, "MVK_INVALID_ENTITY", "MVK_UNEXPECTED_TOKEN",
    NO_GROUPS, TYPE, "MVK_INVALID_ITERATION_IN_SET_EXPRESSION", TYPE, "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING",
    "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_SEMANTIC_INDEX_WITH_WILDCARD", TYPE,
    "MVK_INVALID_ITERATION_IN_SET_EXPRESSION", TYPE, WILDCARDS, TYPE, TYPE, TYPE, "MVK_NO_ITERATION_FOR_WILDCARD"]
  (rows.zip expected).map fun ((errorField, condition), outcome) => (errorField, condition, outcome)

example : filterBodyRows.length = 28 := by native_decide
example : mismatches claimsPolicy P true filterBodyRows = [] := by native_decide

/-- `catalogue` of `FirstFilledOperandShapeLawsTest`: groups of each shape beside fields to read, a
group left unstarred below `Outer`, and a keyed `Keyed` whose index key selects its row. -/
private def catalogue : FlatModel :=
  let I : GroupPath := ["Item"]
  { fields := [text 1 I "Title" [], text 2 I "Subtitle" [], number 3 I "Weight" [],
      band 4 I "Tier" [] ["BASIC", "PLUS"], band 5 (I ++ ["Grading"]) "Grade" [] ["NEW", "USED"],
      text 6 (I ++ ["Lines"]) "Sku" [10], number 7 (I ++ ["Lines"]) "Qty" [10],
      band 8 (I ++ ["Reviews"]) "Stars" [11] ["ONE", "FIVE"],
      text 9 (I ++ ["Nested", "Deep"]) "Note" [],
      text 10 (I ++ ["Outer"]) "Label" [12],
      band 11 (I ++ ["Outer", "Graded"]) "Grade" [12] ["NEW", "USED"],
      text 12 (I ++ ["Keyed"]) "Key" [13], text 13 (I ++ ["Keyed"]) "Note" [13]]
    repeatableGroups := [
      { level := 10, path := I ++ ["Lines"], repeatability := some 5 },
      { level := 11, path := I ++ ["Reviews"], repeatability := some 5 },
      { level := 12, path := I ++ ["Outer"], repeatability := some 5 },
      { level := 13, path := I ++ ["Keyed"], repeatability := some 5, indexField := some 12 }] }

example : catalogue.validate.isOk = true := by native_decide

private def ITEM : GroupPath := ["Item"]

/-- Locked: a12-dmkits FirstFilledOperandShapeLawsTest ("eachShapesClass_onEveryGroupShape_andBesideASecondDefect",
`theGroupShapesKeepTheirClassOnARuleThatIteratesTheRepetition` and `theMarkerOutsideAFilterAnswersAheadOfEveryShape`,
the rows that read no empty group) at 1124b523f, kernel 31.1.1. A group's filter draws the group's class
once the walk passes it, an unstarred one the walk's class where the rule does not iterate it, and a
marked group carrying its own filter the marker's class. -/
private def firstFilledRows : List (String × String × String) :=
  let first (condition : String) := s!"FirstFilledValue({condition}) == \"x\""
  let low (condition : String) := s!"FirstFilledValue({condition}) == \"LOW\""
  [("Title", first "Grading Having [Weight] > 0, Title", NO_GROUPS),
   ("Title", first "Lines Having [Lines/Qty] > 0, Title", NO_WILDCARD),
   ("Title", first "Lines* Having [Lines/Qty] > 0, Title", NO_GROUPS),
   ("Title", low "Grading -> Band", NO_GROUPS),
   ("Title", low "Reviews* -> Band", NO_GROUPS),
   ("Title", low "Reviews -> Band", NO_WILDCARD),
   ("Title", low "Tier -> Band, Grading/Grade -> Band", "admitted"),
   ("Title", low "Reviews*/Stars -> Band", "admitted"),
   ("Title", first "Nested", "admitted"),
   ("Title", first "Title Having [Weight] > 0, Subtitle", WILDCARDS),
   ("Title", low "Tier -> Band Having [Weight] > 0, Grading/Grade -> Band", WILDCARDS),
   ("Title", first "Lines/Sku Having [Lines/Qty] > 0, Title", NO_WILDCARD),
   ("Title", first "Lines*/Sku Having [Lines/Qty] > 0, Subtitle", "admitted"),
   ("Title", low "Grading -> Band, Tier, Tier", NO_GROUPS),
   ("Title", first "Title Having [Weight] > 0, Title", WILDCARDS),
   ("Title", first "Title, Title Having [Weight] > 0", WILDCARDS),
   ("Title", first "Title Having [Weight] > 0, Weight", WILDCARDS),
   ("Title", "[Title] == \"x\"", "admitted"),
   ("Lines/Sku", first "Lines Having [Lines/Qty] > 0, Title", NO_GROUPS),
   ("Lines/Sku", first "Lines* Having [Lines/Qty] > 0, Title", NO_GROUPS),
   ("Lines/Sku", low "Reviews* -> Band", NO_GROUPS),
   ("Lines/Sku", "[Lines/Sku] == \"x\"", "admitted"),
   ("Title", low "$Grading -> Band", OUTER),
   ("Title", low "$Reviews* -> Band", OUTER),
   ("Title", first "$Title Having [Weight] > 0, Subtitle", OUTER),
   ("Title", first "$Grading Having [Weight] > 0, Title", OUTER)]

example : mismatches catalogue ITEM true firstFilledRows = [] := by native_decide

/-- Locked: a12-dmkits FirstFilledOperandShapeLawsTest ("anUnstarredRepetitionOrAnIndexMovesTheClass_andNothingElseDoes",
the rows that read no empty group) at 1124b523f, kernel 31.1.1. An index answers first where it
resolves to no index field and binds the level where it does; inside a filter the bare shapes keep their
classes, except that a marked group carrying its own filter has left the outer filter's scope. -/
private def movingRows : List (String × String × String) :=
  let first (condition : String) := s!"FirstFilledValue({condition}) == \"x\""
  let low (condition : String) := s!"FirstFilledValue({condition}) == \"LOW\""
  let ruleRows := ["Title", "Outer/Label", "Lines/Sku"].flatMap fun rule =>
    [(rule, low "Grading -> Band", NO_GROUPS), (rule, low "Outer*/Graded -> Band", NO_GROUPS),
     (rule, s!"[{rule}] == \"x\"", "admitted")]
  let inFilter := ["", "$"].flatMap fun marker =>
    let category := low (marker ++ "Grading -> Band")
    let filtered := first (marker ++ "Grading Having [Title] == \"a\", Title")
    [("Title", first s!"Lines*/Sku Having {category}, Title", NO_GROUPS),
     ("Title", first s!"Lines*/Sku Having {filtered}, Subtitle", if marker.isEmpty then NO_GROUPS else OUTER)]
  ruleRows ++ [
    ("Title", low "Outer/Graded -> Band", NO_WILDCARD),
    ("Outer/Label", low "Outer/Graded -> Band", NO_GROUPS),
    ("Lines/Sku", low "Outer/Graded -> Band", NO_WILDCARD),
    ("Title", low "Grading For \"k\" -> Band", NO_INDEX_FIELD),
    ("Title", first "Grading For \"k\" Having [Title] == \"a\", Title", NO_INDEX_FIELD),
    ("Title", first "Keyed For \"k\" Having [Keyed/Note] == \"a\", Title", NO_GROUPS),
    ("Title", first "Keyed For \"k\"", "admitted")] ++ inFilter

example : mismatches catalogue ITEM true movingRows = [] := by native_decide

/-! ## The negative-condition guard -/

/-- The peer's `policy-current-repetition`: `Claims` holds `Parts`, each repeating three times. With
`keyedPair`, `Claims` repeats twice and declares an index field, which the ordinary guard skips. -/
private def policyPartsWith (keyedPair : Bool) : FlatModel :=
  { fields := [number 1 (P ++ ["Claims"]) "Amount" [10], text 3 (P ++ ["Claims"]) "ClaimNo" [10],
      number 2 (P ++ ["Claims", "Parts"]) "Qty" [10, 11]]
    repeatableGroups := [
      { level := 10, path := P ++ ["Claims"], repeatability := some (if keyedPair then 2 else 3),
        indexField := if keyedPair then some 3 else none },
      { level := 11, path := P ++ ["Claims", "Parts"], repeatability := some 3 }] }

private def policyParts : FlatModel := policyPartsWith false
private def policyPartsKeyed : FlatModel := policyPartsWith true

example : policyParts.validate.isOk = true ∧ policyPartsKeyed.validate.isOk = true := by native_decide

/-- Locked: a12-dmkits CurrentRepetitionIterationGuardLawsTest (`aRepetitionReadRefusesAtEveryLevelTheRuleIterates`)
at 1124b523f, kernel 31.1.1. The last row is the control that the refusal is the guard's: a positive
read of the bound row rescues the comparison. -/
private def repetitionRows : List (String × String × String) :=
  [("Claims/Parts/Qty", "[Claims/Parts/Qty] > CurrentRepetition(Claims)", NEG),
   ("Claims/Parts/Qty", "CurrentRepetition(Claims) > [Claims/Parts/Qty]", NEG),
   ("Claims/Parts/Qty", "[Claims/Parts/Qty] > CurrentRepetition(Claims/Parts)", NEG),
   ("Claims/Amount", "[Claims/Amount] > CurrentRepetition(Claims)", NEG),
   ("Claims/Parts/Qty", "FieldFilled(Claims/Parts/Qty) And [Claims/Parts/Qty] > CurrentRepetition(Claims)",
    "admitted")]

example : mismatches policyParts P false repetitionRows = [] := by native_decide

/-- Locked: the [kernel 31.1.1 static capture](../../../evidence/kernel-31.1.1/captures/first-calibration-2026-11-04/static-ops.json),
rows "keyed-*". Every peer row keeps its outer level judged, so a refusal there cannot tell "at every
level the rule iterates" from "at the levels the repetition itself iterates". With the outer "Claims"
repeating twice and keyed, the guard skips it (the first row, a bare negative over "Claims", is
admitted) and judges "Parts" alone, where the outer repetition does not iterate; the comparison is
still refused, so the refusal follows the levels the rule iterates. -/
private def skippedOuterRows : List (String × String × String) :=
  [("Claims/Amount", "FieldNotFilled(Claims/Amount)", "admitted"),
   ("Claims/Parts/Qty", "FieldNotFilled(Claims/Parts/Qty)", NEG),
   ("Claims/Parts/Qty", "[Claims/Parts/Qty] > CurrentRepetition(Claims)", NEG),
   ("Claims/Parts/Qty", "FieldFilled(Claims/Parts/Qty) And [Claims/Parts/Qty] > CurrentRepetition(Claims)",
    "admitted"),
   ("Claims/Parts/Qty", "[Claims/Parts/Qty] > CurrentRepetition(Claims/Parts)", NEG)]

example : mismatches policyPartsKeyed P false skippedOuterRows = [] := by native_decide

/-- The warehouse of `SelectedIterationGuardLawsTest`: one warehouse keys its bins, and a repeatable
request names the bin it wants. -/
private def warehouse : FlatModel :=
  let S : GroupPath := ["Store"]
  { fields := [text 1 S "Ref" [], text 2 (S ++ ["Requests"]) "Wanted" [10], text 3 (S ++ ["Requests"]) "Note" [10],
      text 4 (S ++ ["Warehouse", "Bins"]) "BinCode" [11],
      number 5 (S ++ ["Warehouse", "Bins", "Slots"]) "Qty" [11, 12],
      number 6 (S ++ ["Warehouse", "Bins", "Slots"]) "Weight" [11, 12]]
    repeatableGroups := [
      { level := 10, path := S ++ ["Requests"], repeatability := some 3 },
      { level := 11, path := S ++ ["Warehouse", "Bins"], repeatability := some 4, indexField := some 4 },
      { level := 12, path := S ++ ["Warehouse", "Bins", "Slots"], repeatability := some 3 }] }

example : warehouse.validate.isOk = true := by native_decide

/-- Locked: a12-dmkits SelectedIterationGuardLawsTest (`theMixedReferenceGateAsksEveryAggregate`) at
1124b523f, kernel 31.1.1: a product sum mixing the key's iterating selection with a fixed one meets the
mixed-read refusal against a constant like a sum or a maximum, where kernel 30.8.1 exempted it, and an
all-iterating product keeps its zero refusal. Each is a bare comparison reporting on the key it reads. -/
private def mixedRows : List (String × String × String) :=
  let dynamic := "/Store/Warehouse/Bins/Slots*/Qty For Wanted"
  let fixed := "/Store/Warehouse/Bins/Slots*/Weight For \"a\""
  let dynamicWeight := "/Store/Warehouse/Bins/Slots*/Weight For Wanted"
  [("Wanted", s!"Sum({dynamic}, {dynamicWeight}) > 0", "admitted"),
   ("Wanted", s!"Sum({dynamic}, {fixed}) > 0", NEG),
   ("Wanted", s!"MaxValue({dynamic}, {fixed}) > 0", NEG),
   ("Wanted", s!"SumOfProducts({dynamic}, {fixed}) > 0", NEG),
   ("Wanted", s!"SumOfProducts({dynamic}, {fixed}) == 0", NEG),
   ("Wanted", s!"SumOfProducts({dynamic}, {dynamicWeight}) == 0", NEG)]

example : mismatches warehouse ["Store", "Requests"] false mixedRows = [] := by native_decide

end A12Kernel.Dm.IterationGuard31Locks
