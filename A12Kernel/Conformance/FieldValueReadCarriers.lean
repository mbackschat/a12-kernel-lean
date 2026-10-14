import A12Kernel.Conformance.Elaboration.Support
import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.StringPattern
import A12Kernel.Elaboration.TemporalValuesNotUnique
import A12Kernel.Elaboration.ValidationCondition.Assembly

/-! # The field-value read's gates on its remaining carriers

The Kernel asks the field-value read's gates as its bracket closes, ahead of the class of the
operator standing around it, on an arithmetic operand, on a computation's operand writing a String,
an Enumeration, a Time or a Number, and on a category read
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-carriers)), and on a pattern comparison's field and a DateRange
comparison's sides, while a scalar membership's group subject, an entity, waits for its members'
reads ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)).
A field an operator names as a parameter asks the group gate alone and meets its operator's own value
gates, and a category read of a field declaring no Enumeration draws its own class
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
The fixture mirrors those grids' model. A carrier that projects no Kernel class of its own is read
through its resolution failure's class, and a refusal of the carrier's own is kept apart from one
that projects no class.
-/

namespace A12Kernel.Conformance.FieldValueReadCarriers

open A12Kernel
open A12Kernel.Conformance.Elaboration.Support (absolute bare dispatchDateComponents errorOf)

private def items : RepeatableGroupDecl := { level := 10, path := ["Grid", "Items"] }

private def grades : EnumerationDeclaration :=
  { storedTokens := ["A", "B"], categories := [{ name := "Band", tokens := ["Hi", "Lo"] }] }

private def refDecl : FlatFieldDecl :=
  { id := 0, groupPath := ["Grid"], name := "Ref", policy := { kind := .string } }

private def otherDecl : FlatFieldDecl := { refDecl with id := 1, name := "Other" }

private def copyDecl : FlatFieldDecl := { refDecl with id := 2, name := "Copy" }

private def noteDecl : FlatFieldDecl :=
  { refDecl with id := 3, name := "Note", stringValueMode := .raw
                 stringPolicy := { lineBreaksPermitted := true } }

private def amountDecl : FlatFieldDecl :=
  { id := 4, groupPath := ["Grid"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } } }

private def dueDecl : FlatFieldDecl :=
  { id := 5, groupPath := ["Grid"], name := "Due",
    policy := { kind := .temporal .date dispatchDateComponents } }

private def partialDecl : FlatFieldDecl :=
  { dueDecl with id := 6, name := "Partial"
                 temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }

private def gradeDecl : FlatFieldDecl :=
  { id := 7, groupPath := ["Grid"], name := "Grade", policy := { kind := .enumeration },
    enumeration := some grades }

private def gradeCopyDecl : FlatFieldDecl := { gradeDecl with id := 8, name := "GradeCopy" }

private def totalDecl : FlatFieldDecl :=
  { amountDecl with id := 9, groupPath := ["Grid", "Ledger"], name := "Total" }

private def qtyDecl : FlatFieldDecl :=
  { amountDecl with id := 10, groupPath := items.path, name := "Qty", repeatableScope := [items.level] }

private def labelDecl : FlatFieldDecl :=
  { refDecl with id := 11, groupPath := items.path, name := "Label", repeatableScope := [items.level] }

private def spanDecl : FlatFieldDecl :=
  { id := 12, groupPath := ["Grid"], name := "Span", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def span2Decl : FlatFieldDecl := { spanDecl with id := 13, name := "Span2" }

private def priceDecl : FlatFieldDecl :=
  { qtyDecl with id := 14, name := "Price", policy := { kind := .number { scale := 2, signed := false } } }

private def dueCopyDecl : FlatFieldDecl := { dueDecl with id := 15, name := "DueCopy" }

private def model : FlatModel :=
  { fields := [refDecl, otherDecl, copyDecl, noteDecl, amountDecl, dueDecl, partialDecl, gradeDecl,
      gradeCopyDecl, totalDecl, qtyDecl, labelDecl, spanDecl, span2Decl, priceDecl, dueCopyDecl],
    repeatableGroups := [items] }

private def grid (field : String) : SurfaceFieldPath := absolute ["Grid"] field

/-- How a carrier answered: admitted, refused by a resolution failure with the class it projects,
    or refused by the carrier's own gate once every read passed. -/
private inductive ReadView where
  | admitted
  | read (diagnostic : Option KernelStaticDiagnostic)
  | carrier
  deriving Repr, DecidableEq

private def viewOf (resolveOf : ε → Option ResolveError) : Except ε α → ReadView
  | .ok _ => .admitted
  | .error error =>
      match resolveOf error with
      | some resolve => .read resolve.diagnostic?
      | none => .carrier

private def field (name : String) : AuthoredNumericExpr SurfaceNumericAtom := .atom (.field (grid name))

private def one : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 1, authoredScale := 0 }

private def numericResolve? : NumericValidationElabError → Option ResolveError
  | .resolve error => some error
  | _ => none

private def ruleView (left right : AuthoredNumericExpr SurfaceNumericAtom) : ReadView :=
  viewOf numericResolve? (elaborateNumericComparison model ["Grid"] { op := .ordinary .equal, left, right })

/- **An arithmetic operand's read answers ahead of the operator's own class**, on each side of a
   comparison and inside `Abs` and `Min`: a group draws the group class, a raw String the raw class
   and a partially known Date the date class, where a Date of full precision and a String pass the
   read and meet the operator's Number gate. An operand resolved without the read's gates reports a
   group as a name resolving to nothing and the two value refusals as the operator's. -/
example :
    [ruleView (field "Amount") (.binary .add (field "Ledger") one),
      ruleView (field "Amount") (.binary .add (field "Note") one),
      ruleView (field "Amount") (.binary .subtract (field "Partial") one),
      ruleView (field "Amount") (.binary .multiply (field "Ledger") one),
      ruleView (.binary .add (field "Amount") (field "Ledger")) one,
      ruleView (field "Amount") (.abs (field "Ledger")),
      ruleView (field "Amount") (.extremum .minimum (field "Ledger") (field "Amount")),
      ruleView (field "Amount") (.binary .subtract (field "Due") one),
      ruleView (field "Amount") (.binary .multiply (field "Other") one),
      ruleView (field "Amount") (.binary .add (field "NoSuch") one),
      ruleView (field "Amount") (.binary .add (field "Amount") one)] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid),
        .read (some .invalidDateType), .read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .carrier, .carrier,
        .read (some .invalidEntity), .admitted] := by
  native_decide

private def atom (operand : SurfaceNumericAtom) : AuthoredNumericExpr SurfaceNumericAtom := .atom operand

/- **A rule in a repeatable group reads the same way**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
   its addressed operands ask the gates, so a fixed group and a raw String read from the iterated
   level draw their classes, and a fixed group named as `Length`'s parameter draws the group class.
   The rows measure the root's `Amount` on the left (`r1`, `r2`), which this route's row boundary
   refuses, so the fixture reads the row's own `Qty` there. The last three parameters take the group
   class by the parameter rule measured at the root; only `Length` is measured on this route (`r4`). -/
example :
    let addressed (right : AuthoredNumericExpr SurfaceNumericAtom) :=
      viewOf numericResolve? (elaborateRepeatableNumericComparison model items.path
        { op := .ordinary .equal, left := .atom (.field (absolute items.path "Qty")), right })
    [addressed (.binary .add (field "Ledger") one), addressed (.binary .add (field "Note") one),
      addressed (atom (.stringLength (grid "Ledger"))),
      addressed (atom (.stringRange (grid "Ledger") 1 2)),
      addressed (atom (.dateRangeBoundPart (grid "Ledger") .start .year)),
      addressed (atom (.fieldValueAsNumber (.direct (grid "Ledger"))))] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid)] ++
        List.replicate 4 (.read (some .noGroupsAllowed)) := by
  native_decide

/- **A field an operator names as a parameter asks the group gate alone and meets the operator's own
   value gates**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
   A group draws the group class inside `RangeAsNumber`, `Length`, `FieldValueAsNumber` and a
   DateRange endpoint's component. A raw String meets `RangeAsNumber`'s and `Length`'s own gates, which
   this carrier refuses without projecting their classes. -/
example :
    [ruleView (atom (.stringRange (grid "Ledger") 1 2)) one,
      ruleView (.binary .add (atom (.stringLength (grid "Ledger"))) one) one,
      ruleView (atom (.fieldValueAsNumber (.direct (grid "Ledger")))) one,
      ruleView (atom (.dateRangeBoundPart (grid "Ledger") .start .year)) one,
      ruleView (atom (.stringRange (grid "Note") 1 2)) one,
      ruleView (.binary .add (atom (.stringLength (grid "Note"))) one) one] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .noGroupsAllowed), .carrier, .carrier] := by
  native_decide

private def numericComputationResolve? : NumericComputationElabError → Option ResolveError
  | .resolve error => some error
  | _ => none

/- **A Number computation's operand is a field-value read**: a group, a raw String and a partially
   known Date draw their classes ahead of the operator's, while a field of the fixed group is admitted.
   A Date of full precision passes the read and meets the operand's Number gate, and a repeatable
   group draws the missing-star class
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)). -/
example :
    let computed (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      viewOf numericComputationResolve?
        (elaborateNumericComputationOperation model ["Grid"] amountDecl.id expression)
    [computed (.binary .add (field "Ledger") one), computed (.binary .add (field "Note") one),
      computed (.binary .subtract (field "Partial") one),
      computed (.binary .add (.atom (.field (absolute ["Grid", "Ledger"] "Total"))) one),
      computed (.binary .subtract (field "Due") one), computed (.binary .add (field "Items") one)] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid),
        .read (some .invalidDateType), .admitted, .carrier, .read (some .noWildcard)] := by
  native_decide

/- **A Number computation's operator parameter asks the group gate alone**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
   a group draws the group class and a repeatable group the missing-star class, while a raw String
   and a partially known Date meet the operator's own gates rather than the read's. Asking the read's
   value gates would draw the raw class for `Length` and `FieldValueAsNumber` and the date class for
   `RangeAsNumber`. -/
example :
    let computed (operand : SurfaceNumericAtom) :=
      viewOf numericComputationResolve?
        (elaborateNumericComputationOperation model ["Grid"] amountDecl.id (atom operand))
    [computed (.stringLength (grid "Ledger")), computed (.fieldValueAsNumber (.direct (grid "Ledger"))),
      computed (.stringRange (grid "Ledger") 1 2),
      computed (.dateRangeBoundPart (grid "Ledger") .start .year),
      computed (.fieldValueAsNumber (.direct (grid "Items"))), computed (.stringLength (grid "Note")),
      computed (.fieldValueAsNumber (.direct (grid "Note"))), computed (.stringRange (grid "Note") 1 2),
      computed (.stringRange (grid "Partial") 1 2)] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .noGroupsAllowed), .read (some .noWildcard), .carrier, .carrier, .carrier,
        .carrier] := by
  native_decide

private def stringComputationResolve? : StringComputationElabError → Option ResolveError
  | .resolve error => some error
  | _ => none

/- **A String computation's copied field is a field-value read.** A group draws the group class and
   a raw String the raw class, where resolving the operand without the gates reports the group as a
   name resolving to nothing and the raw String as the carrier's own refusal. A repeatable group draws
   the missing-star class, as on a Number target. -/
example :
    let computed (source : String) :=
      viewOf stringComputationResolve?
        (elaborateStringComputationOperation model ["Grid"] copyDecl.id (.field (grid source)))
    [computed "Ledger", computed "Note", computed "Other", computed "Items"] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid), .admitted,
        .read (some .noWildcard)] := by
  native_decide

/- **`FieldValueAsString`'s parameter asks the group gate alone**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
   a group and a repeatable group draw their classes, while a raw String meets the conversion's own
   Number gate rather than the read's raw class. -/
example :
    let computed (source : String) :=
      viewOf stringComputationResolve?
        (elaborateStringComputationOperation model ["Grid"] copyDecl.id (.fieldValueAsString (grid source)))
    [computed "Ledger", computed "Items", computed "Note", computed "Amount"] =
      [.read (some .noGroupsAllowed), .read (some .noWildcard), .carrier, .admitted] := by
  native_decide

private def enumerationComputationResolve? : EnumerationComputationElabError → Option ResolveError
  | .resolve error | .source (.resolve error) => some error
  | _ => none

/- **An Enumeration computation's copied field is a field-value read**, and a category source asks
   the group gate
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)). A group draws the group class on both and
   a raw String the raw class, while another field of the same domain is admitted. -/
example :
    let computed (source : SurfaceTextFieldOperand) :=
      viewOf enumerationComputationResolve?
        (elaborateEnumerationComputation model ["Grid"] gradeCopyDecl.id (.field source))
    [computed (.direct (grid "Ledger")), computed (.category (grid "Ledger") "Band"),
      computed (.direct (grid "Note")), computed (.direct (grid "Grade")),
      computed (.category (grid "Other") "Band"), computed (.category (grid "Note") "Band")] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .rawTypeOperandInvalid), .admitted, .read (some .noEnumeration),
        .read (some .noEnumeration)] := by
  native_decide

/-- The origin grid's model, whose fixed group `Ledger` declares fields named as the root's, each of
    another kind. -/
private def originModel : FlatModel :=
  let ledger := ["Grid", "Ledger"]
  { fields := [otherDecl, gradeDecl, { gradeDecl with id := 20, groupPath := ledger, name := "Tier" },
      { amountDecl with id := 21, groupPath := ledger, name := "Grade" },
      { amountDecl with id := 22, groupPath := ledger, name := "Sum" },
      { amountDecl with id := 23, groupPath := ledger, name := "Other" },
      { refDecl with id := 24, groupPath := ledger, name := "Text" }] }

private def enumerationOrigin (declaringGroup : GroupPath) : ReadView :=
  viewOf enumerationComputationResolve?
    (elaborateEnumerationComputation originModel declaringGroup 20 (.field (.direct (bare "Grade"))))

private def numberOrigin (declaringGroup : GroupPath) : ReadView :=
  viewOf numericComputationResolve? (elaborateNumericComputationOperation originModel declaringGroup 22
    (.binary .add (.atom (.field (bare "Grade"))) one))

private def stringOrigin (declaringGroup : GroupPath) : ReadView :=
  viewOf stringComputationResolve?
    (elaborateStringComputationOperation originModel declaringGroup 24 (.field (bare "Other")))

/- **A computation's relative name resolves from its declaring group, not from its target's**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
   A target in `Ledger` declared at the root reads the root's field of that name, and declared in
   `Ledger` reads `Ledger`'s, on an Enumeration, a Number and a String target alike, so each pair
   admits one declaration and refuses the other. -/
example :
    [enumerationOrigin ["Grid"], enumerationOrigin ["Grid", "Ledger"], numberOrigin ["Grid"],
      numberOrigin ["Grid", "Ledger"], stringOrigin ["Grid"], stringOrigin ["Grid", "Ledger"]] =
      [.admitted, .carrier, .carrier, .admitted, .admitted, .carrier] := by
  native_decide

private def conditionView (condition : SurfaceCondition) : ReadView :=
  viewOf (fun | ElabError.resolve error => some error | _ => none) (elaborate model ["Grid"] condition)

/- **A category read `[F -> C]` asks the group gate**, as a membership's member and as either side
   of a text comparison: a group draws the group class ahead of the subject's kind and the category
   reader's own gates. Its value gates never answer: a raw String's category read draws the
   non-Enumeration class where its stored read draws the raw class
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
example :
    let ledgerBand : SurfaceTextFieldOperand := .category (grid "Ledger") "Band"
    [conditionView (.enumerationFieldValueMembership .included (.direct (grid "Other")) [ledgerBand]),
      conditionView (.compareTextFields .equal ledgerBand (.direct (grid "Other"))),
      conditionView (.compareTextFields .equal (.direct (grid "Other")) ledgerBand),
      conditionView (.compareEnumeration .equal (grid "Ledger") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Grade") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Note") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Note") .stored "A")] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .noGroupsAllowed), .admitted, .read (some .noEnumeration),
        .read (some .rawTypeOperandInvalid)] := by
  native_decide

/- **The category read's non-Enumeration class answers ahead of the field's value gates and of the
   category's own lookup**, on a comparison and as a membership's member
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
   A String, a partially known Date and a full Date draw it alike, so no date gate answers first, and
   a category the String does not declare draws it rather than the unknown-category class. An
   unstarred repeatable group meets the walk before it. -/
example :
    [conditionView (.compareEnumeration .equal (grid "Other") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Partial") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Due") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Other") (.category "Nope") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Items") (.category "Band") "Hi"),
      conditionView (.enumerationFieldValueMembership .included (.direct (grid "Other"))
        [.category (grid "Note") "Band"]),
      conditionView (.enumerationFieldValueMembership .included (.direct (grid "Other"))
        [.category (grid "Other") "Band"])] =
      [.read (some .noEnumeration), .read (some .noEnumeration), .read (some .noEnumeration),
        .read (some .noEnumeration), .read (some .noWildcard), .read (some .noEnumeration),
        .read (some .noEnumeration)] := by
  native_decide

/- **An entity list's category member asks the same class once the walk passes**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
   a category read of a Number inside `Sum` draws the non-Enumeration class, and one of an unstarred
   repeatable field meets the walk first, as a bracketed category read of such a field does. A list
   that dropped the category would admit the first row and sum the Number. -/
example :
    let numberList (first : SurfaceFieldEntityOperand) : ReadView :=
      match elaborateNumberEntitySource model ["Grid"]
          { first, rest := [.field (absolute ["Grid", "Ledger"] "Total")] } with
      | .ok _ => .admitted
      | .error (.shape (.resolve error)) => .read error.diagnostic?
      | .error _ => .carrier
    [numberList (.field (grid "Amount") (.projected "Band")),
      numberList (.field (absolute items.path "Qty") (.projected "Band")),
      numberList (.field (grid "Amount"))] =
      [.read (some .noEnumeration), .read (some .noWildcard), .admitted] := by
  native_decide

/- The same class answers inside `FieldValuesNotUnique` over two Dates (row `d3`). A computation's
   fixed-target list asks it too, before its list-wide walk, an order no row measures. -/
example :
    let unique :=
      match elaborateTemporalValuesNotUniqueSource model ["Grid"]
          { first := .field (grid "Due") (.projected "Band"), rest := [.field (grid "DueCopy")] } with
      | .ok _ => ReadView.admitted
      | .error (.shape (.resolve error)) => .read error.diagnostic?
      | .error _ => .carrier
    let fixedTarget :=
      match elaborateNumberEntitySource model ["Grid"]
          { first := .field (grid "Amount") (.projected "Band"),
            rest := [.field (absolute ["Grid", "Ledger"] "Total")] } (fixedTargetGroup? := some ["Grid"]) with
      | .ok _ => ReadView.admitted
      | .error (.shape (.resolve error)) => .read error.diagnostic?
      | .error _ => .carrier
    [unique, fixedTarget] = [.read (some .noEnumeration), .read (some .noEnumeration)] := by
  native_decide

/- **A scalar membership's plain subject is an entity whose group refusal waits for the members**,
   while a category subject's chain answers as it is read
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites),
   [checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
   A group or a root subject beside a raw member draws the raw class and beside a clean one the group
   class, while an unstarred repeatable group, a name resolving to nothing, a category read of a group
   and a category read of a String answer ahead of a raw member. A subject resolved ahead of the
   members reports the fixed group and the root as names resolving to nothing. -/
example :
    [conditionView (.stringFieldValueMembership .included (grid "Ledger") [grid "Note"]),
      conditionView (.stringFieldValueMembership .included (grid "Ledger") [grid "Other"]),
      conditionView (.enumerationFieldValueMembership .included (.category (grid "Ledger") "Band")
        [.direct (grid "Note")]),
      conditionView (.stringFieldValueMembership .included (absolute [] "Grid") [grid "Note"]),
      conditionView (.stringFieldValueMembership .included (absolute [] "Grid") [grid "Other"]),
      conditionView (.stringFieldValueMembership .included (grid "Items") [grid "Note"]),
      conditionView (.stringFieldValueMembership .included (grid "Items") [grid "Other"]),
      conditionView (.stringFieldValueMembership .included (grid "NoSuch") [grid "Note"]),
      conditionView (.enumerationFieldValueMembership .included (.category (grid "Other") "Band")
        [.direct (grid "Note")])] =
      [.read (some .rawTypeOperandInvalid), .read (some .noGroupsAllowed),
        .read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid),
        .read (some .noGroupsAllowed), .read (some .noWildcard), .read (some .noWildcard),
        .read (some .invalidEntity), .read (some .noEnumeration)] := by
  native_decide

private def patternDiagnostic? (name : String) : Option (Option KernelStaticDiagnostic) :=
  (errorOf (elaborateStringPatternCondition (fun _ => .compiled fun _ => true) model ["Grid"]
    { op := .matched, field := grid name, source := "a" })).map
      StringPatternConditionElabError.diagnostic?

/- **The pattern comparison's field is a field-value read**, so its gates answer ahead of the
   comparison's own kind class ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)): a group, a
   partially known Date and a raw String draw the read's classes, a Date of full precision the
   pattern's kind class, and a String is admitted. -/
example :
    ["Ledger", "Partial", "Note", "Due", "Other"].map patternDiagnostic? =
      [some (some .noGroupsAllowed), some (some .invalidDateType), some (some .rawTypeOperandInvalid),
        some (some .invalidTypeForPatternComparison), none] := by
  native_decide

private def rangeView (left right : String) : ReadView :=
  viewOf (fun | ValidationConditionAssemblyError.fieldReference error => some error | _ => none)
    (CheckedValidationCondition.fromIteratedDateRangeEquality model ["Grid"] .equal (grid left)
      (grid right))

/- **A DateRange comparison's sides are field-value reads**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)). A group on either side draws the group
   class and a raw String partner the raw class, while two DateRanges are admitted. Resolving both
   sides without the gates reports the group as a name resolving to nothing and leaves the raw String
   to the comparison. -/
example :
    [rangeView "Ledger" "Span", rangeView "Span" "Ledger", rangeView "Span" "Note",
      rangeView "Span" "Span2"] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .rawTypeOperandInvalid), .admitted] := by
  native_decide

private def constructionView (stored : String) : ReadView :=
  viewOf (fun | ValidationConditionAssemblyError.fieldReference error => some error | _ => none)
    (CheckedValidationCondition.fromIteratedDateRangeConstructionAgainstStored model ["Grid"]
      (grid "Due") (grid "Due") (grid stored) .right .equal)

/- **A constructed range's stored partner is read the same way**, on the assumption that the
   stored-against-stored rows carry to it: no row measures this comparison. A group partner draws the
   group class and a raw String the raw class, where resolving the partner without the gates reports
   the group as a name resolving to nothing, while a DateRange passes the read and meets this
   fixture's own construction refusal. -/
example : ["Ledger", "Note", "Span"].map constructionView =
    [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid), .carrier] := by
  native_decide

private def itemsQty : SurfaceFieldPath := absolute items.path "Qty"

/-- A single-group filter rule over `Items` whose body compares `leftField`, read on the candidate
    row, with the outer row's `Qty`. -/
private def filterRule (leftField : SurfaceFieldPath) : SurfaceSingleCorrelatedRule where
  errorField := itemsQty
  guardField := itemsQty
  valueField := { base := .absolute, groupsBeforeStar := ["Grid"], starredGroup := "Items", field := "Qty" }
  having := .compareNumbers .equal { origin := .inner, field := leftField }
    { origin := .outer, field := itemsQty }

/- **The single-group filter route's body reads ask the gates too**, as the star route's do: the
   level the filter iterates and a fixed group draw the group class, and a raw String the raw class
   ahead of the route's requirement that the field sit in the filtered group, whose iteration class a
   Number outside that group still draws. -/
example :
    [grid "Items", grid "Ledger", grid "Note", grid "Amount", itemsQty].map (fun leftField =>
      (errorOf (elaborateSingleCorrelatedRule model ["Grid"] (filterRule leftField))).map
        CorrelationElabError.diagnostic?) =
      [some (some .noGroupsAllowed), some (some .noGroupsAllowed),
        some (some .rawTypeOperandInvalid), some (some .noIterationForWildcard), none] := by
  native_decide

/- **A leaf reading a field outside the filtered group beside a leaf reading its iterated level is
   admitted**, so this route's refusal of it claims no class, and a partially known Date in the body
   draws the date class
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
   The kernel rows order their sides, which this route does not carry; an equality asks the same reads
   ahead of any comparison class. Claiming the iteration class for the first row is the wrong account. -/
example :
    let inner (field : SurfaceFieldPath) : SurfaceHavingNumberRef := { origin := .inner, field }
    [.compareNumbers .equal (inner itemsQty) (inner (grid "Amount")),
      .compareNumbers .equal (inner (grid "Partial")) (inner (grid "Due"))].map (fun having =>
      (errorOf (elaborateSingleCorrelatedRule model ["Grid"] { filterRule itemsQty with having })).map
        CorrelationElabError.diagnostic?) =
      [some none, some (some .invalidDateType)] := by
  native_decide

/- **Each leaf's reads and comparison class answer as the leaf closes, and the route's placement
   requirement only after the whole body**, as the filter's own chain is asked around it
   ([`spec/07`](../../spec/07-repetition-and-iteration.md)). A first leaf reading a field outside the
   filtered group beside a group or a raw String draws that read's class, where asking each leaf's
   placement as it is read draws the iteration class. -/
example :
    let twoLeaves (partner : String) : SurfaceSingleCorrelatedRule :=
      { filterRule (grid "Amount") with
        having := .and (.compareNumbers .equal { origin := .inner, field := grid "Amount" }
            { origin := .inner, field := grid partner })
          (.compareNumbers .equal { origin := .inner, field := itemsQty }
            { origin := .outer, field := itemsQty }) }
    ["Ledger", "Note"].map (fun partner =>
      (errorOf (elaborateSingleCorrelatedRule model ["Grid"] (twoLeaves partner))).map
        CorrelationElabError.diagnostic?) =
      [some (some .noGroupsAllowed), some (some .rawTypeOperandInvalid)] := by
  native_decide

/- **A later leaf's read does not answer ahead of an earlier leaf's comparison class.** An ordering of
   a String against a Number, or an equality across scales, ahead of a leaf reading a group or a raw
   String draws its own class, where asking every read of the body first draws the later read's.
   A String leaf, which this route does not represent, still asks its read's gates ahead of an
   earlier leaf's placement. -/
example :
    let inner (field : SurfaceFieldPath) : SurfaceHavingNumberRef := { origin := .inner, field }
    let correlated : SurfaceCorrelatedHaving :=
      .compareNumbers .equal (inner itemsQty) { origin := .outer, field := itemsQty }
    let body (having : SurfaceCorrelatedHaving) : Option (Option KernelStaticDiagnostic) :=
      (errorOf (elaborateSingleCorrelatedRule model ["Grid"] { filterRule itemsQty with having })).map
        CorrelationElabError.diagnostic?
    let stringLeaf (field : String) : SurfaceCorrelatedHaving :=
      .compareStrings .equal { origin := .inner, field := grid field } "x"
    [body (.and (.compareNumbers .less (inner (absolute items.path "Label")) (inner itemsQty))
        (.and (.compareNumbers .equal (inner itemsQty) (inner (grid "Ledger"))) correlated)),
      body (.and (.compareNumbers .equal (inner itemsQty) (inner (absolute items.path "Price")))
        (.and (.compareNumbers .equal (inner itemsQty) (inner (grid "Note"))) correlated)),
      body (.and (.compareNumbers .equal (inner (grid "Amount")) (inner itemsQty)) (stringLeaf "Note")),
      body (.and (.compareNumbers .equal (inner (grid "Amount")) (inner itemsQty)) (stringLeaf "Ledger"))] =
      [some (some .invalidTypeForComparison), some (some .invalidCompareDecimalPlaces),
        some (some .rawTypeOperandInvalid), some (some .noGroupsAllowed)] := by
  native_decide

end A12Kernel.Conformance.FieldValueReadCarriers
