import A12Kernel.Conformance.Elaboration.Support
import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.StringComputation

/-! # The field-value read's gates on its remaining carriers

The Kernel asks the field-value read's gates as its bracket closes, ahead of the class of the
operator standing around it, on an arithmetic operand, on a computation's operand whatever the
target's kind, and on a category read
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-carriers)).
The fixture mirrors that grid's model. A carrier that projects no Kernel class of its own is read
through its resolution failure's class, and a refusal of the carrier's own is kept apart from one
that projects no class.
-/

namespace A12Kernel.Conformance.FieldValueReadCarriers

open A12Kernel
open A12Kernel.Conformance.Elaboration.Support (absolute dispatchDateComponents errorOf)

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

private def model : FlatModel :=
  { fields := [refDecl, otherDecl, copyDecl, noteDecl, amountDecl, dueDecl, partialDecl, gradeDecl,
      gradeCopyDecl, totalDecl, qtyDecl, labelDecl],
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

/- **A rule in a repeatable group reads the same way.** Its addressed operands ask the gates too, so a
   fixed group and a raw String read from the iterated level draw their classes. -/
example :
    let addressed (right : AuthoredNumericExpr SurfaceNumericAtom) :=
      viewOf numericResolve? (elaborateRepeatableNumericComparison model items.path
        { op := .ordinary .equal, left := .atom (.field (absolute items.path "Qty")), right })
    [addressed (.binary .add (field "Ledger") one), addressed (.binary .add (field "Note") one)] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid)] := by
  native_decide

private def numericComputationResolve? : NumericComputationElabError → Option ResolveError
  | .resolve error => some error
  | _ => none

/- **A Number computation's operand is a field-value read**: a group, a raw String and a partially
   known Date draw their classes ahead of the operator's, while a field of the fixed group is admitted.
   A Date of full precision passes the read and meets the operand's Number gate. -/
example :
    let computed (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      viewOf numericComputationResolve?
        (elaborateNumericComputationOperation model ["Grid"] amountDecl.id expression)
    [computed (.binary .add (field "Ledger") one), computed (.binary .add (field "Note") one),
      computed (.binary .subtract (field "Partial") one),
      computed (.binary .add (.atom (.field (absolute ["Grid", "Ledger"] "Total"))) one),
      computed (.binary .subtract (field "Due") one)] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid),
        .read (some .invalidDateType), .admitted, .carrier] := by
  native_decide

private def stringComputationResolve? : StringComputationElabError → Option ResolveError
  | .resolve error => some error
  | _ => none

/- **A String computation's copied field is a field-value read.** A group draws the group class and
   a raw String the raw class, where resolving the operand without the gates reports the group as a
   name resolving to nothing and the raw String as the carrier's own refusal. -/
example :
    let computed (source : String) :=
      viewOf stringComputationResolve?
        (elaborateStringComputationOperation model ["Grid"] copyDecl.id (.field (grid source)))
    [computed "Ledger", computed "Note", computed "Other"] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid), .admitted] := by
  native_decide

private def enumerationComputationResolve? : EnumerationComputationElabError → Option ResolveError
  | .resolve error | .source (.resolve error) => some error
  | _ => none

/- **An Enumeration computation's copied field is a field-value read**, and a category source asks
   the group gate. A group draws the group class on both and a raw String the raw class, while
   another field of the same domain is admitted. -/
example :
    let computed (source : SurfaceTextFieldOperand) :=
      viewOf enumerationComputationResolve?
        (elaborateEnumerationComputation model ["Grid"] gradeCopyDecl.id (.field source))
    [computed (.direct (grid "Ledger")), computed (.category (grid "Ledger") "Band"),
      computed (.direct (grid "Note")), computed (.direct (grid "Grade"))] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .rawTypeOperandInvalid), .admitted] := by
  native_decide

private def conditionView (condition : SurfaceCondition) : ReadView :=
  viewOf (fun | ElabError.resolve error => some error | _ => none) (elaborate model ["Grid"] condition)

/- **A category read `[F -> C]` asks the group gate**, as a membership's member and as either side
   of a text comparison: a group draws the group class ahead of the subject's kind and the category
   reader's own gates. Its value gates never answer, since only an Enumeration has a category, so a
   raw String's category read meets the category reader's refusal where its stored read draws the raw
   class. -/
example :
    let ledgerBand : SurfaceTextFieldOperand := .category (grid "Ledger") "Band"
    [conditionView (.enumerationFieldValueMembership .included (.direct (grid "Other")) [ledgerBand]),
      conditionView (.compareTextFields .equal ledgerBand (.direct (grid "Other"))),
      conditionView (.compareTextFields .equal (.direct (grid "Other")) ledgerBand),
      conditionView (.compareEnumeration .equal (grid "Grade") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Note") (.category "Band") "Hi"),
      conditionView (.compareEnumeration .equal (grid "Note") .stored "A")] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .admitted, .carrier, .read (some .rawTypeOperandInvalid)] := by
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

end A12Kernel.Conformance.FieldValueReadCarriers
