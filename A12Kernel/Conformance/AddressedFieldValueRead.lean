import A12Kernel.Conformance.Elaboration.Support
import A12Kernel.Elaboration.AddressedDateRangeBoundPart
import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.AddressedFieldValueAsNumber
import A12Kernel.Elaboration.AddressedFieldValueAsString
import A12Kernel.Elaboration.AddressedNumberAbs
import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.AddressedRangeAsNumber
import A12Kernel.Elaboration.AddressedRepetitionComputation
import A12Kernel.Elaboration.AddressedStringLength
import A12Kernel.Elaboration.ParallelComputationClearing

/-! # The field-value read's gates on the addressed and parallel computation carriers

A computation writing a repeatable target reads the same way as one writing a nonrepeatable target
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
a bracket read asks the group gate and then the two value gates ahead of the carrier's kind check, an
operator's parameter asks the group gate alone and meets its operator's own gates, and a category read
of a field declaring no Enumeration draws its own class. The walk starts from the target's scope, so a
group whose level the target binds passes it and draws the group class. The fixture mirrors the grid's
model. A carrier that projects no Kernel class of its own is read through its resolution failure's
class, and a refusal of the carrier's own is kept apart from one that projects no class.
-/

namespace A12Kernel.Conformance.AddressedFieldValueRead

open A12Kernel
open A12Kernel.Conformance.Elaboration.Support (absolute dispatchDateComponents)

private def items : RepeatableGroupDecl := { level := 10, path := ["Grid", "Items"] }

private def grades : EnumerationDeclaration :=
  { storedTokens := ["A", "B"], categories := [{ name := "Band", tokens := ["Hi", "Lo"] }] }

private def otherDecl : FlatFieldDecl :=
  { id := 1, groupPath := ["Grid"], name := "Other", policy := { kind := .string } }

private def noteDecl : FlatFieldDecl :=
  { otherDecl with id := 3, name := "Note", stringValueMode := .raw
                   stringPolicy := { lineBreaksPermitted := true } }

private def amountDecl : FlatFieldDecl :=
  { id := 4, groupPath := ["Grid"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } } }

private def partialDecl : FlatFieldDecl :=
  { id := 6, groupPath := ["Grid"], name := "Partial",
    policy := { kind := .temporal .date dispatchDateComponents },
    temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }

private def gradeDecl : FlatFieldDecl :=
  { id := 7, groupPath := ["Grid"], name := "Grade", policy := { kind := .enumeration },
    enumeration := some grades }

private def totalDecl : FlatFieldDecl :=
  { amountDecl with id := 9, groupPath := ["Grid", "Ledger"], name := "Total" }

private def qtyDecl : FlatFieldDecl :=
  { amountDecl with id := 10, groupPath := items.path, name := "Qty", repeatableScope := [items.level] }

private def labelDecl : FlatFieldDecl :=
  { otherDecl with id := 11, groupPath := items.path, name := "Label", repeatableScope := [items.level] }

private def tierDecl : FlatFieldDecl :=
  { gradeDecl with id := 15, groupPath := items.path, name := "Tier", repeatableScope := [items.level] }

private def spanDecl : FlatFieldDecl :=
  { id := 12, groupPath := ["Grid"], name := "Span", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def model : FlatModel :=
  { fields := [otherDecl, noteDecl, amountDecl, partialDecl, gradeDecl, totalDecl, qtyDecl, labelDecl,
      tierDecl, spanDecl],
    repeatableGroups := [items] }

private def grid (field : String) : SurfaceFieldPath := absolute ["Grid"] field

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

private def placementResolve? : AddressedNumericPlacementElabError → Option ResolveError
  | .source error => some error
  | _ => none

private def numberSourceResolve? : AddressedNumberSourceElabError → Option ResolveError
  | .placement cause => placementResolve? cause
  | .sourceRead refusal => some refusal
  | .sourceNotNumber _ _ => none

private def numberFieldResolve? : AddressedNumberFieldElabError → Option ResolveError
  | .placement cause => placementResolve? cause
  | .sourceRead refusal => some refusal
  | _ => none

/-- A direct copy, `Abs` and a sum of two fields into `Items/Qty`. -/
private def directViews (source : String) : List ReadView :=
  [viewOf numberFieldResolve? (checkAddressedNumberField model ["Grid"] qtyDecl.id (grid source)),
    viewOf numberFieldResolve? (checkAddressedNumberAbs model ["Grid"] qtyDecl.id (grid source)),
    viewOf (fun | AddressedNumberBinaryElabError.pair (.left cause) | .pair (.right cause) =>
                    numberSourceResolve? cause
                | _ => none)
      (checkAddressedNumberBinary model ["Grid"] qtyDecl.id (grid "Amount") (grid source) .add)]

/- **A bracket read into a repeatable Number target asks the group gate and then the value gates**,
   as a direct copy, inside `Abs` and as either side of a sum: a group draws the group class, a raw
   String the raw class and a partially known Date the date class, while a Number field is admitted.
   The target's own group passes the walk, which its scope binds, and draws the group class too.
   Resolving the source without the gates reports a group as a name resolving to nothing and each
   value refusal as the carrier's Number check. The rows measure every source as a direct copy
   (`c1` to `c3`, `y5`) and the fixed group and raw String inside `Abs` and a sum (`g16` to `g19`); the
   partial Date and the target's own group inside `Abs` and a sum share the one source check and are
   not measured there. -/
example :
    ["Ledger", "Note", "Partial", "Items", "Amount"].map directViews =
      [List.replicate 3 (.read (some .noGroupsAllowed)),
        List.replicate 3 (.read (some .rawTypeOperandInvalid)),
        List.replicate 3 (.read (some .invalidDateType)),
        List.replicate 3 (.read (some .noGroupsAllowed)),
        List.replicate 3 .admitted] := by
  native_decide

/- **An operator's parameter asks the group gate alone** and meets its operator's own gates, so a
   group draws the group class inside `Length`, `FieldValueAsNumber`, `RangeAsNumber` and a DateRange
   endpoint's component, while a raw String and a partially known Date draw no read class: `Length`,
   `FieldValueAsNumber` and `RangeAsNumber` refuse them with their own gates, which these carriers do
   not project. Asking the read's value gates would draw the raw and the date class. -/
example :
    [viewOf (fun | AddressedStringLengthElabError.placement cause => placementResolve? cause | _ => none)
        (checkAddressedStringLength model ["Grid"] qtyDecl.id (grid "Ledger")),
      viewOf (fun | AddressedFieldValueAsNumberElabError.placement cause => placementResolve? cause
                  | _ => none)
        (checkAddressedFieldValueAsNumber model ["Grid"] qtyDecl.id (.direct (grid "Ledger"))),
      viewOf (fun | AddressedRangeAsNumberElabError.placement cause => placementResolve? cause | _ => none)
        (checkAddressedRangeAsNumber model ["Grid"] qtyDecl.id (grid "Ledger") 1 2),
      viewOf (fun | AddressedDateRangeBoundPartElabError.placement cause => placementResolve? cause
                  | _ => none)
        (checkAddressedDateRangeBoundPart model ["Grid"] qtyDecl.id (grid "Ledger") .start .year),
      viewOf (fun | AddressedStringLengthElabError.placement cause => placementResolve? cause | _ => none)
        (checkAddressedStringLength model ["Grid"] qtyDecl.id (grid "Note")),
      viewOf (fun | AddressedStringLengthElabError.placement cause => placementResolve? cause | _ => none)
        (checkAddressedStringLength model ["Grid"] qtyDecl.id (grid "Partial")),
      viewOf (fun | AddressedFieldValueAsNumberElabError.placement cause => placementResolve? cause
                  | _ => none)
        (checkAddressedFieldValueAsNumber model ["Grid"] qtyDecl.id (.direct (grid "Note"))),
      viewOf (fun | AddressedFieldValueAsNumberElabError.placement cause => placementResolve? cause
                  | _ => none)
        (checkAddressedFieldValueAsNumber model ["Grid"] qtyDecl.id (.direct (grid "Partial"))),
      viewOf (fun | AddressedRangeAsNumberElabError.placement cause => placementResolve? cause | _ => none)
        (checkAddressedRangeAsNumber model ["Grid"] qtyDecl.id (grid "Note") 1 2),
      viewOf (fun | AddressedRangeAsNumberElabError.placement cause => placementResolve? cause | _ => none)
        (checkAddressedRangeAsNumber model ["Grid"] qtyDecl.id (grid "Other") 1 2),
      viewOf (fun | AddressedDateRangeBoundPartElabError.placement cause => placementResolve? cause
                  | _ => none)
        (checkAddressedDateRangeBoundPart model ["Grid"] qtyDecl.id (grid "Span") .start .year)] =
      List.replicate 4 (.read (some .noGroupsAllowed)) ++ List.replicate 5 .carrier ++
        [.admitted, .admitted] := by
  native_decide

private def fieldValueAsStringView (source : String) : ReadView :=
  viewOf (fun | AddressedFieldValueAsStringElabError.source cause => some cause | _ => none)
    (checkAddressedFieldValueAsString model ["Grid"] labelDecl.id (grid source))

/- **`FieldValueAsString`'s parameter into a repeatable String target asks the group gate alone**: a
   group and the target's own group draw the group class, and a raw String meets the conversion's
   Number gate rather than the read's raw class. -/
example :
    ["Ledger", "Items", "Note", "Amount"].map fieldValueAsStringView =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .carrier, .admitted] := by
  native_decide

private def enumerationView (source : SurfaceTextFieldOperand) : ReadView :=
  viewOf (fun | AddressedEnumerationComputationElabError.ordinary (.source (.resolve cause)) => some cause
              | _ => none)
    (checkAddressedEnumerationComputation model ["Grid"] tierDecl.id (.field source))

/- **A repeatable Enumeration target's copied field is a field-value read**, and a category source
   asks the group gate and then the non-Enumeration class: a group draws the group class on both, the
   target's own group too, a raw String the raw class, a partially known Date the date class and a
   category read of a String the non-Enumeration class, while another field of the domain is
   admitted. -/
example :
    [enumerationView (.direct (grid "Ledger")), enumerationView (.category (grid "Ledger") "Band"),
      enumerationView (.direct (grid "Items")), enumerationView (.direct (grid "Note")),
      enumerationView (.direct (grid "Partial")), enumerationView (.category (grid "Other") "Band"),
      enumerationView (.direct (grid "Grade"))] =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .read (some .noGroupsAllowed),
        .read (some .rawTypeOperandInvalid), .read (some .invalidDateType), .read (some .noEnumeration),
        .admitted] := by
  native_decide

private def repetitionView (operand : SurfaceNumericAtom) : ReadView :=
  viewOf (fun | AddressedRepetitionComputationElabError.source cause => some cause | _ => none)
    (checkAddressedRepetitionComputation model ["Grid"] qtyDecl.id
      (.binary .add (.atom operand) (.atom (.currentRepetition { base := .absolute, groups := items.path }))))

/- **A read beside `CurrentRepetition` asks the same gates**: a bracketed group draws the group class,
   a raw String the raw class and a partially known Date the date class, and `Length` of a group the
   group class, while a Number field is admitted. -/
example :
    [repetitionView (.field (grid "Ledger")), repetitionView (.field (grid "Note")),
      repetitionView (.field (grid "Partial")), repetitionView (.stringLength (grid "Ledger")),
      repetitionView (.field (grid "Amount"))] =
      [.read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid),
        .read (some .invalidDateType), .read (some .noGroupsAllowed), .admitted] := by
  native_decide

private def targetGroup : RepeatableGroupDecl :=
  { level := 60, path := ["Plan", "Target"], repeatability := some 2, indexField := some 1 }

private def operandGroup : RepeatableGroupDecl :=
  { level := 70, path := ["Plan", "Operand"], repeatability := some 2, indexField := some 3 }

private def thirdGroup : RepeatableGroupDecl := { level := 80, path := ["Plan", "Third"] }

/-- The parallel grid's model: two keyed repeatable groups side by side, the operand one holding a raw
    String, a partially known Date and a fixed group. -/
private def parallelModel : FlatModel :=
  let within (group : RepeatableGroupDecl) (id : FieldId) (name : String) (declaration : FlatFieldDecl) :
      FlatFieldDecl :=
    { declaration with id, groupPath := group.path, name, repeatableScope := [group.level] }
  { fields := [within targetGroup 1 "Key" otherDecl, within targetGroup 2 "Result" amountDecl,
      within operandGroup 3 "Key" otherDecl, within operandGroup 4 "Input" amountDecl,
      within operandGroup 20 "Memo" noteDecl, within operandGroup 21 "Part" partialDecl,
      { within operandGroup 22 "Total" amountDecl with groupPath := operandGroup.path ++ ["Sub"] },
      within thirdGroup 23 "Extra" amountDecl],
    repeatableGroups := [targetGroup, operandGroup, thirdGroup] }

/- **A parallel operand is a field-value read**: a fixed group inside the operand group and the operand
   group itself draw the group class, since the index join binds the operand's level, and a raw String
   and a partially known Date draw their value classes, while a Number is admitted. The last row names
   an unkeyed repeatable group beside the target, which the join does not bind; it takes the shared
   walk's missing-star class, and no row measures it on this carrier. -/
example :
    [absolute operandGroup.path "Sub", absolute ["Plan"] "Operand", absolute operandGroup.path "Memo",
      absolute operandGroup.path "Part", absolute operandGroup.path "Input", absolute ["Plan"] "Third"].map
      (fun reference =>
        viewOf (fun | ParallelComputationPlanError.operandResolve cause => some cause | _ => none)
          (checkParallelNumericComputationClearingPlan parallelModel ["Plan"] 2 reference)) =
      [.read (some .noGroupsAllowed), .read (some .noGroupsAllowed), .read (some .rawTypeOperandInvalid),
        .read (some .invalidDateType), .admitted, .read (some .noWildcard)] := by
  native_decide

/- **A bare name naming a group reads as the group, and an operator's parameter beside
   `CurrentRepetition` asks the group gate alone**: `[Ledger] + 1` draws the group class ahead of this
   carrier's own refusal of an expression carrying no repetition, which the admitted `[Amount] + 1`
   meets instead (row `c9` measures the first, `c10` admits the second). `RangeAsNumber`, a DateRange
   endpoint's component and `FieldValueAsNumber` naming a group draw the group class on this carrier by
   the parameter rule measured on the others; only `Length` is measured here (`w5`). -/
example :
    let one : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 1, authoredScale := 0 }
    let noRepetition (reference : SurfaceFieldPath) :=
      viewOf (fun | AddressedRepetitionComputationElabError.source cause => some cause | _ => none)
        (checkAddressedRepetitionComputation model ["Grid"] qtyDecl.id (.binary .add (.atom (.field reference)) one))
    [noRepetition { base := .relative 0, groups := [], field := "Ledger" }, noRepetition (grid "Amount"),
      repetitionView (.stringRange (grid "Ledger") 1 2),
      repetitionView (.dateRangeBoundPart (grid "Ledger") .start .year),
      repetitionView (.fieldValueAsNumber (.direct (grid "Ledger")))] =
      [.read (some .noGroupsAllowed), .carrier, .read (some .noGroupsAllowed),
        .read (some .noGroupsAllowed), .read (some .noGroupsAllowed)] := by
  native_decide

end A12Kernel.Conformance.AddressedFieldValueRead
