import A12Kernel.Elaboration.ConditionDiagnostic
import A12Kernel.Conformance.FieldCopyComparison

/-! # A rule condition's refusal classes on the plain comparison

Every expected class below is a retained Kernel row of the [condition-class grid](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection),
run on the [field-copy grid's](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)
eleven-kind model, which this module shares. Each row is `FieldFilled(Note2) And <comparison>` from
`/Order`. `none:` names the refusal arm this fragment projects to no class, deliberately: a same-kind
Number, DateRange or Boolean field pair, which this flat route does not admit although the Kernel
does, a scale mismatch between two Number fields, which it does not reach, and a clock literal on a
temporal field. Tags drop the `MVK_` and `MVK_INVALID_COMPARE_` prefixes. -/

namespace A12Kernel.Conformance.ConditionDiagnostic

open A12Kernel
open A12Kernel.Conformance.FieldCopyComparison (model)

private def fields : List String :=
  ["Note", "Qty", "Amount", "Due", "At", "Stamp", "Window", "Flag", "Signed", "Plain", "Labelled"]

private def onOrder (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def tag (code : String) : String :=
  ((code.replace "MVK_INVALID_COMPARE_" "").replace "MVK_" "")

/-- The refusal's constructor, so a lock tells one unclassed arm from another. -/
private def arm (error : ElabError) : String :=
  ((reprStr error).takeWhile (!·.isWhitespace)).replace "A12Kernel.ElabError." ""

private def classOn (onModel : FlatModel) (condition : SurfaceCondition) : String :=
  match elaborate onModel ["Order"]
      (.and (.fieldFilled { base := .relative 0, groups := [], field := "Note2" }) condition) with
  | .ok _ => "admitted"
  | .error error =>
      let surface := SurfaceCondition.and
        (.fieldFilled { base := .relative 0, groups := [], field := "Note2" }) condition
      ((surface.refusalDiagnostic? error).map (tag ·.kernelCode)).getD ("none:" ++ arm error)

private def classOf := classOn model

/- Two fields compared under `==`: one kind arm over the pair answers in either order, the walk a
copied field meets, except that two Confirm fields draw the Confirm class, which the equality operator
narrows ([`kf383`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf383)); two temporal fields
of different families meet the format question; and a String and an Enumeration meet the display
arm. A field is compared with its twin on the diagonal. -/
example :
    fields.map (fun left => fields.map fun right =>
      classOf (.compareFields .equal (onOrder left) (onOrder (if left == right then right ++ "2" else right)))) =
    [
      ["admitted", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "admitted", "ENUM_TO_STRING"],
      ["TO_ENUM_OR_STRING", "none:temporalOperandKindMismatch", "none:temporalOperandKindMismatch", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"],
      ["TO_ENUM_OR_STRING", "none:temporalOperandKindMismatch", "none:temporalOperandKindMismatch", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_DATE", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"],
      ["TO_DATE_RANGE", "TO_DATE_RANGE", "TO_DATE_RANGE", "TO_DATE", "TO_DATE", "TO_DATE", "none:temporalOperandKindMismatch", "TO_YESNO", "TO_YES", "TO_DATE_RANGE", "TO_DATE_RANGE"],
      ["TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "none:temporalOperandKindMismatch", "TO_YES", "TO_YESNO", "TO_YESNO"],
      ["TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES", "TO_YES"],
      ["admitted", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "admitted", "ENUM_TO_STRING"],
      ["ENUM_TO_STRING", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "ENUM_TO_STRING", "admitted"]] := by
  native_decide

/- A field against a String, a Number, a date, `True` and `False` literal: the literal ladder, where a
Boolean or Confirm field outranks every literal and a date literal reports its own family, and the
Confirm field refuses `False`. -/
example :
    fields.map (fun name =>
      [.string "x", .number 5, .date TemporalComponents.fullDate ⟨0⟩, .boolean true, .boolean false].map
        fun (literal : SurfaceLiteral) => classOf (.compare .equal (onOrder name) literal)) =
    [
      ["admitted", "TO_ENUM_OR_STRING", "TO_DATE", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"],
      ["TO_ENUM_OR_STRING", "admitted", "TO_DATE", "INCONSISTENT_TYPES_COMPARED", "INCONSISTENT_TYPES_COMPARED"],
      ["TO_ENUM_OR_STRING", "admitted", "TO_DATE", "INCONSISTENT_TYPES_COMPARED", "INCONSISTENT_TYPES_COMPARED"],
      ["TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_DATE"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE"],
      ["TO_DATE_RANGE", "TO_DATE_RANGE", "TO_DATE", "TO_DATE_RANGE", "TO_DATE_RANGE"],
      ["TO_YESNO", "TO_YESNO", "TO_YESNO", "admitted", "admitted"],
      ["TO_YES", "TO_YES", "TO_YES", "admitted", "TO_YES"],
      ["INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON", "TO_ENUM_OR_STRING", "TO_DATE", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"],
      ["INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON", "TO_ENUM_OR_STRING", "TO_DATE", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"]] := by
  native_decide

private def today (position : SurfacePointInTimePosition) (name : String) : SurfaceCondition :=
  .compareToday .equal position (onOrder name)
private def now (position : SurfacePointInTimePosition) (name : String) : SurfaceCondition :=
  .compareNow .equal position (onOrder name)

/- `Today` and `Now` meet the same kind arm as a temporal partner, in either position, and a date-only
field compared with `Now` draws the date class. -/
example :
    [now .right "At", today .left "At", now .left "Due", today .right "Flag", today .right "Note", today .right "Qty", now .right "Flag", today .right "Window", now .right "Signed", now .right "Note", today .right "Plain", today .right "Due", now .right "Stamp"].map classOf =
    ["TO_DATE", "TO_DATE", "TO_DATE", "TO_YESNO", "TO_DATE", "TO_DATE", "TO_YESNO", "TO_DATE", "TO_YES", "TO_DATE", "TO_DATE", "admitted", "admitted"] := by
  native_decide

/- `BaseYear` meets the kind arm as a **Number** partner, so a String draws the text class and a
DateRange its own, while a Date and a scale-0 Number are admitted and a scale-2 Number draws the
scale class; a model with no Base Year refuses the operand first. -/
example :
    let withYear := classOn { model with baseYear := some 2024 }
    [withYear (.compareBaseYear .equal .right (onOrder "At")), withYear (.compareBaseYear .equal .right (onOrder "Due")), withYear (.compareBaseYear .equal .right (onOrder "Qty")), withYear (.compareBaseYear .equal .right (onOrder "Flag")), withYear (.compareBaseYear .equal .right (onOrder "Note")), withYear (.compareBaseYear .equal .right (onOrder "Amount")), withYear (.compareBaseYear .equal .left (onOrder "Stamp")), withYear (.compareBaseYear .equal .right (onOrder "Signed")), withYear (.compareBaseYear .equal .right (onOrder "Window"))] =
      ["TO_DATE", "admitted", "admitted", "TO_YESNO", "TO_ENUM_OR_STRING", "DEC_PLACES", "TO_DATE", "TO_YES", "TO_DATE_RANGE"] ∧
    classOf (.compareBaseYear .equal .right (onOrder "Due")) = "NO_BASE_YEAR" ∧
    classOf (.compareBaseYear .equal .right (onOrder "Qty")) = "NO_BASE_YEAR" := by
  native_decide

/- A Base Year range endpoint meets the kind arm as a **date** partner, unlike the year itself. -/
example :
    let range (endpoint : BaseYearRangeEndpoint) (name : String) :=
      classOn { model with baseYear := some 2024 }
        (.compareBaseYearRange .equal .right endpoint (onOrder name))
    [range .start "Note", range .start "Qty", range .start "Flag", range .finish "Signed",
      range .start "Window", range .start "Due", range .start "At", range .finish "Plain"] =
      ["TO_DATE", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "admitted", "TO_DATE", "TO_DATE"] := by
  native_decide

/- An Enumeration literal it does not declare, two Enumerations whose labels conflict, and `Length` on
a Number. -/
example :
    classOf (.compare .equal (onOrder "Plain") (.string "PENDING")) = "INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON" ∧
      classOf (.compareFields .equal (onOrder "Plain") (onOrder "Swapped")) = "ENUM_TO_STRING" ∧
      classOf (.compareFields .equal (onOrder "Plain") (onOrder "Wide")) = "admitted" ∧
      classOf (.lengthCompare .greater (onOrder "Qty") { value := 2, authoredScale := 0 }) = "NO_STRING" ∧
      classOf (.lengthCompare .greater (onOrder "Note") { value := 2, authoredScale := 0 }) = "admitted" := by
  native_decide


/- The rows the first grid left unlocked: a Time against `Today`, a Date against `Now`, and a field
against itself, admitted. -/
example :
    [classOf (.compareToday .equal .right (onOrder "At")), classOf (.compareNow .equal .right (onOrder "Due")),
      classOf (.compareFields .equal (onOrder "Note") (onOrder "Note"))] =
      ["TO_DATE", "TO_DATE", "admitted"] := by
  native_decide

/- A clock literal draws the ladder's date family on every non-temporal field. On the three temporal
fields it meets the date-literal component gate, unclassed here: the Kernel draws the date class on
the Date and DateTime fields and admits it on the Time field, an admission this route refuses. -/
example :
    fields.map (fun name => classOf (.compare .equal (onOrder name) (.date TemporalComponents.time ⟨37800000⟩))) =
      ["TO_DATE", "TO_DATE", "TO_DATE", "none:invalidTemporalLiteralComponents",
        "none:invalidTemporalLiteralComponents", "none:invalidTemporalLiteralComponents", "TO_DATE",
        "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"] := by
  native_decide

/- The [domain rows](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection):
`BaseYear`, `Today`, `Now` and a range endpoint written on the left meet the same arm as on the right,
the `End` endpoint the same as `Start` on six further kinds, and `Length` refuses a Boolean, an
Enumeration and a DateRange as it does a Number. `Length` under `==` is refused here by its operator
gate, where the Kernel answers the kind class. -/
example :
    let year := classOn { model with baseYear := some 2024 }
    let two : DecodedNumericLiteral := { value := 2, authoredScale := 0 }
    [year (.compareBaseYear .equal .left (onOrder "Note")), year (.compareBaseYear .equal .left (onOrder "Window")),
      year (.compareBaseYear .equal .left (onOrder "Flag")), year (.compareToday .equal .left (onOrder "Note")),
      year (.compareToday .equal .left (onOrder "Flag")), year (.compareToday .equal .left (onOrder "Qty")),
      year (.compareNow .equal .left (onOrder "Qty")), year (.compareNow .equal .left (onOrder "Plain")),
      year (.compareBaseYearRange .equal .left .start (onOrder "Qty"))] =
      ["TO_ENUM_OR_STRING", "TO_DATE_RANGE", "TO_YESNO", "TO_DATE", "TO_YESNO", "TO_DATE", "TO_DATE",
        "TO_DATE", "TO_DATE"] ∧
    ["Note", "Qty", "Flag", "Window", "Due", "At"].map
        (fun name => year (.compareBaseYearRange .equal .right .finish (onOrder name))) =
      ["TO_DATE", "TO_DATE", "TO_YESNO", "TO_DATE", "admitted", "TO_DATE"] ∧
    [classOf (.lengthCompare .greater (onOrder "Flag") two), classOf (.lengthCompare .greater (onOrder "Plain") two),
      classOf (.lengthCompare .greater (onOrder "Window") two), classOf (.lengthCompare .equal (onOrder "Qty") two)] =
      ["NO_STRING", "NO_STRING", "NO_STRING", "none:unsupportedOperator"] ∧
    classOf (.compareBaseYear .equal .left (onOrder "Note")) = "NO_BASE_YEAR" := by
  native_decide

/- Outside the measured shapes the projection answers nothing, though each arm below names a class
on the measured ones. The Kernel draws `MVK_INVALID_TYPE_FOR_COMPARISON` for the first three under an
ordering ([`kf270`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf270)), admits two Confirm fields
under `!=` ([`kf383`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf383)) and a Date ordered against
`Now` ([`spec/05`](../../spec/05-dates-and-time.md)), and answers a value list's undeclared literal and a String in a Number list with
classes of their own. -/
example :
    [classOf (.compare .greater (onOrder "Window") (.number 0)), classOf (.compare .greater (onOrder "Plain") (.number 0)),
      classOf (.compareFields .greater (onOrder "Qty") (onOrder "Signed")),
      classOf (.compareFields .notEqual (onOrder "Signed") (onOrder "Signed2")),
      classOf (.compareNow .greater .right (onOrder "Due")),
      classOf (.enumerationValueList .atLeastOne [.direct (onOrder "Plain")] ["PENDING"]),
      classOf (.numberValueMembership .included (onOrder "Note") [1, 2])] =
      ["none:literalKindMismatch", "none:literalKindMismatch", "none:temporalOperandKindMismatch",
        "none:temporalOperandKindMismatch", "none:temporalNowRequiresTime", "none:enumerationOperand",
        "none:literalKindMismatch"] := by
  native_decide

/- The [settling rows](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection)
for the remaining partner positions: `BaseYear` on the left opposite a Time, a Confirm, a scale-2 Number
and an Enumeration, an Enumeration on either side, and both endpoints on the left opposite a String, a
Number and an Enumeration, each beside an admitted Date or scale-0 Number control. -/
example :
    let year := classOn { model with baseYear := some 2024 }
    [year (.compareBaseYear .equal .left (onOrder "At")), year (.compareBaseYear .equal .left (onOrder "Signed")),
      year (.compareBaseYear .equal .left (onOrder "Amount")), year (.compareBaseYear .equal .left (onOrder "Plain")),
      year (.compareBaseYear .equal .right (onOrder "Plain")), year (.compareBaseYear .equal .right (onOrder "Labelled")),
      year (.compareBaseYear .equal .left (onOrder "Due")), year (.compareBaseYear .equal .left (onOrder "Qty")),
      year (.compareBaseYearRange .equal .left .finish (onOrder "Note")),
      year (.compareBaseYearRange .equal .left .finish (onOrder "Qty")),
      year (.compareBaseYearRange .equal .left .finish (onOrder "Plain")),
      year (.compareBaseYearRange .equal .left .start (onOrder "Plain")),
      year (.compareBaseYearRange .equal .right .start (onOrder "Plain")),
      year (.compareBaseYearRange .equal .left .finish (onOrder "Due"))] =
      ["TO_DATE", "TO_YES", "DEC_PLACES", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING",
        "admitted", "admitted", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "admitted"] := by
  native_decide

/- The text-field form over two direct reads is the same measured pair as the field-pair form, so it
draws the same class, while a category read on either side stays outside the measured shapes. -/
example :
    let pairs := [("Note", "Labelled"), ("Plain", "Labelled"), ("Labelled", "Note"), ("Note", "Plain")]
    pairs.map (fun (left, right) =>
        classOf (.compareTextFields .equal (.direct (onOrder left)) (.direct (onOrder right)))) =
      pairs.map (fun (left, right) => classOf (.compareFields .equal (onOrder left) (onOrder right))) ∧
    classOf (.compareTextFields .equal (.direct (onOrder "Note")) (.direct (onOrder "Labelled"))) =
      "ENUM_TO_STRING" ∧
    (classOf (.compareTextFields .equal (.category (onOrder "Plain") "Band") (.direct (onOrder "Note")))).startsWith "none:" := by
  native_decide

end A12Kernel.Conformance.ConditionDiagnostic
