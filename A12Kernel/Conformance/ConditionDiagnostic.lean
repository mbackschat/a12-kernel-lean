import A12Kernel.Elaboration.ConditionDiagnostic
import A12Kernel.Conformance.FieldCopyComparison

/-! # A rule condition's refusal classes on the plain comparison

Every expected class below is a retained Kernel row of the [condition-class grid](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection),
run on the [field-copy grid's](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)
eleven-kind model, which this module shares. Each row is `FieldFilled(Note2) And <comparison>` from
`/Order`. `refused` marks a refusal this fragment projects to no class, deliberately: a same-kind
Number, DateRange or Boolean field pair, which this flat route does not admit although the Kernel
does, and a scale mismatch between two Number fields, which it does not reach. Tags drop the
`MVK_` and `MVK_INVALID_COMPARE_` prefixes. -/

namespace A12Kernel.Conformance.ConditionDiagnostic

open A12Kernel
open A12Kernel.Conformance.FieldCopyComparison (model)

private def fields : List String :=
  ["Note", "Qty", "Amount", "Due", "At", "Stamp", "Window", "Flag", "Signed", "Plain", "Labelled"]

private def onOrder (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def tag (code : String) : String :=
  ((code.replace "MVK_INVALID_COMPARE_" "").replace "MVK_" "")

private def classOn (onModel : FlatModel) (condition : SurfaceCondition) : String :=
  match elaborate onModel ["Order"]
      (.and (.fieldFilled { base := .relative 0, groups := [], field := "Note2" }) condition) with
  | .ok _ => "admitted"
  | .error error => (error.diagnostic?.map (tag ·.kernelCode)).getD "refused"

private def classOf := classOn model

/- Two fields compared: one kind arm over the pair answers in either order, the walk a copied field
meets, except that two Confirm fields are refused here where a copy admits them; two temporal fields
of different families meet the format question; and a String and an Enumeration meet the display
arm. A field is compared with its twin on the diagonal. -/
example :
    fields.map (fun left => fields.map fun right =>
      classOf (.compareFields .equal (onOrder left) (onOrder (if left == right then right ++ "2" else right)))) =
    [
      ["admitted", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "admitted", "ENUM_TO_STRING"],
      ["TO_ENUM_OR_STRING", "refused", "refused", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"],
      ["TO_ENUM_OR_STRING", "refused", "refused", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE_RANGE", "TO_YESNO", "TO_YES", "TO_ENUM_OR_STRING", "TO_ENUM_OR_STRING"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_DATE", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"],
      ["TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "TO_DATE", "admitted", "TO_DATE", "TO_YESNO", "TO_YES", "TO_DATE", "TO_DATE"],
      ["TO_DATE_RANGE", "TO_DATE_RANGE", "TO_DATE_RANGE", "TO_DATE", "TO_DATE", "TO_DATE", "refused", "TO_YESNO", "TO_YES", "TO_DATE_RANGE", "TO_DATE_RANGE"],
      ["TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "TO_YESNO", "refused", "TO_YES", "TO_YESNO", "TO_YESNO"],
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

end A12Kernel.Conformance.ConditionDiagnostic
