import A12Kernel.Elaboration.StringContext
import A12Kernel.Semantics.ModelZone

/-! # Flat-elaboration conformance support -/

namespace A12Kernel.Conformance.Elaboration.Support

open A12Kernel

def numberInfo : NumField := { scale := 2, signed := false }

def quantityDecl : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Quantity",
    policy := { kind := .number numberInfo } }

def expressDecl : FlatFieldDecl :=
  { id := 1, groupPath := ["Order"], name := "ExpressShipping",
    policy := { kind := .boolean } }

def confirmDecl : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "TermsConfirmed",
    policy := { kind := .confirm } }

def ancestorLimitDecl : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "Limit",
    policy := { kind := .number { scale := 0, signed := true } } }

def localLimitDecl : FlatFieldDecl :=
  { id := 4, groupPath := ["Order", "Details"], name := "Limit",
    policy := { kind := .number { scale := 1, signed := false } } }

def externalCodeDecl : FlatFieldDecl :=
  { id := 5, groupPath := ["Reference"], name := "ExternalCode",
    policy := { kind := .boolean } }

def repeatableCountDecl : FlatFieldDecl :=
  { id := 6, groupPath := ["Order", "Items"], name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

def noteDecl : FlatFieldDecl :=
  { id := 7, groupPath := ["Order"], name := "Note",
    policy := { kind := .string } }

def dispatchDateComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := false, minute := false, second := false }

def dispatchDateDecl : FlatFieldDecl :=
  { id := 8, groupPath := ["Order"], name := "DispatchDate",
    policy := { kind := .temporal .date dispatchDateComponents } }

def arrivalDateDecl : FlatFieldDecl :=
  { id := 9, groupPath := ["Order"], name := "ArrivalDate",
    policy := { kind := .temporal .date dispatchDateComponents } }

def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

def eventTimeDecl : FlatFieldDecl :=
  { id := 10, groupPath := ["Order"], name := "EventTime",
    policy := { kind := .temporal .time timeComponents } }

def dateTimeComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

def eventDateTimeDecl : FlatFieldDecl :=
  { id := 11, groupPath := ["Order"], name := "EventDateTime",
    policy := { kind := .temporal .dateTime dateTimeComponents } }

def monthDayComponents : TemporalComponents :=
  { year := false, month := true, day := true,
    hour := false, minute := false, second := false }

def recurringDateDecl : FlatFieldDecl :=
  { id := 12, groupPath := ["Order"], name := "RecurringDate",
    policy := { kind := .temporal .date monthDayComponents } }

def repeatableItems : RepeatableGroupDecl :=
  { level := 10, path := ["Order", "Items"] }

def model : FlatModel :=
  { fields := [quantityDecl, expressDecl, confirmDecl, ancestorLimitDecl,
      localLimitDecl, externalCodeDecl, repeatableCountDecl, noteDecl,
      dispatchDateDecl, arrivalDateDecl, eventTimeDecl, eventDateTimeDecl,
      recurringDateDecl],
    repeatableGroups := [repeatableItems],
    fieldRefByShortNameAllowed := true }

def baseYearModel : FlatModel := { model with baseYear := some 2020 }

def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

def relative (parents : Nat) (groups : List String)
    (field : String) : SurfaceFieldPath :=
  { base := .relative parents, groups, field }

def bare (field : String) : SurfaceFieldPath := relative 0 [] field

def compare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
    (literal : SurfaceLiteral) : SurfaceCondition :=
  .compare op field literal

def compareFields (op : SurfaceComparisonOp) (left right : String) :
    SurfaceCondition :=
  .compareFields op (absolute ["Order"] left) (absolute ["Order"] right)

def compareNow (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
    (field : String) : SurfaceCondition :=
  .compareNow op position (absolute ["Order"] field)

def compareToday (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
    (field : String) : SurfaceCondition :=
  .compareToday op position (absolute ["Order"] field)

def compareBaseYear (op : SurfaceComparisonOp)
    (position : SurfacePointInTimePosition) (field : String) : SurfaceCondition :=
  .compareBaseYear op position (absolute ["Order"] field)

def compareBaseYearRange (op : SurfaceComparisonOp)
    (position : SurfacePointInTimePosition) (endpoint : BaseYearRangeEndpoint)
    (field : String) : SurfaceCondition :=
  .compareBaseYearRange op position endpoint (absolute ["Order"] field)

def dateLiteral (components : TemporalComponents) (millis : Int) :
    SurfaceLiteral :=
  .date components { epochMillis := millis }

def coreOf {checkedModel : FlatModel}
    (result : Except ElabError (CheckedFlatCondition checkedModel)) :
    Option FlatCondition :=
  match result with
  | .ok checked => some checked.core
  | .error _ => none

def rowGroupOf {checkedModel : FlatModel}
    (result : Except ElabError (CheckedFlatCondition checkedModel)) :
    Option GroupPath :=
  match result with
  | .ok checked => some checked.rowGroup
  | .error _ => none

def valueOf : Except ε α → Option α
  | .ok value => some value
  | .error _ => none

def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

def resolvedIdOf (result : Except ResolveError FlatFieldDecl) : Option FieldId :=
  (valueOf result).map (·.id)

example : coreOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))) =
    some (.compare (.number (.ordinary .equal)
      { id := 0, info := numberInfo } 0)) := by
  native_decide

end A12Kernel.Conformance.Elaboration.Support
