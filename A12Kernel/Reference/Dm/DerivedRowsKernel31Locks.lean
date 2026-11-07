import A12Kernel.Reference.Dm.Model

/-! # The evaluation reader on the declarations of the derived-row capture

The [derived-row capture](../../../evidence/kernel-31.1.1/captures/derived-rows-2026-11-04/) ran four
declaration shapes through kernel 31.1.1's runtime route that the evaluation reader had refused, and the
Kernel built and evaluated each one on both strategies:

* a DateTime declaring `youngerThan1900Check`, whose 1850 value draws no finding (`T31_DM`, `Y1850`), and a Time
  declaring it (`mc-time-1900`): the reader reads past a member the type body does not declare (spec/01 §1.1),
  as it does `datePrecision` beside a Time, a DateTime or a DateFragment (the declaration capture's `pp-*`);
* a `format` written `""` on a Date, Time or DateTime, which reads as the kind's default (`date-empty`,
  `dt-empty`, `time-empty`): the expand copy drops an empty member (peer KF658), while a blank `" "` still
  leaves no model (`mc-dt-space`, `mc-time-blank`);
* an unlabelled Enumeration entry without a token, beside tokens and with no category, which the Kernel builds
  (`E31_DM`: "A" and "C" are values, "Beta" and "X" draw the domain finding, `""` is absent).

The rows below read each declaration through the evaluation reader and state the policy it builds. The
runtime outcomes are compared row by row against the retained artifacts by the population replay.
-/

namespace A12Kernel.Dm.DerivedRowsKernel31Locks

open Lean A12Kernel

/-- A one-field model under "Form" declaring the field type written as JSON text. -/
private def modelWith (fieldType : String) : Except String Json :=
  Json.parse (r#"{"header":{"id":"D_DM","modelType":"document","modelVersion":"29.4.0","locales":[{"code":"en_US"}]},
"content":{"modelInfo":{"name":"D"},"modelConfig":{"timeZone":"Europe/Berlin","conditionLanguage":{"code":"en_US"}},
"modelRoot":{"rootGroups":[{"type":"Group","id":"/Form","name":"Form","Group":{"elements":[
{"type":"Field","id":"/Form/T1","name":"T1","Field":{"fieldType":"# ++ fieldType ++ "}}]}}]}}}")

/-- The declared field as the evaluation reader builds it, or the reader's refusal. -/
private def read (fieldType : String) : Except String FlatFieldDecl := do
  let model ← readModel (← modelWith fieldType)
  let some field := model.flat.fields.find? (·.name == "T1") | throw "no field"
  pure field

private def policyOf (fieldType : String) : Option TemporalTargetPolicy :=
  (read fieldType).toOption.bind (·.temporalTargetPolicy)

private def refused (fieldType : String) : Bool := (read fieldType).isOk == false

/-- Members a Time or DateTime body does not declare, and a fragment's precision, are read past; a Date's
pre-1900 check is bound but inert on kernel 31.3.1 (KF677, [31.3.1 Letter J](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §1). -/
example :
    policyOf r#"{"type":"DateTimeType","DateTimeType":{"youngerThan1900Check":true}}"# =
      some { format := "yyyy-MM-dd'T'HH:mm:ss" } ∧
    policyOf r#"{"type":"DateTimeType","DateTimeType":{"datePrecision":"DAY_OPTIONAL"}}"# =
      some { format := "yyyy-MM-dd'T'HH:mm:ss" } ∧
    policyOf r#"{"type":"TimeType","TimeType":{"youngerThan1900Check":true}}"# = some { format := "HH:mm:ss" } ∧
    policyOf r#"{"type":"DateFragmentType","DateFragmentType":{"formatOfFragment":"dd.MM.","datePrecision":"DAY_OPTIONAL"}}"# =
      some { format := "dd.MM." } ∧
    policyOf r#"{"type":"DateType","DateType":{"youngerThan1900Check":true,"datePrecision":"DAY_OPTIONAL"}}"# =
      some { format := "yyyy-MM-dd", partialMode := .dayOptional } := by
  native_decide

/-- An empty format is the kind's default, a blank one leaves no model, and a fragment's empty format has no
default to take. -/
example :
    policyOf r#"{"type":"DateType","DateType":{"format":""}}"# = some { format := "yyyy-MM-dd" } ∧
    policyOf r#"{"type":"TimeType","TimeType":{"format":""}}"# = some { format := "HH:mm:ss" } ∧
    policyOf r#"{"type":"DateTimeType","DateTimeType":{"format":""}}"# = some { format := "yyyy-MM-dd'T'HH:mm:ss" } ∧
    refused r#"{"type":"DateTimeType","DateTimeType":{"format":" "}}"# ∧
    refused r#"{"type":"TimeType","TimeType":{"format":" "}}"# ∧
    refused r#"{"type":"DateFragmentType","DateFragmentType":{"formatOfFragment":""}}"# := by
  native_decide

/-- The refusal the model reader records for the field, `none` when it keeps the field or reads no model. -/
private def refusal (fieldType : String) : Option String :=
  match modelWith fieldType >>= readModel with
  | .ok model => (model.refusals.find? (·.1.getLast? == some "T1")).map (·.2)
  | .error _ => none

private def refusalNames (fieldType fragment : String) : Bool :=
  match refusal fieldType with
  | some reason => (reason.splitOn fragment).length > 1
  | none => false

/-- An unlabelled entry without a token keeps its place and the declaration holds no token for it. A second such entry draws the
repeated-value notification, one beside a category the missing-token notification, and a labelled one the label
classes, each before the declaration is validated (spec/01 §1.3). -/
example :
    ((read r#"{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{},{"value":"C"}]}}"#).toOption.bind
      (·.enumeration)).map (fun declaration => (declaration.storedTokens, declaration.tokenlessPositions)) =
      some (["A", "C"], [1]) ∧
    refusalNames r#"{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{},{"value":"C"}],"categories":[{"name":"Band","values":["x","y","z"]}]}}"# "MISSING_INTERNAL" ∧
    refusalNames r#"{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{},{},{"value":"C"}]}}"# "repeated" ∧
    refusalNames r#"{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"label":[{"locale":"en_US","text":"Beta"}]}]}}"# "MVK_INTERNAL_VALUE_MISSING" := by
  native_decide

/-- An unlabelled empty token is a token-less entry: it keeps its place and the declaration holds no token for it,
as the declaration walk reads it (a12-dmkits KF566, KF321). -/
example :
    ((read r#"{"type":"EnumerationType","EnumerationType":{"values":[{"value":""},{"value":"C"}]}}"#).toOption.bind
      (·.enumeration)).map (fun declaration => (declaration.storedTokens, declaration.tokenlessPositions)) =
      some (["C"], [0]) := by
  native_decide

end A12Kernel.Dm.DerivedRowsKernel31Locks
