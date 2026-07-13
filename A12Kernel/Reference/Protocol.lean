import A12Kernel.Elaboration.Flat
import A12Kernel.Reference.Decimal
import A12Kernel.Reference.StrictJson
import A12Kernel.Reference.Support

/-! # A12Kernel.Reference.Protocol — normalized flat-reference protocol v1

The transport is intentionally outside the trusted semantic and theorem roots. It decodes one closed normalized request into the existing checked flat surface and emits a stable response algebra without exposing Lean `Repr` text.
-/

namespace A12Kernel.Reference

open Lean

structure Diagnostic where
  code : Support.DiagnosticCode
  location : String
  details : Json

namespace Diagnostic

def make (code : Support.DiagnosticCode) (location : String)
    (details : Json := Json.mkObj []) : Diagnostic :=
  { code, location, details }

def asJson (diagnostic : Diagnostic) : Json :=
  Json.mkObj [
    ("category", toJson diagnostic.code.category.tag),
    ("code", toJson diagnostic.code.tag),
    ("at", toJson diagnostic.location),
    ("details", diagnostic.details)]

end Diagnostic

inductive Response where
  | verdict (value : Verdict)
  | diagnostic (value : Diagnostic)

namespace Response

private def verdictJson (verdict : Verdict) : Json :=
  match Support.VerdictTag.ofVerdict verdict with
  | .notFired => Json.mkObj [("tag", toJson "notFired")]
  | .unknown => Json.mkObj [("tag", toJson "unknown")]
  | .firedValue =>
      Json.mkObj [("tag", toJson "fired"), ("polarity", toJson "value")]
  | .firedOmission =>
      Json.mkObj [("tag", toJson "fired"), ("polarity", toJson "omission")]

def asJson : Response → Json
  | .verdict value =>
      Json.mkObj [
        ("protocolVersion", toJson Support.protocolVersion),
        ("kernelBehaviorVersion", toJson Support.kernelBehaviorVersion),
        ("outcome", toJson "ok"),
        ("verdict", verdictJson value)]
  | .diagnostic value =>
      Json.mkObj [
        ("protocolVersion", toJson Support.protocolVersion),
        ("kernelBehaviorVersion", toJson Support.kernelBehaviorVersion),
        ("outcome", toJson "error"),
        ("diagnostic", value.asJson)]

def render (response : Response) : String :=
  response.asJson.compress ++ "\n"

end Response

structure CellInput where
  fieldId : FieldId
  raw : RawCell
  deriving Repr, DecidableEq

structure Request where
  model : FlatModel
  declaringGroup : GroupPath
  condition : SurfaceCondition
  cells : List CellInput
  hasContent : Bool
  deriving Repr, DecidableEq

namespace Decode

private def child (location name : String) : String :=
  if location == "$" then s!"$.{name}" else s!"{location}.{name}"

private def indexed (location : String) (index : Nat) : String :=
  s!"{location}[{index}]"

private def reasonDetails (reason : String) : Json :=
  Json.mkObj [("reason", toJson reason)]

private def invalidShape (location : String) (reason : String := "invalidShape") : Diagnostic :=
  .make .invalidShape location (reasonDetails reason)

private def resourceLimit (location limit : String) (maximum : Nat) : Diagnostic :=
  .make .resourceLimit location
    (Json.mkObj [("limit", toJson limit), ("maximum", toJson maximum)])

private def unsupported (code : Support.DiagnosticCode) (location tagName tag : String) :
    Diagnostic :=
  .make code location (Json.mkObj [(tagName, toJson tag)])

private def requireObject (json : Json) (location : String) (allowed : List String) :
    Except Diagnostic Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => throw (invalidShape location "expectedObject")
  for (name, _) in object.toList do
    if !allowed.contains name then
      throw (.make .invalidShape (child location name)
        (Json.mkObj [("member", toJson name), ("reason", toJson "unknownMember")]))

private def hasMember (json : Json) (name : String) : Bool :=
  match json.getObj? with
  | .ok object => object.contains name
  | .error _ => false

private def requiredJson (json : Json) (location name : String) : Except Diagnostic Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error _ => throw (invalidShape (child location name) "missingMember")

private def required [FromJson α] (json : Json) (location name : String) :
    Except Diagnostic α := do
  let value ← requiredJson json location name
  match fromJson? value with
  | .ok decoded => pure decoded
  | .error _ => throw (invalidShape (child location name) "wrongType")

private def parseNatural (json : Json) (location : String) : Except Diagnostic Nat := do
  let value ← match fromJson? (α := Nat) json with
    | .ok value => pure value
    | .error _ => throw (invalidShape location "expectedNaturalNumber")
  if value > Support.maxNaturalNumber then
    throw (resourceLimit location "naturalNumber" Support.maxNaturalNumber)
  pure value

private def requiredNatural (json : Json) (location name : String) : Except Diagnostic Nat := do
  parseNatural (← requiredJson json location name) (child location name)

private def parseNaturalList (json : Json) (location : String) :
    Except Diagnostic (List Nat) := do
  let values : List Json ← match fromJson? (α := List Json) json with
    | .ok values => pure values
    | .error _ => throw (invalidShape location "expectedArray")
  values.zipIdx.mapM fun (value, index) => parseNatural value (indexed location index)

private def validateSegment (segment location : String) : Except Diagnostic Unit := do
  if segment.isEmpty then throw (invalidShape location "emptyPathSegment")
  if segment.utf8ByteSize > Support.maxSegmentBytes then
    throw (resourceLimit location "segmentBytes" Support.maxSegmentBytes)

private def validateSegments (segments : List String) (location : String) :
    Except Diagnostic Unit := do
  if segments.length > Support.maxPathSegments then
    throw (resourceLimit location "pathSegments" Support.maxPathSegments)
  for (segment, index) in segments.zipIdx do
    validateSegment segment (indexed location index)

private def validateFieldPath (groups : List String) (field location : String) :
    Except Diagnostic Unit := do
  validateSegments groups (child location "groups")
  validateSegment field (child location "field")
  if groups.length + 1 > Support.maxPathSegments then
    throw (resourceLimit location "pathSegments" Support.maxPathSegments)

private def parsePath (json : Json) (location : String) :
    Except Diagnostic SurfaceFieldPath := do
  requireObject json location ["base", "parents", "groups", "field"]
  let baseTag : String ← required json location "base"
  let groups : List String ← required json location "groups"
  let field : String ← required json location "field"
  validateFieldPath groups field location
  let base ← match baseTag with
    | "absolute" =>
        if hasMember json "parents" then
          throw (invalidShape (child location "parents") "absolutePathHasParents")
        else
          pure PathBase.absolute
    | "relative" => pure (.relative (← requiredNatural json location "parents"))
    | other => throw (unsupported .pathBase (child location "base") "base" other)
  if (Support.PathFormTag.classify base groups).isNone then
    throw (unsupported .pathForm location "form" "childRelative")
  pure { base, groups, field }

private def parseDecimal (json : Json) (location : String) : Except Diagnostic Rat := do
  let text ← match fromJson? (α := String) json with
    | .ok text => pure text
    | .error _ => throw (invalidShape location "expectedCanonicalDecimalString")
  match Decimal.parse text with
  | .ok value => pure value
  | .error .tooLong =>
      throw (resourceLimit location "decimalCharacters" Support.maxDecimalCharacters)
  | .error .invalidCanonical =>
      throw (.make .invalidDecimal location (Json.mkObj [("value", toJson text)]))

private def parseLiteral (json : Json) (location : String) :
    Except Diagnostic SurfaceLiteral := do
  requireObject json location ["tag", "value"]
  let tag : String ← required json location "tag"
  match tag with
  | "number" => pure (.number (← parseDecimal (← requiredJson json location "value")
      (child location "value")))
  | "boolean" => pure (.boolean (← required json location "value"))
  | other => throw (unsupported .literalKind (child location "tag") "kind" other)

private def checkNodeLimit (location : String) (nodes : Nat) : Except Diagnostic Nat := do
  if nodes > Support.maxConditionNodes then
    throw (resourceLimit location "conditionNodes" Support.maxConditionNodes)
  pure nodes

private def parseCondition : Nat → Json → String →
    Except Diagnostic (SurfaceCondition × Nat)
  | 0, _, location =>
      throw (resourceLimit location "conditionDepth" Support.maxConditionDepth)
  | fuel + 1, json, location => do
      requireObject json location ["tag", "operator", "field", "literal", "left", "right"]
      let tag : String ← required json location "tag"
      match Support.ConditionFormTag.fromTag? tag with
      | none => throw (unsupported .conditionForm (child location "tag") "form" tag)
      | some .compare => do
          requireObject json location ["tag", "operator", "field", "literal"]
          let operatorTag : String ← required json location "operator"
          let operator ← match Support.ComparisonOperator.fromTag? operatorTag with
            | some operator => pure operator
            | none => throw (unsupported .operator (child location "operator")
                "operator" operatorTag)
          if !operator.isSupported then
            throw (unsupported .operator location "operator" operatorTag)
          let field ← parsePath (← requiredJson json location "field")
            (child location "field")
          let literal ← parseLiteral (← requiredJson json location "literal")
            (child location "literal")
          pure (.compare operator.toSurface field literal, 1)
      | some .fieldFilled => do
          requireObject json location ["tag", "field"]
          let field ← parsePath (← requiredJson json location "field")
            (child location "field")
          pure (.fieldFilled field, 1)
      | some .fieldNotFilled => do
          requireObject json location ["tag", "field"]
          let field ← parsePath (← requiredJson json location "field")
            (child location "field")
          pure (.fieldNotFilled field, 1)
      | some .and => do
          requireObject json location ["tag", "left", "right"]
          let (left, leftNodes) ← parseCondition fuel
            (← requiredJson json location "left") (child location "left")
          let (right, rightNodes) ← parseCondition fuel
            (← requiredJson json location "right") (child location "right")
          let nodes ← checkNodeLimit location (1 + leftNodes + rightNodes)
          pure (.and left right, nodes)
      | some .or => do
          requireObject json location ["tag", "left", "right"]
          let (left, leftNodes) ← parseCondition fuel
            (← requiredJson json location "left") (child location "left")
          let (right, rightNodes) ← parseCondition fuel
            (← requiredJson json location "right") (child location "right")
          let nodes ← checkNodeLimit location (1 + leftNodes + rightNodes)
          pure (.or left right, nodes)

private def parseFieldKind (json : Json) (location : String) :
    Except Diagnostic FieldPolicy := do
  requireObject json location ["tag", "scale", "signed"]
  let tag : String ← required json location "tag"
  match Support.FieldKindTag.fromTag? tag with
  | none => throw (unsupported .fieldKind (child location "tag") "kind" tag)
  | some .number => do
      let scale ← requiredNatural json location "scale"
      let signed : Bool ← required json location "signed"
      pure { kind := .number { scale, signed } }
  | some .boolean =>
      if hasMember json "scale" || hasMember json "signed" then
        throw (invalidShape location "booleanKindHasNumberMembers")
      else
        pure { kind := .boolean }
  | some .confirm =>
      if hasMember json "scale" || hasMember json "signed" then
        throw (invalidShape location "confirmKindHasNumberMembers")
      else
        pure { kind := .confirm }

private def parseField (json : Json) (location : String) :
    Except Diagnostic FlatFieldDecl := do
  requireObject json location ["id", "groupPath", "name", "kind", "repeatableScope"]
  let groupPath : List String ← required json location "groupPath"
  let name : String ← required json location "name"
  let repeatableScope ← parseNaturalList (← requiredJson json location "repeatableScope")
    (child location "repeatableScope")
  validateFieldPath groupPath name location
  if repeatableScope.length > Support.maxRepeatableScopeLevels then
    throw (resourceLimit (child location "repeatableScope")
      "repeatableScopeLevels" Support.maxRepeatableScopeLevels)
  pure {
    id := ← requiredNatural json location "id"
    groupPath
    name
    policy := ← parseFieldKind (← requiredJson json location "kind")
      (child location "kind")
    repeatableScope }

private def parseRepeatableGroup (json : Json) (location : String) :
    Except Diagnostic RepeatableGroupDecl := do
  requireObject json location ["level", "path"]
  let path : List String ← required json location "path"
  validateSegments path (child location "path")
  pure { level := ← requiredNatural json location "level", path }

private def parseModel (json : Json) (location : String) : Except Diagnostic FlatModel := do
  requireObject json location ["fieldRefByShortNameAllowed", "repeatableGroups", "fields"]
  let fieldJson : List Json ← required json location "fields"
  let repeatableJson : List Json ← required json location "repeatableGroups"
  if fieldJson.length > Support.maxFields then
    throw (resourceLimit (child location "fields") "fields" Support.maxFields)
  if repeatableJson.length > Support.maxRepeatableGroups then
    throw (resourceLimit (child location "repeatableGroups")
      "repeatableGroups" Support.maxRepeatableGroups)
  let fields ← fieldJson.zipIdx.mapM fun (field, index) =>
    parseField field (indexed (child location "fields") index)
  let repeatableGroups ← repeatableJson.zipIdx.mapM fun (group, index) =>
    parseRepeatableGroup group (indexed (child location "repeatableGroups") index)
  pure {
    fields
    repeatableGroups
    fieldRefByShortNameAllowed := ← required json location "fieldRefByShortNameAllowed" }

private def baseFormalCause : Support.RejectedCauseTag → BaseFormalCause
  | .malformed => .malformed
  | .declaredConstraint => .declaredConstraint
  | .unsupportedCharacter => .unsupportedCharacter
  | .leadingOrTrailingSpace => .leadingOrTrailingSpace
  | .customValidation => .customValidation

private def parseCellState (json : Json) (location : String) : Except Diagnostic RawCell := do
  requireObject json location ["tag", "value", "cause"]
  let tag : String ← required json location "tag"
  match Support.RawCellFormTag.fromTag? tag with
  | none => throw (unsupported .cellState (child location "tag") "state" tag)
  | some .parsedNumber => do
      requireObject json location ["tag", "value"]
      pure (.parsed (.num (← parseDecimal (← requiredJson json location "value")
        (child location "value"))))
  | some .parsedBoolean => do
      requireObject json location ["tag", "value"]
      pure (.parsed (.bool (← required json location "value")))
  | some .parsedConfirm => do
      requireObject json location ["tag", "value"]
      let value : Bool ← required json location "value"
      if value then pure (.parsed (.conf true))
      else throw (invalidShape (child location "value") "storedConfirmMustBeTrue")
  | some .rejected => do
      requireObject json location ["tag", "cause"]
      let causeTag : String ← required json location "cause"
      let cause ← match Support.RejectedCauseTag.fromTag? causeTag with
        | some cause => pure cause
        | none => throw (unsupported .rejectedCause (child location "cause")
            "cause" causeTag)
      pure (.rejected (baseFormalCause cause))

private def parseCell (json : Json) (location : String) : Except Diagnostic CellInput := do
  requireObject json location ["fieldId", "state"]
  pure {
    fieldId := ← requiredNatural json location "fieldId"
    raw := ← parseCellState (← requiredJson json location "state")
      (child location "state") }

def request (json : Json) : Except Diagnostic Request := do
  let location := "$"
  requireObject json location ["protocolVersion", "kernelBehaviorVersion", "operation",
    "model", "declaringGroup", "condition", "cells", "hasContent"]
  let receivedVersion ← requiredNatural json location "protocolVersion"
  if receivedVersion != Support.protocolVersion then
    throw (.make .unsupportedVersion "$.protocolVersion"
      (Json.mkObj [("received", toJson receivedVersion),
        ("supported", toJson Support.protocolVersion)]))
  let receivedKernel : String ← required json location "kernelBehaviorVersion"
  if receivedKernel != Support.kernelBehaviorVersion then
    throw (.make .kernelBehaviorVersionMismatch "$.kernelBehaviorVersion"
      (Json.mkObj [("received", toJson receivedKernel),
        ("supported", toJson Support.kernelBehaviorVersion)]))
  let receivedOperation : String ← required json location "operation"
  if receivedOperation != Support.operation then
    throw (.make .unsupportedOperation "$.operation"
      (Json.mkObj [("received", toJson receivedOperation),
        ("supported", toJson Support.operation)]))
  let declaringGroup : List String ← required json location "declaringGroup"
  validateSegments declaringGroup "$.declaringGroup"
  let cellJson : List Json ← required json location "cells"
  if cellJson.length > Support.maxCells then
    throw (resourceLimit "$.cells" "cells" Support.maxCells)
  let cells ← cellJson.zipIdx.mapM fun (cell, index) =>
    parseCell cell (indexed "$.cells" index)
  let (condition, _) ← parseCondition Support.maxConditionDepth
    (← requiredJson json location "condition") "$.condition"
  pure {
    model := ← parseModel (← requiredJson json location "model") "$.model"
    declaringGroup
    condition
    cells
    hasContent := ← required json location "hasContent" }

end Decode

example : Decimal.maxCharacters = Support.maxDecimalCharacters := rfl

end A12Kernel.Reference
