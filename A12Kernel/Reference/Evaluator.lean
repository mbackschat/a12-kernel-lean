import A12Kernel.Reference.Protocol

/-! # A12Kernel.Reference.Evaluator — pure protocol-to-semantics adapter

This adapter validates transport-only cell invariants, calls the existing checked flat elaborator and evaluator, and exhaustively translates internal rejection constructors into the stable public diagnostic algebra.
-/

namespace A12Kernel.Reference

open Lean

inductive InternalFailure where
  | incoherentCore
  deriving Repr, DecidableEq

private def pathDetails (path : List String) : Json :=
  Json.mkObj [("path", toJson path)]

private def fieldReferenceJson (reference : SurfaceFieldPath) : Json :=
  let baseFields := match reference.base with
    | .absolute => [("base", toJson "absolute")]
    | .relative parents => [("base", toJson "relative"), ("parents", toJson parents)]
  Json.mkObj (baseFields ++ [("groups", toJson reference.groups),
    ("field", toJson reference.field)])

private def scalarKindTag : SurfaceScalarKind → String
  | .number => "number"
  | .boolean => "boolean"
  | .confirm => "confirm"
  | .string => "string"

private def resolveDiagnostic : ResolveError → Diagnostic
  | .invalidModelPath path =>
      .make .invalidPath "$.model" (pathDetails path)
  | .duplicateFieldId id =>
      .make .duplicateFieldId "$.model"
        (Json.mkObj [("fieldId", toJson id)])
  | .duplicateEntityPath path =>
      .make .duplicateEntityPath "$.model" (pathDetails path)
  | .invalidRepeatableGroupPath path =>
      .make .invalidRepeatableGroupPath "$.model" (pathDetails path)
  | .duplicateRepeatableGroupPath path =>
      .make .duplicateRepeatableGroupPath "$.model" (pathDetails path)
  | .duplicateRepeatableLevel level =>
      .make .duplicateRepeatableLevel "$.model"
        (Json.mkObj [("level", toJson level)])
  | .entityHierarchyCollision fieldPath groupPath =>
      .make .hierarchyCollision "$.model"
        (Json.mkObj [("fieldPath", toJson fieldPath), ("groupPath", toJson groupPath)])
  | .repeatableScopeMismatch path expected actual =>
      .make .repeatableScopeMismatch "$.model"
        (Json.mkObj [("path", toJson path), ("expected", toJson expected),
          ("actual", toJson actual)])
  | .unknownRepeatableGroup path =>
      .make .unknownRepeatableGroup "$.condition" (pathDetails path)
  | .unknownFieldId id =>
      .make .unknownFieldId "$.condition"
        (Json.mkObj [("fieldId", toJson id)])
  | .invalidRuleGroup path =>
      .make .invalidRuleGroup "$.declaringGroup" (pathDetails path)
  | .invalidReference reference =>
      .make .invalidReference "$.condition"
        (Json.mkObj [("field", fieldReferenceJson reference)])
  | .aboveRoot parents =>
      .make .aboveRoot "$.condition"
        (Json.mkObj [("parents", toJson parents)])
  | .invalidEntity reference =>
      .make .unknownField "$.condition"
        (Json.mkObj [("field", fieldReferenceJson reference)])
  | .ambiguousEntity path =>
      .make .ambiguousField "$.condition" (pathDetails path)
  | .shortNameNotUnique name =>
      .make .shortNameNotUnique "$.condition"
        (Json.mkObj [("name", toJson name)])
  | .repeatableReference path =>
      .make .repeatableReference "$.condition" (pathDetails path)

private def elaborationResult : ElabError → Except InternalFailure Diagnostic
  | .resolve error => pure (resolveDiagnostic error)
  | .unsupportedOperator operator =>
      let tag := Support.ComparisonOperator.ofSurface operator |>.tag
      pure (.make .operator "$.condition"
        (Json.mkObj [("operator", toJson tag)]))
  | .literalKindMismatch path expected actual =>
      pure (.make .literalKindMismatch "$.condition"
        (Json.mkObj [("path", toJson path), ("expected", toJson (scalarKindTag expected)),
          ("actual", toJson (scalarKindTag actual))]))
  | .illegalConfirmLiteral path =>
      pure (.make .illegalConfirmLiteral "$.condition"
        (pathDetails path))
  | .incoherentCore => throw .incoherentCore

private def duplicateCellId? : List CellInput → Option FieldId
  | [] => none
  | cell :: rest =>
      if rest.any (·.fieldId == cell.fieldId) then some cell.fieldId
      else duplicateCellId? rest

private def validateCells (model : FlatModel) (cells : List CellInput) :
    Except Diagnostic Unit := do
  match duplicateCellId? cells with
  | some id =>
      throw (.make .duplicateCellId "$.cells"
        (Json.mkObj [("fieldId", toJson id)]))
  | none => pure ()
  for cell in cells do
    let declaration ← match model.lookupUniqueId cell.fieldId with
      | .ok declaration => pure declaration
      | .error _ =>
          throw (.make .undeclaredCellId "$.cells"
            (Json.mkObj [("fieldId", toJson cell.fieldId)]))
    if !declaration.repeatableScope.isEmpty then
      throw (.make .repeatableCell "$.cells"
        (Json.mkObj [("fieldId", toJson cell.fieldId),
          ("repeatableScope", toJson declaration.repeatableScope)]))

private def rawContext (cells : List CellInput) : RawFlatContext where
  read id :=
    match cells.find? (·.fieldId == id) with
    | some cell => cell.raw
    | none => .empty

def evaluate (request : Request) : Except InternalFailure Response := do
  match elaborate request.model request.declaringGroup request.condition with
  | .error error => pure (.diagnostic (← elaborationResult error))
  | .ok checked =>
      match validateCells request.model request.cells with
      | .error diagnostic => pure (.diagnostic diagnostic)
      | .ok () =>
          pure (.verdict (checked.core.evalFull
            (request.model.checkContext (rawContext request.cells))
            request.hasContent))

private def inputBytesDiagnostic : Diagnostic :=
  .make .resourceLimit "$"
    (Json.mkObj [("limit", toJson "inputBytes"),
      ("maximum", toJson Support.maxInputBytes)])

private def invalidJsonDiagnostic : Diagnostic :=
  .make .invalidJson "$"

private def strictJsonLimitDiagnostic (limit : StrictJson.Limit) : Diagnostic :=
  .make .resourceLimit "$"
    (Json.mkObj [("limit", toJson limit.tag), ("maximum", toJson limit.maximum)])

def evaluateText (input : String) : Except InternalFailure Response := do
  if input.utf8ByteSize > Support.maxInputBytes then
    pure (.diagnostic inputBytesDiagnostic)
  else
    match StrictJson.parse input with
    | .error (.invalidJson _) =>
        pure (.diagnostic invalidJsonDiagnostic)
    | .error (.duplicateMember name) =>
        pure (.diagnostic (.make .duplicateMember "$"
          (Json.mkObj [("member", toJson name)])))
    | .error .nonCanonicalNumber =>
        pure (.diagnostic (.make .invalidJsonNumber "$"))
    | .error (.resourceLimit limit) =>
        pure (.diagnostic (strictJsonLimitDiagnostic limit))
    | .ok json =>
        match Decode.request json with
        | .error diagnostic => pure (.diagnostic diagnostic)
        | .ok request => evaluate request

def evaluateBytes (input : ByteArray) : Except InternalFailure Response := do
  if input.size > Support.maxInputBytes then
    pure (.diagnostic inputBytesDiagnostic)
  else
    match String.fromUTF8? input with
    | none => pure (.diagnostic invalidJsonDiagnostic)
    | some text => evaluateText text

end A12Kernel.Reference
