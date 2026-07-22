import A12Kernel.Reference.Protocol

/-! # A12Kernel.Reference.Evaluator — pure protocol-to-semantics adapter

This adapter validates transport-only cell invariants, calls the existing checked elaborators and evaluators, and exhaustively translates internal rejection constructors into the stable public diagnostic algebra.
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

private def groupReferenceJson (reference : SurfaceGroupPath) : Json :=
  let baseFields := match reference.base with
    | .absolute => [("base", toJson "absolute")]
    | .relative parents => [("base", toJson "relative"), ("parents", toJson parents)]
  Json.mkObj (baseFields ++ [("groups", toJson reference.groups)])

private def havingOriginTag : HavingOrigin → String
  | .inner => "inner"
  | .outer => "outer"

private def scalarKindTag : SurfaceScalarKind → String
  | .number => "number"
  | .boolean => "boolean"
  | .confirm => "confirm"
  | .string => "string"
  | .enumeration => "enumeration"
  | .temporal .date => "date"
  | .temporal .time => "time"
  | .temporal .dateTime => "dateTime"

private def resolveDiagnosticAt (referenceLocation : String) : ResolveError → Diagnostic
  | .invalidModelPath path =>
      .make .invalidPath "$.model" (pathDetails path)
  | .duplicateFieldId id =>
      .make .duplicateFieldId "$.model"
        (Json.mkObj [("fieldId", toJson id)])
  | .duplicateEntityPath path =>
      .make .duplicateEntityPath "$.model" (pathDetails path)
  | .customTypeRequiresString path =>
      .make .fieldKindMismatch "$.model"
        (Json.mkObj [("operation", toJson "customFieldTypeDeclaration"),
          ("path", toJson path), ("expected", toJson "string")])
  | .enumerationMetadataRequiresEnumeration _
  | .enumerationDeclarationRequired _
  | .invalidEnumerationDeclaration _ _ =>
      .make .fieldKindMismatch "$.model"
        (Json.mkObj [("operation", toJson "enumerationDeclaration")])
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
      .make .unknownRepeatableGroup referenceLocation (pathDetails path)
  | .unknownFieldId id =>
      .make .unknownFieldId referenceLocation
        (Json.mkObj [("fieldId", toJson id)])
  | .invalidRuleGroup path =>
      .make .invalidRuleGroup "$.declaringGroup" (pathDetails path)
  | .invalidReference reference =>
      .make .invalidReference referenceLocation
        (Json.mkObj [("field", fieldReferenceJson reference)])
  | .aboveRoot parents =>
      .make .aboveRoot referenceLocation
        (Json.mkObj [("parents", toJson parents)])
  | .invalidEntity reference =>
      .make .unknownField referenceLocation
        (Json.mkObj [("field", fieldReferenceJson reference)])
  | .ambiguousEntity path =>
      .make .ambiguousField referenceLocation (pathDetails path)
  | .shortNameNotUnique name =>
      .make .shortNameNotUnique referenceLocation
        (Json.mkObj [("name", toJson name)])
  | .repeatableReference path =>
      .make .repeatableReference referenceLocation (pathDetails path)

private def elaborationResult : ElabError → Except InternalFailure Diagnostic
  | .resolve error => pure (resolveDiagnosticAt "$.condition" error)
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
  | .temporalOperandKindMismatch leftPath rightPath leftKind rightKind =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "temporalComparison"),
          ("leftPath", toJson leftPath), ("rightPath", toJson rightPath),
          ("leftKind", toJson (scalarKindTag leftKind)),
          ("rightKind", toJson (scalarKindTag rightKind))]))
  | .temporalFormatsIncompatible leftPath rightPath =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "temporalComparison"),
          ("reason", toJson "incompatibleFormats"),
          ("leftPath", toJson leftPath), ("rightPath", toJson rightPath)]))
  | .temporalNowRequiresTime path =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "temporalComparison"),
          ("reason", toJson "nowRequiresTime"), ("path", toJson path)]))
  | .temporalLiteralNeedsBaseYear path =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "temporalComparison"),
          ("reason", toJson "baseYearRequired"), ("path", toJson path)]))
  | .invalidTemporalLiteralComponents path =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "temporalComparison"),
          ("reason", toJson "invalidDateLiteralComponents"),
          ("path", toJson path)]))
  | .baseYearNotDeclared =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "baseYear"),
          ("reason", toJson "notDeclared")]))
  | .baseYearScaleMismatch path scale =>
      pure (.make .equalityScaleMismatch "$.condition"
        (Json.mkObj [("operation", toJson "baseYear"),
          ("path", toJson path), ("fieldScale", toJson scale),
          ("baseYearScale", toJson 0)]))
  | .lengthOperandKindMismatch path actual =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("function", toJson "Length"), ("path", toJson path),
          ("expected", toJson (scalarKindTag .string)),
          ("actual", toJson (scalarKindTag actual))]))
  | .enumerationOperand _ _ => throw .incoherentCore
  | .textFieldOperandKindMismatch path actual =>
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "textFieldComparison"),
          ("path", toJson path), ("actual", toJson (scalarKindTag actual))]))
  | .emptyValueList path =>
      pure (.make .conditionForm "$.condition"
        (Json.mkObj [("operation", toJson "enumerationValueList"),
          ("path", toJson path)]))
  | .emptyValueListFields =>
      pure (.make .conditionForm "$.condition"
        (Json.mkObj [("operation", toJson "enumerationValueList")]))
  | .emptyValueListValueFields =>
      pure (.make .conditionForm "$.condition"
        (Json.mkObj [("operation", toJson "enumerationFieldValueList"),
          ("side", toJson "values")]))
  | .duplicateValueListField path projectionRef =>
      let projection := match projectionRef with
        | .stored => "stored"
        | .category name => name
      pure (.make .conditionForm "$.condition"
        (Json.mkObj [("operation", toJson "enumerationValueList"),
          ("path", toJson path), ("projection", toJson projection)]))
  | .duplicateStringValueListField path =>
      pure (.make .conditionForm "$.condition"
        (Json.mkObj [("operation", toJson "stringValueList"),
          ("path", toJson path)]))
  | .enumerationComparability leftPath rightPath error =>
      let reason := match error with
        | .displayClassMismatch => "displayClassMismatch"
        | .displayMapConflict => "displayMapConflict"
      pure (.make .fieldKindMismatch "$.condition"
        (Json.mkObj [("operation", toJson "directFieldComparison"),
          ("leftPath", toJson leftPath), ("rightPath", toJson rightPath),
          ("reason", toJson reason)]))
  | .incoherentCore => throw .incoherentCore

private def correlationElaborationResult : CorrelationElabError →
    Except InternalFailure Diagnostic
  | .resolve error => pure (resolveDiagnosticAt "$.rule" error)
  | .invalidGroupReference reference =>
      pure (.make .invalidGroupReference "$.rule"
        (Json.mkObj [("group", groupReferenceJson reference)]))
  | .wildcardWithParentNavigation parents =>
      pure (.make .pathForm "$.rule.valueField"
        (Json.mkObj [("form", toJson "parentNavigatingStar"),
          ("parents", toJson parents)]))
  | .fieldNotNumber path =>
      pure (.make .fieldKindMismatch "$.rule"
        (Json.mkObj [("path", toJson path), ("expected", toJson "number")]))
  | .fieldOutsideGroup origin fieldPath expectedGroup =>
      pure (.make .fieldOutsideGroup "$.rule.having"
        (Json.mkObj [("origin", toJson (havingOriginTag origin)),
          ("fieldPath", toJson fieldPath), ("expectedGroup", toJson expectedGroup)]))
  | .fieldScopeMismatch fieldPath expected actual =>
      pure (.make .fieldScopeMismatch "$.rule"
        (Json.mkObj [("fieldPath", toJson fieldPath), ("expected", toJson expected),
          ("actual", toJson actual)]))
  | .repetitionGroupMismatch expected actual =>
      pure (.make .repetitionGroupMismatch "$.rule.having"
        (Json.mkObj [("expected", toJson expected), ("actual", toJson actual)]))
  | .equalityScaleMismatch leftPath leftScale rightPath rightScale =>
      pure (.make .equalityScaleMismatch "$.rule.having"
        (Json.mkObj [("leftPath", toJson leftPath), ("leftScale", toJson leftScale),
          ("rightPath", toJson rightPath), ("rightScale", toJson rightScale)]))
  | .unsupportedOperator operator =>
      let tag := Support.ComparisonOperator.ofSurface operator |>.tag
      pure (.make .operator "$.rule.having"
        (Json.mkObj [("operator", toJson tag)]))
  | .missingInner =>
      pure (.make .missingInner "$.rule.having")
  | .missingOuter =>
      pure (.make .uncorrelatedHaving "$.rule.having")
  | .errorGuardMismatch errorPath guardPath =>
      pure (.make .errorGuardMismatch "$.rule"
        (Json.mkObj [("errorPath", toJson errorPath), ("guardPath", toJson guardPath)]))
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

private def duplicateCellAddress? : List CorrelationCellInput → Option (RowIndex × FieldId)
  | [] => none
  | cell :: rest =>
      if rest.any fun other => other.row == cell.row && other.fieldId == cell.fieldId then
        some (cell.row, cell.fieldId)
      else
        duplicateCellAddress? rest

private def contextDiagnostic : SingleGroupContextError → Diagnostic
  | .zeroCandidate row =>
      .make .zeroCandidate "$.candidates" (Json.mkObj [("row", toJson row)])
  | .duplicateCandidate row =>
      .make .duplicateCandidate "$.candidates" (Json.mkObj [("row", toJson row)])

private def validateCandidateSequence (candidates : List RowIndex) : Except Diagnostic Unit := do
  let expected := (List.range candidates.length).map (· + 1)
  if candidates.isEmpty || candidates != expected then
    throw (.make .invalidCandidateSequence "$.candidates"
      (Json.mkObj [("required", toJson "nonEmptyContiguousOneBased"),
        ("received", toJson candidates)]))

private def validateCorrelationCells (model : FlatModel) (group : RepeatableGroupDecl)
    (candidates : List RowIndex) (cells : List CorrelationCellInput) :
    Except Diagnostic Unit := do
  match duplicateCellAddress? cells with
  | some (row, fieldId) =>
      throw (.make .duplicateCellAddress "$.cells"
        (Json.mkObj [("row", toJson row), ("fieldId", toJson fieldId)]))
  | none => pure ()
  for cell in cells do
    if !candidates.contains cell.row then
      throw (.make .cellRowNotCandidate "$.cells"
        (Json.mkObj [("row", toJson cell.row), ("fieldId", toJson cell.fieldId)]))
    let declaration ← match model.lookupUniqueId cell.fieldId with
      | .ok declaration => pure declaration
      | .error _ =>
          throw (.make .undeclaredCellId "$.cells"
            (Json.mkObj [("fieldId", toJson cell.fieldId)]))
    if declaration.groupPath != group.path || declaration.repeatableScope != [group.level] then
      throw (.make .cellOutsideGroup "$.cells"
        (Json.mkObj [("row", toJson cell.row), ("fieldId", toJson cell.fieldId),
          ("fieldPath", toJson declaration.path), ("expectedGroup", toJson group.path),
          ("expectedScope", toJson [group.level])]))

private def correlationRawContext (request : CorrelationRequest) : RawSingleGroupContext where
  candidates := request.candidates
  read row id :=
    match request.cells.find? fun cell => cell.row == row && cell.fieldId == id with
    | some cell => cell.raw
    | none => .empty

private def evaluateFlat (request : FlatRequest) : Except InternalFailure Response := do
  match elaborate request.model request.declaringGroup request.condition with
  | .error error => pure (.diagnostic (← elaborationResult error))
  | .ok checked =>
      match validateCells request.model request.cells with
      | .error diagnostic => pure (.diagnostic diagnostic)
      | .ok () =>
          pure (.verdict (checked.core.evalFull
            (request.model.checkContext (rawContext request.cells))
            request.hasContent))

private def evaluateCorrelation (request : CorrelationRequest) :
    Except InternalFailure Response := do
  match elaborateSingleCorrelatedRule request.model request.declaringGroup request.rule with
  | .error error => pure (.diagnostic (← correlationElaborationResult error))
  | .ok checked =>
      let raw := correlationRawContext request
      match raw.validate with
      | .error error => pure (.diagnostic (contextDiagnostic error))
      | .ok () =>
          match validateCandidateSequence request.candidates with
          | .error diagnostic => pure (.diagnostic diagnostic)
          | .ok () =>
              match validateCorrelationCells request.model checked.core.group
                  request.candidates request.cells with
              | .error diagnostic => pure (.diagnostic diagnostic)
              | .ok () =>
                  match checked.firingRows raw with
                  | .ok rows => pure (.firingRows rows)
                  | .error error => pure (.diagnostic (contextDiagnostic error))

def evaluate (request : Request) : Except InternalFailure Response := do
  match request with
  | .flatValidation flat => evaluateFlat flat
  | .singleGroupCorrelation correlation => evaluateCorrelation correlation

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
