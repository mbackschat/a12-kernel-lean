import A12Kernel.Elaboration.Flat.Types

/-! # Validated flat-model and path resolution -/

namespace A12Kernel

private def validName (name : String) : Bool := !name.isEmpty

def GroupPath.isValid (path : GroupPath) : Bool :=
  !path.isEmpty && path.all validName

def GroupPath.isPrefixOf : GroupPath → GroupPath → Bool
  | [], _ => true
  | _, [] => false
  | prefixHead :: prefixRest, segment :: pathRest =>
      prefixHead == segment && GroupPath.isPrefixOf prefixRest pathRest

private def FlatFieldDecl.hasValidPath (declaration : FlatFieldDecl) : Bool :=
  GroupPath.isValid declaration.groupPath && validName declaration.name

private def invalidDeclPath? : List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: rest =>
      if declaration.hasValidPath then invalidDeclPath? rest else some declaration.path

private def duplicateId? : List FlatFieldDecl → Option FieldId
  | [] => none
  | declaration :: rest =>
      if rest.any (fun candidate => candidate.id == declaration.id) then
        some declaration.id
      else
        duplicateId? rest

private def duplicatePath? : List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: rest =>
      if rest.any (fun candidate => candidate.path == declaration.path) then
        some declaration.path
      else
        duplicatePath? rest

private def customTypeKindMismatch? : List FlatFieldDecl → Option (List String)
  | [] => none
  | declaration :: rest =>
      match declaration.customType, declaration.policy.kind with
      | none, _ => customTypeKindMismatch? rest
      | some _, .string => customTypeKindMismatch? rest
      | some _, _ => some declaration.path

private def rawValueModeError? : List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.stringValueMode, declaration.policy.kind,
          declaration.customType with
      | .evaluated, _, _ => rawValueModeError? rest
      | .raw, .string, none => rawValueModeError? rest
      | .raw, .string, some _ =>
          some (.rawValueModeForbidsCustomType declaration.path)
      | .raw, _, _ => some (.rawValueModeRequiresString declaration.path)

private def stringPolicyError? : List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      let policy := declaration.stringPolicy
      match declaration.policy.kind, declaration.customType with
      | .string, some _ =>
          if policy == {} then stringPolicyError? rest
          else some (.stringPolicyForbidsCustomType declaration.path)
      | .string, none =>
          if declaration.stringValueMode == .raw && !policy.lineBreaksPermitted then
            some (.rawStringRequiresLineBreakPermission declaration.path)
          else if declaration.stringValueMode == .raw && policy.minLength.isSome then
            some (.rawStringForbidsMinimumLength declaration.path)
          else if policy.minimumExceedsMaximum then
            some (.stringMinimumExceedsMaximum declaration.path)
          else if policy.lineBreakMaximumInvalid then
            some (.lineBreakWithSingleCharacterMaximum declaration.path)
          else
            stringPolicyError? rest
      | _, _ =>
          if policy == {} then stringPolicyError? rest
          else some (.stringPolicyRequiresString declaration.path)

private def stringPatternError? : List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.stringPatternSource, declaration.policy.kind,
          declaration.stringValueMode, declaration.customType with
      | none, _, _, _ => stringPatternError? rest
      | some _, .string, .raw, _ =>
          some (.rawStringForbidsPattern declaration.path)
      | some _, .string, .evaluated, some _ =>
          some (.stringPatternForbidsCustomType declaration.path)
      | some _, .string, .evaluated, none => stringPatternError? rest
      | some _, _, _, _ => some (.stringPatternRequiresString declaration.path)

private def numericTargetConstraintsError? :
    List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      let constraints := declaration.numericTargetConstraints
      match declaration.policy.kind with
      | .number info =>
          if info.scale < constraints.minFractionalDigits then
            some (.numericMinimumFractionalDigitsExceedMaximum declaration.path
              constraints.minFractionalDigits info.scale)
          else
            match constraints.maxIntegerDigits with
            | some 0 => some (.numericMaximumIntegerDigitsZero declaration.path)
            | some _ | none => numericTargetConstraintsError? rest
      | .boolean | .confirm | .string | .enumeration | .temporal _ _ =>
          if constraints == NumericTargetConstraints.unconstrained then
            numericTargetConstraintsError? rest
          else some (.numericTargetConstraintsRequireNumber declaration.path)

private def enumerationDeclarationError? :
    List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.policy.kind, declaration.enumeration with
      | .enumeration, none => some (.enumerationDeclarationRequired declaration.path)
      | .enumeration, some source =>
          match source.validate with
          | .error error => some (.invalidEnumerationDeclaration declaration.path error)
          | .ok () => enumerationDeclarationError? rest
      | _, some _ => some (.enumerationMetadataRequiresEnumeration declaration.path)
      | _, none => enumerationDeclarationError? rest

private def invalidRepeatableGroupPath? : List RepeatableGroupDecl → Option GroupPath
  | [] => none
  | group :: rest =>
      if GroupPath.isValid group.path then invalidRepeatableGroupPath? rest else some group.path

private def duplicateRepeatableGroupPath? : List RepeatableGroupDecl → Option GroupPath
  | [] => none
  | group :: rest =>
      if rest.any (fun candidate => candidate.path == group.path) then
        some group.path
      else
        duplicateRepeatableGroupPath? rest

private def duplicateRepeatableLevel? : List RepeatableGroupDecl → Option RepeatableLevel
  | [] => none
  | group :: rest =>
      if rest.any (fun candidate => candidate.level == group.level) then
        some group.level
      else
        duplicateRepeatableLevel? rest

/-- An index-field declaration must identify one direct child of its group with an evaluation value. General repeatable-scope coherence is checked separately; individual consumers may support a narrower scope. -/
private def invalidIndexField? (fields : List FlatFieldDecl) :
    List RepeatableGroupDecl → Option (GroupPath × FieldId)
  | [] => none
  | group :: rest =>
      match group.indexField with
      | none => invalidIndexField? fields rest
      | some field =>
          match fields.filter (fun declaration => declaration.id == field) with
          | [declaration] =>
              if declaration.groupPath == group.path &&
                  !declaration.isRawString then
                invalidIndexField? fields rest
              else
                some (group.path, field)
          | _ => some (group.path, field)

private def prefixedGroupPath? (fieldPath : GroupPath) :
    List GroupPath → Option GroupPath
  | [] => none
  | groupPath :: rest =>
      if fieldPath.isPrefixOf groupPath then some groupPath
      else prefixedGroupPath? fieldPath rest

private def entityHierarchyCollision? (groupPaths : List GroupPath) :
    List FlatFieldDecl → Option (GroupPath × GroupPath)
  | [] => none
  | declaration :: rest =>
      match prefixedGroupPath? declaration.path groupPaths with
      | some groupPath => some (declaration.path, groupPath)
      | none => entityHierarchyCollision? groupPaths rest

/-- Derive the canonical outer-to-inner repeatable ancestry from declared group paths. -/
def FlatModel.repeatableScopeForGroupPath (model : FlatModel) (groupPath : GroupPath) :
    List RepeatableLevel :=
  (List.range groupPath.length).filterMap fun offset =>
    (model.repeatableGroups.find? fun group =>
      group.path == groupPath.take (offset + 1)).map (·.level)

private def repeatableScopeMismatch? (model : FlatModel) :
    List FlatFieldDecl →
      Option (List String × List RepeatableLevel × List RepeatableLevel)
  | [] => none
  | declaration :: rest =>
      let expected := model.repeatableScopeForGroupPath declaration.groupPath
      if declaration.repeatableScope == expected then
        repeatableScopeMismatch? model rest
      else
        some (declaration.path, expected, declaration.repeatableScope)

def FlatModel.validate (model : FlatModel) : Except ResolveError Unit := do
  match invalidDeclPath? model.fields with
  | some path => throw (.invalidModelPath path)
  | none => pure ()
  match customTypeKindMismatch? model.fields with
  | some path => throw (.customTypeRequiresString path)
  | none => pure ()
  match rawValueModeError? model.fields with
  | some error => throw error
  | none => pure ()
  match stringPolicyError? model.fields with
  | some error => throw error
  | none => pure ()
  match stringPatternError? model.fields with
  | some error => throw error
  | none => pure ()
  match numericTargetConstraintsError? model.fields with
  | some error => throw error
  | none => pure ()
  match enumerationDeclarationError? model.fields with
  | some error => throw error
  | none => pure ()
  match duplicateId? model.fields with
  | some id => throw (.duplicateFieldId id)
  | none => pure ()
  match duplicatePath? model.fields with
  | some path => throw (.duplicateEntityPath path)
  | none => pure ()
  match invalidRepeatableGroupPath? model.repeatableGroups with
  | some path => throw (.invalidRepeatableGroupPath path)
  | none => pure ()
  match duplicateRepeatableGroupPath? model.repeatableGroups with
  | some path => throw (.duplicateRepeatableGroupPath path)
  | none => pure ()
  match duplicateRepeatableLevel? model.repeatableGroups with
  | some level => throw (.duplicateRepeatableLevel level)
  | none => pure ()
  let groupPaths := model.fields.map (·.groupPath) ++ model.repeatableGroups.map (·.path)
  match entityHierarchyCollision? groupPaths model.fields with
  | some (fieldPath, groupPath) =>
      throw (.entityHierarchyCollision fieldPath groupPath)
  | none => pure ()
  match repeatableScopeMismatch? model model.fields with
  | some (path, expected, actual) =>
      throw (.repeatableScopeMismatch path expected actual)
  | none => pure ()
  match invalidIndexField? model.fields model.repeatableGroups with
  | some (groupPath, field) => throw (.invalidIndexField groupPath field)
  | none => pure ()

/-- Unique lookup is intentionally order-independent: ambiguity is an error, never a
    first-match choice. -/
def FlatModel.lookupUniqueId (model : FlatModel) (id : FieldId) :
    Except ResolveError FlatFieldDecl :=
  match model.fields.filter (fun declaration => declaration.id == id) with
  | [] => .error (.unknownFieldId id)
  | [declaration] => .ok declaration
  | _ => .error (.duplicateFieldId id)

/-- Look up the declaration proving that an exact written group path is repeatable. -/
def FlatModel.lookupUniqueRepeatablePath (model : FlatModel) (path : GroupPath) :
    Except ResolveError RepeatableGroupDecl :=
  match model.repeatableGroups.filter (fun group => group.path == path) with
  | [] => .error (.unknownRepeatableGroup path)
  | [group] => .ok group
  | _ => .error (.duplicateRepeatableGroupPath path)

/-- Resolve one repeatable level after model validation has established unique level identity. -/
def FlatModel.repeatableGroupAtLevel? (model : FlatModel)
    (level : RepeatableLevel) : Option RepeatableGroupDecl :=
  model.repeatableGroups.find? fun group => group.level == level

/-- Resolve a field's model-owned requiredness policy without erasing the group that gates it. A checked model makes the incoherent-scope error unreachable. -/
def FlatModel.requirednessScopeFor (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except ResolveError (Option RequirednessScope) :=
  match declaration.requiredness with
  | none => .ok none
  | some .relativeToParent =>
      .ok (some (.relativeTo declaration.groupPath))
  | some .absoluteOrNearestRepeatableAncestor =>
      match declaration.repeatableScope.getLast? with
      | none => .ok (some .absolute)
      | some level =>
          match model.repeatableGroupAtLevel? level with
          | some group => .ok (some (.relativeTo group.path))
          | none =>
              .error (.repeatableScopeMismatch declaration.path
                (model.repeatableScopeForGroupPath declaration.groupPath)
                declaration.repeatableScope)

/-- A group is present in the flattened namespace when it owns or contains a declared field, or has its own repeatable declaration. Empty nonrepeatable groups are rejected by the kernel and therefore need no representation here. -/
def FlatModel.hasGroupPath (model : FlatModel) (path : GroupPath) : Bool :=
  GroupPath.isValid path &&
    ((model.fields.any fun declaration => path.isPrefixOf declaration.groupPath) ||
      model.repeatableGroups.any fun group => group.path == path)

private def FlatModel.lookupPath? (model : FlatModel) (path : List String) :
    Except ResolveError (Option FlatFieldDecl) :=
  match model.fields.filter (fun declaration => declaration.path == path) with
  | [] => .ok none
  | [declaration] => .ok (some declaration)
  | _ => .error (.ambiguousEntity path)

private def SurfaceFieldPath.hasValidShape (reference : SurfaceFieldPath) : Bool :=
  validName reference.field && reference.groups.all validName &&
    reference.turningPoint.all validName &&
    reference.base.allowsTurningPoint reference.turningPoint &&
    match reference.base with
    | .absolute => !reference.groups.isEmpty
    | .relative _ => true

def PathKeywordProfile.requiresQuote (profile : PathKeywordProfile)
    (name : String) : Bool :=
  profile.reserved.contains name

namespace AuthoredPathName

/-- Validate one exact-case keyword collision and erase accepted quote syntax before semantic name lookup. Unnecessary quotes are legal and become semantically transparent. -/
def lower (name : AuthoredPathName) (profile : PathKeywordProfile) :
    Except PathSyntaxError String :=
  if profile.requiresQuote name.text && !name.quoted then
    .error (.unquotedKeyword name.text)
  else
    .ok name.text

end AuthoredPathName

namespace PathKeywordProfile

/-- Canonical structured rendering quotes exactly the names that collide with the selected language's terminal set. -/
def reifyName (profile : PathKeywordProfile) (name : String) :
    AuthoredPathName :=
  { text := name, quoted := profile.requiresQuote name }

end PathKeywordProfile

namespace AuthoredFieldPath

/-- Validate quote provenance in every name-bearing position, then erase it into the sole existing structured field-path representation. -/
def lower (path : AuthoredFieldPath) (profile : PathKeywordProfile) :
    Except PathSyntaxError SurfaceFieldPath := do
  let turningPoint ← match path.turningPoint with
    | none => pure none
    | some name => pure (some (← name.lower profile))
  let groups ← path.groups.mapM (·.lower profile)
  let field ← path.field.lower profile
  pure { base := path.base, turningPoint, groups, field }

end AuthoredFieldPath

namespace SurfaceFieldPath

/-- Reintroduce canonical quote provenance without changing the semantic path identity. -/
def reifyQuotes (path : SurfaceFieldPath) (profile : PathKeywordProfile) :
    AuthoredFieldPath :=
  {
    base := path.base
    turningPoint := path.turningPoint.map profile.reifyName
    groups := path.groups.map profile.reifyName
    field := profile.reifyName path.field
  }

end SurfaceFieldPath

def GroupPath.walkUp (group : GroupPath) (parents : Nat) : Except ResolveError GroupPath :=
  if parents < group.length then
    .ok (group.take (group.length - parents))
  else
    .error (.aboveRoot parents)

/-- Check an optional explicit turning-point label against the group reached by parent walking. The label is a guard, never an alternative ancestor search. -/
def GroupPath.matchesTurningPoint (group : GroupPath)
    (turningPoint : Option String) : Bool :=
  match turningPoint with
  | none => true
  | some expected => group.getLast? == some expected

def FlatFieldDecl.requireNonrepeatable (declaration : FlatFieldDecl) :
    Except ResolveError FlatFieldDecl :=
  if declaration.repeatableScope.isEmpty then
    .ok declaration
  else
    .error (.repeatableReference declaration.path)

/-- Resolve one declaration by stable ID and reject repeatable targets or operands. -/
def FlatModel.resolveNonrepeatableDeclarationById
    (model : FlatModel) (field : FieldId) :
    Except ResolveError FlatFieldDecl := do
  (← model.lookupUniqueId field).requireNonrepeatable

/-- Resolve a bare single-segment reference exactly as the kernel parser does: try the
    declaring group, then (when enabled) require one model-wide short-name match. There
    is deliberately no implicit ancestor walk; parent lookup requires `..`. -/
private def FlatModel.resolveBareDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  match ← model.lookupPath? (declaringGroup ++ [reference.field]) with
  | some declaration => pure declaration
  | none =>
      if model.fieldRefByShortNameAllowed then
        match model.fields.filter (fun declaration => declaration.name == reference.field) with
        | [] => throw (.invalidEntity reference)
        | [declaration] => pure declaration
        | _ => throw (.shortNameNotUnique reference.field)
      else
        throw (.invalidEntity reference)

/-- Shared path mechanism for both non-repeatable and repeatable elaborators. This resolves one declaration without deciding whether its repeatable scope is legal for the caller. -/
def FlatModel.resolveFieldDeclarationUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  if !GroupPath.isValid declaringGroup then throw (.invalidRuleGroup declaringGroup)
  if !reference.hasValidShape then throw (.invalidReference reference)
  match reference.base with
  | .absolute =>
      match ← model.lookupPath? (reference.groups ++ [reference.field]) with
      | some declaration => pure declaration
      | none => throw (.invalidEntity reference)
  | .relative parents =>
      if parents == 0 && reference.groups.isEmpty then
        model.resolveBareDeclaration declaringGroup reference
      else
        let base ← GroupPath.walkUp declaringGroup parents
        if !base.matchesTurningPoint reference.turningPoint then
          throw (.invalidEntity reference)
        else
          match ← model.lookupPath? (base ++ reference.groups ++ [reference.field]) with
          | some declaration => pure declaration
          | none => throw (.invalidEntity reference)

/-- Resolve a nonrepeatable declaration after a caller has validated the model. This is shared by checked condition and computation-expression lowering. -/
def FlatModel.resolveNonrepeatableFieldUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  (← model.resolveFieldDeclarationUnchecked declaringGroup reference).requireNonrepeatable

/-- Resolve one structured field path against a validated expanded model while preserving its repeatable scope for a later elaborator. -/
def FlatModel.resolveFieldDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveFieldDeclarationUnchecked declaringGroup reference

/-- Resolve one structured field path against a validated expanded model. -/
def FlatModel.resolveField (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveNonrepeatableFieldUnchecked declaringGroup reference

/-- Validate selected-language quote provenance and then reuse the sole checked nonrepeatable field resolver. -/
def FlatModel.resolveAuthoredField (model : FlatModel)
    (profile : PathKeywordProfile) (declaringGroup : GroupPath)
    (reference : AuthoredFieldPath) :
    Except AuthoredFieldPathError FlatFieldDecl := do
  let path ← (reference.lower profile).mapError .syntax
  (model.resolveField declaringGroup path).mapError .resolve

end A12Kernel
