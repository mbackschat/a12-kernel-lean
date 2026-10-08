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

/-- The largest `maxFractionalDigits` a Number field may declare. Measured at a12-dmkits
`ee2f5d84`: 14 is accepted and 15 refused by a plain MVK-less model check. This is the
`fieldScaleCap` of `spec/04`, not the `maxRoundingPlaces` bound on a rounding argument. -/
def declaredNumericScaleCap : Nat := 14

private def numericTargetConstraintsError? :
    List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      let constraints := declaration.numericTargetConstraints
      match declaration.policy.kind with
      | .number info =>
          -- `fieldScaleCap` before `fieldScaleOrdering`. The ordering gate refuses exactly
          -- `max >= 0 && min > max`, where an absent member reads as `0` and a *negative*
          -- maximum takes the pair out of the comparison rather than failing it (`spec/04`).
          -- Both members are `Nat` here, so the `max >= 0` conjunct is vacuous and the test
          -- below is the whole gate for every declaration this model can express. The negative
          -- maximum is therefore outside the represented universe rather than wrongly refused
          -- — do not read this arm as deciding it. An earlier comment justified the order by
          -- `0 <= min <= max <= 14`; that reading over-rejects in two directions and was
          -- corrected from a12-dmkits' measurement ([inbound](../../../docs/SOURCES.md)).
          if declaredNumericScaleCap < info.scale then
            some (.numericFractionalDigitsAboveCap declaration.path
              info.scale declaredNumericScaleCap)
          else if info.scale < constraints.minFractionalDigits then
            some (.numericMinimumFractionalDigitsExceedMaximum declaration.path
              constraints.minFractionalDigits info.scale)
          else
            match constraints.maxIntegerDigits with
            | some 0 => some (.numericMaximumIntegerDigitsZero declaration.path)
            | some _ | none => numericTargetConstraintsError? rest
      | .boolean | .confirm | .string | .enumeration | .temporal _ _ | .dateRange =>
          if constraints == NumericTargetConstraints.unconstrained then
            numericTargetConstraintsError? rest
          else some (.numericTargetConstraintsRequireNumber declaration.path)

private def temporalTargetPolicyError? :
    List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.policy.kind, declaration.temporalTargetPolicy with
      | _, none => temporalTargetPolicyError? rest
      | .temporal kind components, some policy =>
          match policy.errorFor? kind components with
          | some error => some (.invalidTemporalTargetPolicy declaration.path error)
          | none => temporalTargetPolicyError? rest
      | _, some _ => some (.temporalTargetPolicyRequiresTemporal declaration.path)

private def dateRangeDeclarationPolicyError? :
    List FlatFieldDecl → Option ResolveError
  | [] => none
  | declaration :: rest =>
      match declaration.policy.kind, declaration.dateRangePolicy with
      | .dateRange, none =>
          some (.dateRangeDeclarationPolicyRequired declaration.path)
      | .dateRange, some policy =>
          match policy.error? with
          | some error =>
              some (.invalidDateRangeDeclarationPolicy declaration.path error)
          | none => dateRangeDeclarationPolicyError? rest
      | _, some _ =>
          some (.dateRangeDeclarationPolicyRequiresDateRange declaration.path)
      | _, none => dateRangeDeclarationPolicyError? rest

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

def WrittenFieldPlacement.of (declaringGroup writtenGroup : GroupPath) : WrittenFieldPlacement :=
  if GroupPath.isPrefixOf declaringGroup writtenGroup then .contained else .outside

/-- The type step of the index gates, for two index fields of one name, the written path's first,
    decided on the two keys' kinds. The Kernel iterates the two jointly when their kinds agree, which
    its BA documentation requires
    ([Parallel Iteration](../../../../a12-kernel/documentation/_merged/kernel-ba.md)) and the rows
    measure for String, Number, Enumeration and Date keys. It also iterates them when a Date key
    meets a DateTime or Time key or a DateTime key meets a Time one, which that requirement wrongly
    excludes. It draws the type class for a String key beside any other kind, a Number key beside a
    String, Enumeration or Date one, an Enumeration beside a Boolean, a Boolean beside a Confirm, and
    a Date beside a date range
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope),
    [inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-index-type-table)).

    **Across kinds only the measured direction is claimed**: every other pair of differing kinds, the
    reverse of a measured one included, is `unmeasured`, although the rows fit a pairing by base type
    that joins the temporal kinds. **Within a kind, a key's configuration is assumed not to split a
    pair**: the rows vary a Number's scale, an Enumeration's values, a Date's components, a date
    fragment included, and a custom type on the read key, and pair each, while a Number's sign, a
    temporal format, and a custom type on the written key are not varied. A date fragment is a
    `.date` carrying its components here, as [`TemporalFormat`](../../Semantics/TemporalFormat.lean)
    records, and a custom type lies outside `FieldKind`, so the Date and String arms reach both on
    either side; [SG9](../../../docs/gaps/paths-and-groups.md#gap-sg9) owns the assumption. -/
def FieldKind.indexTypeGate (written operand : FieldKind) : ParallelIndexGate :=
  if written == operand then .legal
  else match written, operand with
    | .string, _ => .differentType
    | .number _, .number _ => .legal
    | .number _, .string | .number _, .enumeration | .number _, .temporal .date _ => .differentType
    | .enumeration, .boolean | .boolean, .confirm | .temporal .date _, .dateRange => .differentType
    | .temporal .date _, .temporal _ _ | .temporal .dateTime _, .temporal .time _ => .legal
    | _, _ => .unmeasured

/-- The index gates `group` meets beside the written field's group, for a group and a written path
    that each declare an index field. Each chain must carry exactly one keyed group of its own: the
    measured multiple-index row keys a second group above the level on the operand's side only
    ([`kf371`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)). -/
def FlatModel.parallelIndexGate (model : FlatModel) (writtenGroup : GroupPath)
    (group : RepeatableGroupDecl) : ParallelIndexGate :=
  let keyedAbove (path : GroupPath) := model.repeatableGroups.filter fun candidate =>
    GroupPath.isPrefixOf candidate.path path && candidate.indexField.isSome
  let operandKeys := keyedAbove group.path
  let writtenKeys := keyedAbove writtenGroup
  let indexDeclaration? (keyed : RepeatableGroupDecl) : Option FlatFieldDecl :=
    keyed.indexField.bind fun id => model.fields.find? (·.id == id)
  if operandKeys.any writtenKeys.contains || writtenKeys.length != 1 then .unmeasured
  else if operandKeys.length > 1 then .multipleIndexFields
  else
    match indexDeclaration? group, writtenKeys.head?.bind indexDeclaration? with
    | some operandIndex, some writtenIndex =>
        if operandIndex.name != writtenIndex.name then .differentName
        else writtenIndex.policy.kind.indexTypeGate operandIndex.policy.kind
    | _, _ => .unmeasured

/-- The class facts of one level a read leaves unbound, for a construct declared in `declaringGroup`
    that writes a field of `writtenGroup`. -/
def FlatModel.unboundOperandLevel (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (level : RepeatableLevel) : UnboundOperandLevel :=
  let group? := model.repeatableGroups.find? (·.level == level)
  let placement := WrittenFieldPlacement.of declaringGroup writtenGroup
  let holdsWritten := group?.any fun group => GroupPath.isPrefixOf group.path writtenGroup
  let parallel := !holdsWritten && !(group?.any fun group => GroupPath.isPrefixOf writtenGroup group.path)
  let indexKeyed := group?.any (·.indexField.isSome)
  let writtenPathKeyed := model.repeatableGroups.any fun group =>
    GroupPath.isPrefixOf group.path writtenGroup && group.indexField.isSome
  { level, placement, parallel, indexKeyed, writtenPathKeyed
    writtenBound := placement == .contained && holdsWritten
    parallelGate :=
      match placement, group? with
      | .contained, some group =>
          if parallel && indexKeyed && writtenPathKeyed then
            model.parallelIndexGate writtenGroup group
          else .notReached
      | _, _ => .notReached }

/-- The first of these levels, outermost first, that the walk does not pass, or the outermost when
    it passes every one. -/
def UnboundOperandLevel.walkRefusal? (levels : List UnboundOperandLevel) :
    Option UnboundOperandLevel :=
  (levels.find? (!·.passesWalk)).orElse fun _ => levels.head?

/-- The unbound level a list of operand binding scopes is refused at, for an evaluation that binds
    none of them. The walk asks every level of a read outermost first and passes a legal parallel
    iteration ([`kf371`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)), or a level the
    written field binds, to the next, so a read refuses at its first other level; one that passes
    every level still returns its outermost, whose class is `none`, because no route evaluating these
    scopes binds those levels. Which
    refusing operand decides when two would draw different classes is not measured; this takes the
    first in authored order. -/
def FlatModel.firstUnboundOperandLevel? (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (scopes : List (List RepeatableLevel)) : Option UnboundOperandLevel :=
  UnboundOperandLevel.walkRefusal? <| scopes.filterMap fun scope =>
    UnboundOperandLevel.walkRefusal? (scope.map (model.unboundOperandLevel declaringGroup writtenGroup))

/-- The level a validation read is refused at among those this evaluation does not bind, found by
    the walk and placed by the written field, or `none` when `bound` covers every level of it. `bound` defaults to what the rule group binds; a
    caller with a narrower reading scope passes that. With the written field outside the rule group
    nothing binds a level, the rule group's own included, so every level draws containment
    ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-24d-star-containment)). Inside it the
    written field also binds the levels holding it: the Kernel admits those reads, and the walk passes
    them claiming no class, because an evaluation at `bound` cannot bind them
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)). -/
def FlatModel.unboundReadLevel? (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (scope : List RepeatableLevel)
    (bound : List RepeatableLevel := model.repeatableScopeForGroupPath declaringGroup) :
    Option UnboundOperandLevel :=
  let bound := match WrittenFieldPlacement.of declaringGroup writtenGroup with
    | .contained => bound
    | .outside => []
  model.firstUnboundOperandLevel? declaringGroup writtenGroup [scope.filter (!bound.contains ·)]

/-- The level the walk refuses outright among a starred operand's levels above its first star, which
    are read per row. A level the walk passes is left to the rule's own iteration, which may bind it
    from the error field's scope; it is not refused here. -/
def FlatModel.refusedReadLevel? (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (scope : List RepeatableLevel)
    (bound : List RepeatableLevel := model.repeatableScopeForGroupPath declaringGroup) :
    Option UnboundOperandLevel :=
  (model.unboundReadLevel? declaringGroup writtenGroup scope bound).filter (!·.passesWalk)

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

/-- The reserved name matched case-insensitively, spelled character-wise rather than through
    `String.toLower`: the checked-model structures carry `validate.isOk = true` as a proof field that
    callers discharge definitionally, and `toLower` does not reduce cheaply enough for that. -/
private def isReservedRootName (name : String) : Bool :=
  match name.toList with
  | [first, second] =>
      (first == 'I' || first == 'i') && (second == 'D' || second == 'd')
  | _ => false

/-- Every declared path's first segment names the root group, so this reads them all rather than
    assuming a single-root model that `FlatModel` does not enforce elsewhere. -/
private def reservedRootGroupName? (model : FlatModel) : Option String :=
  (model.fields.map (·.groupPath) ++ model.repeatableGroups.map (·.path)).findSome? fun path =>
    match path.head? with
    | some name => if isReservedRootName name then some name else none
    | none => none

/-- The declared maximum row count A12 still admits, which depends on the declaring carrier: a root
    group stops an order of magnitude below a nested one. Both bounds are measured
    ([`kf365`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf365)). -/
def repeatabilityCap (path : GroupPath) : Nat :=
  if path.length ≤ 1 then 999999999 else 1999999999

private def repeatabilityAboveCap? (groups : List RepeatableGroupDecl) :
    Option (List String × Nat × Nat) :=
  groups.findSome? fun group =>
    match group.repeatability with
    | some declared =>
        let cap := repeatabilityCap group.path
        if cap < declared then some (group.path, declared, cap) else none
    | none => none

def FlatModel.validate (model : FlatModel) : Except ResolveError Unit := do
  match reservedRootGroupName? model with
  | some name => throw (.reservedRootGroupName name)
  | none => pure ()
  match repeatabilityAboveCap? model.repeatableGroups with
  | some (path, declared, cap) => throw (.repeatabilityAboveCap path declared cap)
  | none => pure ()
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
  match temporalTargetPolicyError? model.fields with
  | some error => throw error
  | none => pure ()
  match dateRangeDeclarationPolicyError? model.fields with
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

/-- Whether a group carries at least one field anywhere in its subtree.

This is the Kernel's own group-operand gate. Measured 2026-08-29, an operand naming a group whose
subtree carries no field is refused `MVK_GROUP_IS_EMPTY` (and `MVK_ROOT_GROUP_IS_EMPTY` for a root),
while a group populated only through a descendant subgroup is admitted, so the test is over the whole
subtree rather than the direct children ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-empty-declared-group)).
It is deliberately not the same question as `hasGroupPath`: a group with no fields may still be
**present**, because a repeatable declaration names it. -/
def FlatModel.groupContributesField (model : FlatModel) (path : GroupPath) : Bool :=
  model.fields.any fun declaration => path.isPrefixOf declaration.groupPath

/-- A group is present in the flattened namespace when it owns or contains a declared field, or has its own repeatable declaration.

An empty **nonrepeatable** group is therefore outside this representation, and that is a limit of `FlatModel` rather than of the Kernel: measured 2026-08-29, the Kernel admits such a group and reports the model valid ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-empty-declared-group)). One gate would diverge if that input could be built, since the message group position's root gate reports its undeclared-root class where the Kernel reports the ordinary group class; no `FlatModel` can build it, and giving groups their own declaration list is the change that would lift the limit, which [SG9](../../../docs/SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion) carries.

An empty **repeatable** group is a different matter and *is* expressible, because a repeatable declaration names its group directly. Presence is therefore not admission: `groupContributesField` is the gate a group **operand** must pass, and this query is not. -/
def FlatModel.hasGroupPath (model : FlatModel) (path : GroupPath) : Bool :=
  GroupPath.isValid path &&
    (model.groupContributesField path ||
      model.repeatableGroups.any fun group => group.path == path)

/-- Whether a name is a declared root group. The Kernel resolves a field or group path segment by
    segment, so a path that misses reports the root-group class exactly when its first segment fails
    this test, whatever follows, and the entity class for a later miss
    ([fields](../../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier),
    [groups](../../../docs/sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)). -/
def FlatModel.declaresRoot (model : FlatModel) (name : String) : Bool :=
  model.hasGroupPath [name]

/-- Every field declared anywhere in a group's subtree, in declaration order. A group declares no kind, value, or instance of its own, so this recursive extent is the whole of what a group-scope operand contributes, and a deeper descendant group's field belongs to it exactly like a direct child's.

    Every group expansion in the theory routes through this one query rather than re-deriving the walk at each operand site, so no site can disagree with a sibling about how far a group reaches. -/
def FlatModel.groupSubtreeFields (model : FlatModel) (path : GroupPath) :
    List FlatFieldDecl :=
  model.fields.filter fun declaration => path.isPrefixOf declaration.groupPath

/-- Whether some repeatable group declares this field as its index. -/
def FlatModel.isIndexField (model : FlatModel) (field : FieldId) : Bool :=
  model.repeatableGroups.any fun group => group.indexField == some field

/-- How many cells one declaration contributes beneath a group whose own repeatable ancestry already
covers `enclosing` levels: one per row combination its remaining repeatable ancestors may reach.
A declaration with no repeatable ancestor below that group contributes exactly one. `none` is an
unretained maximum on some level, which has no finite contribution and lies outside the measured
repeatability domain `RepeatableGroupDecl.repeatability` records. -/
def FlatModel.declarationSlots? (model : FlatModel) (enclosing : Nat)
    (declaration : FlatFieldDecl) : Option Nat :=
  (declaration.repeatableScope.drop enclosing).foldl (init := some 1)
    fun rows level =>
      rows.bind fun product =>
        (model.repeatableGroupAtLevel? level).bind fun group =>
          group.repeatability.map (· * product)

/-- Sum declaration capacities below the already bound ancestry. Fixed-group count movement and
starred field-fill predicates differ in where that ancestry stops, but count the same remaining
row combinations per declaration ([group-fill checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-group-field-fill-declared-slots)). -/
def FlatModel.declarationsSlotCapacity? (model : FlatModel) (enclosing : Nat)
    (declarations : List FlatFieldDecl) : Option Nat :=
  declarations.foldl (init := some 0)
    fun total declaration =>
      total.bind fun accumulated =>
        (model.declarationSlots? enclosing declaration).map (accumulated + ·)

/-- The declared **slot capacity** of a group's subtree: how many cells a document can hold beneath
this group once every repeatable descendant is filled to its declared maximum. `none` means some
descendant's maximum is not retained, so the subtree has no finite capacity to reach.

This is deliberately not `(groupSubtreeFields path).length`. The two coincide exactly when the
subtree owns no repeatable descendant, so a movement rule keyed on the declaration count looks
correct on every model without one — and kernel 30.8.1 keeps such a count grow-only until this
capacity is reached, not until the declaration count is
([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-filled-field-count-nested-capacity)). -/
def FlatModel.groupSubtreeSlotCapacity? (model : FlatModel) (path : GroupPath) :
    Option Nat :=
  model.declarationsSlotCapacity? (model.repeatableScopeForGroupPath path).length
    (model.groupSubtreeFields path)

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

/-- Whether every repeatable level a declaration crosses is already bound by the reading scope.
The empty scope admits exactly the nonrepeatable declarations, so a scalar read is this predicate's
`[]` instance rather than a separate rule. The scope a caller supplies is the reading rule's own
iteration scope, or a computation's target scope. -/
def FlatFieldDecl.repetitionBoundBy (declaration : FlatFieldDecl)
    (scope : List RepeatableLevel) : Bool :=
  declaration.repeatableScope.all (scope.contains ·)

def FlatFieldDecl.requireNonrepeatable (declaration : FlatFieldDecl) :
    Except ResolveError FlatFieldDecl :=
  if declaration.repeatableScope.isEmpty then
    .ok declaration
  else
    .error (.repeatableReference declaration.path)

/-- Refuse a repeatable declaration for a fragment that reads nonrepeatable operands only, split by
whether `scope`, the reading rule's iterated levels, already binds every level of it. Unbound is the
Kernel's missing wildcard; bound is only this fragment's boundary, because the Kernel admits that
read. -/
def FlatFieldDecl.requireNonrepeatableAt (declaration : FlatFieldDecl)
    (scope : List RepeatableLevel) : Except ResolveError FlatFieldDecl :=
  if declaration.repeatableScope.isEmpty then
    .ok declaration
  else if declaration.repetitionBoundBy scope then
    .error (.boundRepeatableReference declaration.path)
  else
    .error (.repeatableReference declaration.path)

/-- Accept one operand whose repeatable levels the reading scope binds, and otherwise report the
same repeatable-reference class the nonrepeatable resolver reports: unplaced, the Kernel reports one
missing-wildcard class for both. A caller that knows the written field replaces the refusal with
the level `unboundReadLevel?` places. -/
def FlatFieldDecl.requireRepetitionBoundBy (declaration : FlatFieldDecl)
    (scope : List RepeatableLevel) : Except ResolveError FlatFieldDecl :=
  if declaration.repetitionBoundBy scope then
    .ok declaration
  else
    .error (.repeatableReference declaration.path)

/-- Resolve one declaration by stable ID and reject repeatable targets or operands. -/
def FlatModel.resolveNonrepeatableDeclarationById
    (model : FlatModel) (field : FieldId) :
    Except ResolveError FlatFieldDecl := do
  (← model.lookupUniqueId field).requireNonrepeatable

/- Resolve a bare single-segment reference exactly as the kernel parser does: try the declaring
   group, then (when enabled) require one model-wide short-name match. A name the declaring group
   declares as a group takes no fallback, so every field resolver reports it as a miss, however many
   fields elsewhere share the name
   ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)).
   A site that displaces a group miss classes it as the group; any other carrier keeps the miss's
   entity class, which no row measures on a bare name.
   There is deliberately no implicit ancestor walk; parent lookup requires `..`. -/
private def FlatModel.resolveBareDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  match ← model.lookupPath? (declaringGroup ++ [reference.field]) with
  | some declaration => pure declaration
  | none =>
      if model.hasGroupPath (declaringGroup ++ [reference.field]) then
        throw (.invalidEntity reference)
      else if model.fieldRefByShortNameAllowed then
        match model.fields.filter (fun declaration => declaration.name == reference.field) with
        | [] => throw (.invalidEntity reference)
        | [declaration] => pure declaration
        | _ => throw (.shortNameNotUnique reference.field)
      else
        throw (.invalidEntity reference)

/-- The first segment of a longer relative path when the declaring group declares neither a group
    nor a field by that name, which is where the short-name fallback answers. Measured only on paths
    without a leading up-step, so any other path returns `none`. -/
def FlatModel.unresolvedFirstSegment? (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Option String := do
  let .relative 0 := reference.base | none
  let first ← reference.groups.head?
  let own := declaringGroup ++ [first]
  if model.hasGroupPath own || model.fields.any (·.path == own) then none
  pure first

/-- The field the short-name fallback binds a longer relative path's first segment to, when exactly
    one declaration carries that name. -/
def FlatModel.shortNameFirstSegmentField? (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Option FlatFieldDecl := do
  let first ← model.unresolvedFirstSegment? declaringGroup reference
  if !model.fieldRefByShortNameAllowed then none
  match model.fields.filter (·.name == first) with
  | [declaration] => some declaration
  | _ => none

/-- Shared path mechanism for both non-repeatable and repeatable elaborators. This resolves one declaration without deciding whether its repeatable scope is legal for the caller. -/
def FlatModel.resolveFieldDeclarationUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  if !GroupPath.isValid declaringGroup then throw (.invalidRuleGroup declaringGroup)
  -- An undeclared first segment answers before any later segment and before a lone segment's
  -- missing field is judged.
  if let .absolute := reference.base then
    let root := reference.groups.headD reference.field
    if validName root && !model.declaresRoot root then throw (.unknownRootGroup reference)
  if !reference.hasValidShape then throw (.invalidReference reference)
  match reference.base with
  | .absolute =>
      match ← model.lookupPath? (reference.groups ++ [reference.field]) with
      | some declaration => pure declaration
      | none => throw (.invalidEntity reference)
  | .relative parents =>
      if parents == 0 && reference.groups.isEmpty then
        model.resolveBareDeclaration declaringGroup reference
      else if let some first := model.unresolvedFirstSegment? declaringGroup reference then
        -- The short-name fallback answers a relative path's first segment whatever follows it. A
        -- unique match binds a field and the segment below it misses, so only an ambiguous one
        -- changes the class ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-path-walk)).
        if model.fieldRefByShortNameAllowed &&
            (model.fields.filter (·.name == first)).length > 1 then
          throw (.shortNameNotUnique first)
        else
          throw (.invalidEntity reference)
      else
        let base ← GroupPath.walkUp declaringGroup parents
        if !base.matchesTurningPoint reference.turningPoint then
          throw (.invalidEntity reference)
        else
          match ← model.lookupPath? (base ++ reference.groups ++ [reference.field]) with
          | some declaration => pure declaration
          | none => throw (.invalidEntity reference)

/-- The declared group a field reference's path names, or `none` when it names none. -/
def FlatModel.groupNamedBy? (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Option GroupPath := do
  let base ← match reference.base with
    -- A turning point on an absolute path is a spelling defect, whatever group the path names.
    | .absolute => if reference.turningPoint.isSome then none else some []
    | .relative parents =>
        match GroupPath.walkUp declaringGroup parents with
        | .ok base => if base.matchesTurningPoint reference.turningPoint then some base else none
        | .error _ => none
  let group := base ++ reference.groups ++ [reference.field]
  if model.hasGroupPath group then some group else none

/-- Class a presence predicate's or a field-value read's field operand whose path names a declared
    group rather than a field, or `none` when it names none. The rule group binds and the written field places an
    unbound level, as for any read, and a level the walk passes leaves the root and kind gates to
    answer: a legal parallel iteration draws the kind class
    ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-25-parallel-index-gates)). -/
def FlatModel.groupFieldSlotRefusal? (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (reference : SurfaceFieldPath) : Option (GroupPath × GroupFieldSlotRefusal) := do
  let group ← model.groupNamedBy? declaringGroup reference
  match model.refusedReadLevel? declaringGroup writtenGroup (model.repeatableScopeForGroupPath group) with
  | some unbound => some (group, .unboundLevel unbound)
  | none => if group.length == 1 then some (group, .root) else some (group, .group)

/-- Resolve a presence predicate's field operand with `resolve`, classing a path that names a group
    by `groupFieldSlotRefusal?` instead of as the field miss `resolve` reports. Only a failure about
    the reference is displaced: an invalid rule group answers ahead of any operand. -/
def FlatModel.resolvePresenceOperand (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (reference : SurfaceFieldPath) (resolve : Except ResolveError FlatFieldDecl) :
    Except ResolveError FlatFieldDecl :=
  let displace (error : ResolveError) : Except ResolveError FlatFieldDecl :=
    match model.groupFieldSlotRefusal? declaringGroup writtenGroup reference with
    | some (group, refusal) => .error (.groupInFieldSlot group refusal error)
    | none => .error error
  match resolve with
  | .ok declaration => .ok declaration
  | .error error => if error.isGroupDisplaceableMiss then displace error else .error error

/-- Resolve a nonrepeatable operand of a condition after a caller has validated the model.
`declaringGroup` is the reading rule's group. With the error field at or below it, an operand that
group already iterates is refused as this fragment's boundary rather than as the missing wildcard;
with the error field outside it nothing binds a level, so that operand draws containment. Either way
a level left unbound is classed by `writtenGroup`, the error field's group, which the rule group
stands in for when a caller has none. -/
def FlatModel.resolveNonrepeatableFieldUnchecked (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath)
    (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl := do
  let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup reference
  match model.unboundReadLevel? declaringGroup writtenGroup declaration.repeatableScope with
  | some unbound => throw (.unboundOperandLevel declaration.path unbound)
  | none => declaration.requireNonrepeatableAt (model.repeatableScopeForGroupPath declaringGroup)

/-- Resolve one structured field path against a validated expanded model while preserving its repeatable scope for a later elaborator. -/
def FlatModel.resolveFieldDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveFieldDeclarationUnchecked declaringGroup reference

/-- Resolve one structured field path against a validated expanded model. -/
def FlatModel.resolveField (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl := do
  model.validate
  model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup

/-- Validate selected-language quote provenance and then reuse the sole checked nonrepeatable field resolver. -/
def FlatModel.resolveAuthoredField (model : FlatModel)
    (profile : PathKeywordProfile) (declaringGroup : GroupPath)
    (reference : AuthoredFieldPath) :
    Except AuthoredFieldPathError FlatFieldDecl := do
  let path ← (reference.lower profile).mapError .syntax
  (model.resolveField declaringGroup path).mapError .resolve


/-- A successful reference resolution certifies its declaring group. The guard above rejects an
unrepresentable group before anything else, so every consumer holding an `.ok` result may state
group validity instead of re-testing it. -/
theorem FlatModel.resolveFieldDeclarationUnchecked_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {reference : SurfaceFieldPath}
    {declaration : FlatFieldDecl}
    (resolved :
      model.resolveFieldDeclarationUnchecked declaringGroup reference = .ok declaration) :
    GroupPath.isValid declaringGroup = true := by
  cases hValid : GroupPath.isValid declaringGroup with
  | true => rfl
  | false =>
    rw [FlatModel.resolveFieldDeclarationUnchecked] at resolved
    simp only [hValid, Bool.not_false, if_true, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at resolved
    cases resolved

end A12Kernel
