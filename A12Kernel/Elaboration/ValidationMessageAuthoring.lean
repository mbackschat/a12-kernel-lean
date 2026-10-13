import A12Kernel.Elaboration.ValidationMessageTypes

/-! # Checked authoring for validation-message templates

Each parameter is decoded on its own by `MessageParameterSyntax` into the events the Kernel's parser
meets — every name resolved as it ends, a key's nesting refused, a fault where it stands — and its
form's check, and this module runs them in that order. A parameter's entity spec is the **shared path
grammar** the condition parser uses, so the decoder reads the same separators and hands the result to
the one existing field resolver rather than carrying a second lookup: a leading `/` is absolute, each leading `..` crosses one enclosing group
with an optional explicit turning point after the last of them, and `/` separates the remaining group
names from the field. A field is therefore addressable by its bare name when that name is unique, by
a path relative to the rule group, or absolutely when it lies outside the rule context.

A name that collides with a terminal is written in the grammar's **single-quote** escape, and the
quotes are erased before any semantic lookup, so an unnecessary quote is transparent. This producer's
quoting requirement is deliberately **narrower** than the condition language's: a set of terminals is
historically accepted unquoted inside an entity name, and the caller supplies both lists from the
language version it supports.

A field reference may carry an Enumeration **category** suffix, `->Name`, whose three gates are the
Kernel's own: a missing name, a field that is not an Enumeration, and a name that is not one of that
declaration's categories. It carries neither of the value suffix's extra gates, and combining it with the value suffix is a parse failure — the two really are alternatives. A **doubled** arrow is refused
only after the first category's kind and membership gates pass. Its diagnostic therefore depends on
that first name: an undeclared category or a non-Enumeration field stops at its own gate, while a
declared category reaches the trailing-syntax refusal. What a category access **renders** is measured: the category
token the field's current stored value maps to, so the checked part carries the declaration's own
mapping and the caller supplies only the stored token. An absent stored token renders as the empty
string, which is measured. A token the category does not map cannot arise, and that is now the
Kernel's rule rather than this fragment's convenience: a category's token list must have exactly as
many entries as the enum has values, paired by position, so every value carries exactly one token
([reconciliation](../../docs/sources/computation-placement-and-constant-probes.md#src-2026-08-29-reconciliation)).

A field reference may finally carry a **semantic-index key**, `For "k"` or `For SomeField`, after any
value or category suffix — that order is the grammar's, not a preference. Its gate is on the
**semantic index**, not on the field: the condition must use that same index the same way, and the
keyed field itself need not be a condition operand at all. That freedom is **narrower than it first
measured**, and the correction is worth carrying here because the wide reading is the natural one.
A keyed parameter may name a field the condition never references, but only one such field — the
group's **declared index field** — so the admitted set is exactly the fields the condition selects
under that key, through a keyed field or a keyed group read, together with that index field, and a
*third* field of the same group, keyed identically, is refused. What must match is the keyed group and key plus the displayed field being one of those two,
not the group's fields at large; a fixture whose group declares only those two cannot tell the two
readings apart, which is how both this project and a12-dmkits published the wide one
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-keyed-parameter-admits-the-index-field-only)). The unkeyed
spelling of a keyed field stays refused, so condition membership belongs to the unkeyed form alone,
and the pairing is exact in the other direction too: a keyed condition operand does not license an
unkeyed parameter.

No flat condition reads a field under a key, so the flat entry point refuses every keyed parameter,
`MVK_INDEX_FOR_ERROR_TEXT_INVALID` in the name position and `INVALID_GROUP` in the group position,
both measured on the flat model; the grammar in front of that gate — suffix order, key spelling,
nesting, whitespace — answers first. On a rule, a keyed field parameter is a member when the
condition selects the field's nearest indexed group by the same spelled key, and it renders that
selected row; a keyed group parameter additionally requires its matching positive presence guard.

A parameter written `$#...$` occupies the **group position**, which is a different position from the
name one and resolves the same words differently: bare `$RootGroup$` is an entity lookup and refused,
while `$#RootGroup$` is admitted. Its argument is one of the two keyword shorthands for the endpoints
of the rule's ancestor chain or a group path, absolute or relative to the rule's group, so a bare word
names a group directly below it, falling back to a field's short name and never to a group's. The
argument is refused in the order the Kernel's parser meets it: each lexer or syntax fault where it
stands, a keyword or path's check once that alternative is complete, and a token left after it only
then. The named group
must be **available**: the rule's own group and its ancestors always are, and so is any group holding a
field the condition reads, which admits a read descendant or sibling and refuses the same group when
nothing in it is read. An absolute path resolves in two stages the Kernel reports apart, an undeclared
root ahead of availability, and its segments take the same quote escape as a name — but only an
unquoted word opens a keyword alternative, so quoting a terminal turns it back into an ordinary group
name. Two historic terminals keep their own refusal class, which the Kernel reports distinctly rather
than as an unknown group, and quoting removes that reading too.

One **non-field** parameter form is admitted: the Base Year terminal with an optional signed offset.
Its only static gate is that the model declares a Base Year, and the offset is applied at authoring
because nothing about it depends on the document.

Two **form-pointer** forms are admitted beside those, `<entity>.Vordruckzeile` and
`<entity>.Vordruckname`. They share the name position's entity spec and nothing else: their one gate
resolves that entity to a field, and the condition-membership requirement every other field form
carries **does not apply** — the Kernel admits both on a field the condition never references, which
is why the checked part has no membership witness to carry rather than an unset one. What either
renders is unmeasured and stays caller-supplied.

The index terminal uses the checked rule's actual error declaration and condition-reference modes.
Its resolution and suffix gates are owned by `IndexMessageAuthoring`.

A name resolves wherever its path leads, a repeatable field included: the rule's group, a deeper or a
starred group, all resolve alike, and membership in the condition decides
([iteration checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates)).
A read only through a semantic-index selection does not make an unkeyed parameter a member. The value
suffix then asks two questions the name form does not: whether some read of the field writes no
wildcard, and whether a String field skips value validation, each refused on its own class.
-/

namespace A12Kernel

/-- Treat an exempt terminal as if the author had quoted it, then reuse the one existing
quote-provenance lowering. The exemption says exactly "no quote is needed here", so recording it as
quoted expresses that decision in the shared type instead of duplicating the lowering walk. -/
private def exemptQuoting (profile : ValidationMessageKeywordProfile)
    (name : AuthoredPathName) : AuthoredPathName :=
  if profile.unquotedTerminals.contains name.text then
    { name with quoted := true }
  else
    name

/-- The model a message parameter's name resolves in: the same declarations with the short-name tier
always on. Measured, a model whose flag is off still answers a message name by its model-wide short
name — ambiguous, unread, read, or form-pointed — while the same model's condition refuses a short name
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
def FlatModel.messageNameModel (model : FlatModel) : FlatModel :=
  { model with fieldRefByShortNameAllowed := true }

/-- A message key literal as `group`'s index column reads it. The authored spelling is kept because the
key gate compares spellings, and the decoded token is what selects the rendered row: on a Number index
`"2"` selects the row keyed 2 ([checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15),
rule `RNum`). A spelling the column cannot read keeps its text and matches no condition key. -/
def messageLiteralKey (model : FlatModel) (group : Option RepeatableGroupDecl) (text : String) :
    CheckedSemanticIndexKey :=
  let token := (do
    let index ← (← group).indexField
    let declaration ← model.fields.find? (fun (field : FlatFieldDecl) => field.id == index)
    declaration.semanticIndexLiteral? text).getD (.text text)
  .literal token (some text)

/-- One checked field reference of a message parameter. `parameter` retains the authored spelling for
Explain, including any value suffix; `reference` is its decoded path, which is what resolved. A keyed
parameter's `key` selects the row it renders, and its membership is the keyed gate rather than the
unkeyed one. -/
structure CheckedValidationMessageReference
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  parameter : String
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.messageNameModel.resolveFieldDeclarationUnchecked condition.rowGroup reference =
      .ok declaration
  key : Option CheckedSemanticIndexKey := none
  conditionReferenced :
    condition.messageAdmits declaration key = some true

/-- One checked form-pointer parameter. It is deliberately **not** a `CheckedValidationMessageReference`
carrying a flag: the difference between the two is precisely that this one has no membership witness to
carry, and a shared record with an optional field would let a consumer read the exemption as missing
data rather than as the measured rule. -/
structure CheckedValidationMessageFormPointer
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  parameter : String
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  pointer : MessageFormPointer
  resolved :
    model.messageNameModel.resolveFieldDeclarationUnchecked condition.rowGroup reference =
      .ok declaration

/-- One checked category access: the field reference beside the resolved projection, with witnesses
that the projection belongs to *that* field's own Enumeration declaration and selects *that* category.
Together with the projection's own check this is the complete gate. -/
structure CheckedValidationMessageCategory
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  reference : CheckedValidationMessageReference model condition
  category : String
  projection : CheckedEnumerationProjection
  enumerationOwned :
    reference.declaration.enumeration = some projection.declaration.declaration
  categorySelected : projection.projectionRef = .category category

/-- Whether a message may name `group` in the group position: it is the rule's own group or one of its
ancestors, or it holds, at any depth, a field the condition reads. The second arm is why a descendant,
a sibling, and an intermediate group holding no read field directly are all nameable once the condition
reads below them, and why the same groups are refused when it does not
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability)). A
field is never available, because its own path is never a prefix of its group's. -/
def messageGroupAvailable (model : FlatModel) (condition : ValidationMessageCondition model)
    (group : GroupPath) : Bool :=
  GroupPath.isPrefixOf group condition.rowGroup ||
    model.fields.any fun declaration =>
      condition.core.referencesField declaration.id &&
        GroupPath.isPrefixOf group declaration.groupPath

/-- One admitted group-position parameter: the group the author named, beside the witnesses that it is
a representable path and that it is **available** to this rule's message. -/
structure CheckedValidationMessageGroup
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  parameter : String
  group : GroupPath
  valid : GroupPath.isValid group = true
  available : messageGroupAvailable model condition group = true
  key : Option CheckedSemanticIndexKey := none

/-- Admit one resolved group under the two gates every argument shares: it is a representable path,
and it is available. Below the root gate, availability needs no separate existence test, because every
ancestor of a declared group and every group holding a declared field is itself declared — so a group
passing it is declared, and one failing it is refused whether or not the model declares it, which is
what a **declared** unread group and an unknown one sharing one refusal already says. -/
def admitMessageGroup {model : FlatModel}
    (condition : ValidationMessageCondition model) (parameter : String)
    (group : GroupPath) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  if hValid : GroupPath.isValid group = true then
    if hAvailable : messageGroupAvailable model condition group = true then
      .ok { parameter, group, valid := hValid, available := hAvailable }
    else
      .error (.invalidGroupParameter parameter)
  else
    .error (.invalidGroupParameter parameter)

private def knownMessageReference (parameter : String) : Option Bool →
    Except ValidationMessageTemplateError Bool
  | some answer => pure answer
  | none => throw (.groupReferenceMetadataRequired parameter)

/-- Group availability, wildcard mode, and positive keyed presence are distinct gates
(FullChecks_ErrorTextParameterParser.checkLevelParam). -/
private def checkMessageGroupMode (condition : ValidationMessageCondition model)
    (parameter : String) (group : GroupPath) (key : Option CheckedSemanticIndexKey) :
    Except ValidationMessageTemplateError Unit := do
  match condition with
  | .flat _ =>
      if key.isSome then throw (.invalidGroupParameter parameter)
  | .rule _ | .parallel _ _ =>
      match model.repeatableGroups.find? (·.path == group) with
      | none => if key.isSome then throw (.invalidGroupParameter parameter)
      | some declaration =>
          match key with
          | some key =>
              let selected ← knownMessageReference parameter (condition.selectedGroupReferenced? group (some key))
              if declaration.indexField.isNone || !selected then
                throw (.invalidGroupParameter parameter)
          | none =>
              if declaration.indexField.isSome then
                let available ← knownMessageReference parameter (condition.unkeyedGroupReferenced? group declaration.level)
                if !available then
                  let selected ← knownMessageReference parameter condition.anySelectedGroupReferenced?
                  if !(group.isPrefixOf condition.rowGroup) || selected then
                    throw (.invalidGroupParameter parameter)
          if declaration.repeatability.any (· > 1) then
            match condition.nonWildcardGroupReferenced? group declaration.level with
            | some true => pure ()
            | some false => throw (.groupReferenceMode parameter .iterParamWithStarReference)
            | none => throw (.groupReferenceMetadataRequired parameter)
          if let some key := key then
            if !condition.keyedGroupGuarded group key then
              throw (.groupReferenceMode parameter .invalidUseOfSemanticIndex)

/-- Whether a path names a declared group or field. -/
def FlatModel.declaresEntityPath (model : FlatModel) (path : GroupPath) : Bool :=
  model.hasGroupPath path || model.fields.any (·.path == path)

/-- A relative group argument's parent walk and its check, which the Kernel runs when the walk's own
rule ends: a climb past the root first, then a turning point that does not name the group reached. -/
def walkMessageGroup {model : FlatModel} (condition : ValidationMessageCondition model)
    (parameter : String) (parents : Nat) (turningPoint : Option String) :
    Except ValidationMessageTemplateError GroupPath :=
  match GroupPath.walkUp condition.rowGroup parents with
  | .error _ => .error (.parameterAboveRoot parameter)
  | .ok base =>
      if base.matchesTurningPoint turningPoint then .ok base
      else .error (.turningPointMismatch parameter)

/-- Look one group-position argument up against the rule's own group, before its availability is
asked. An absolute path resolves in the two stages the Kernel reports apart: its first segment must
name a declared root group, and then the whole path must name an entity. The root gate belongs to the
absolute form alone — a keyword or a relative path resolves from the rule's own group, which
introduces no root the model might not declare. A relative path walks up first, refusing a climb past
the root, then checks its turning point against the group reached, and only then descends. A single
bare word that names nothing below the rule's group falls back to the short name of a **field**, the
only kind that lookup covers
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)). -/
def resolveMessageGroup {model : FlatModel} (condition : ValidationMessageCondition model)
    (parameter : String) : AuthoredMessageGroup → Except ValidationMessageTemplateError GroupPath
  -- The root shorthand is the top of the *rule's own* ancestor chain rather than a model-wide root.
  -- A model with two roots separates the two readings, and the rule's own chain is what the Kernel
  -- admits: under the second root the shorthand is accepted while the first root is refused.
  -- The shorthand carries a placement condition the other two spellings do not: a rule sitting
  -- directly in a root group may not use it. Measured on both carriers, and it is the gate the
  -- availability test cannot express, because a root group is trivially its own ancestor.
  | .ruleGroup =>
      if condition.rowGroup.length ≤ 1 then
        .error (.ruleGroupImmediatelyBelowRoot parameter)
      else
        .ok condition.rowGroup
  -- The root shorthand is the serial parameter, whose one gate is the condition's parallel iteration.
  | .rootGroup =>
      match hashParameterRefusal .a12 { parallelIteration := condition.parallelIteration } .serial with
      | some diagnostic => .error (.groupReferenceMode parameter diagnostic)
      | none => .ok (condition.rowGroup.take 1)
  | .absolute [] => .error (.invalidGroupParameter parameter)
  | .absolute (root :: rest) =>
      -- A root declaring no field is still a declared root: `$#/Hollow$` on one draws the ordinary
      -- group class, where an undeclared root draws the root class
      -- ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-empty-declared-group)).
      if !(model.hasGroupPath [root] || model.declaresEmptyGroup [root]) then
        .error (.unknownRootGroup parameter root)
      else if model.declaresEntityPath (root :: rest) then
        .ok (root :: rest)
      else
        .error (.invalidGroupParameter parameter)
  | .relative parents turningPoint path =>
      match walkMessageGroup condition parameter parents turningPoint with
      | .error error => .error error
      | .ok base =>
          if model.declaresEntityPath (base ++ path) then
            .ok (base ++ path)
          else
            match parents, path with
            | 0, [name] =>
                match model.fields.filter (·.name == name) with
                | [declaration] => .ok declaration.path
                | [] => .error (.invalidGroupParameter parameter)
                | _ => .error (.groupShortNameNotUnique parameter name)
            | _, _ => .error (.invalidGroupParameter parameter)

/-- Check one group-position argument: look it up, accept the group only if it is available, and only
then refuse a token left after the path. The lookup and availability are the alternative's check,
which the Kernel runs before it meets the end of the text: `$#He-ad$` and the unavailable `$#Side-x$`
draw the group class, and only `$#Head-x$` the syntax class
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events)). A
fault met after a complete parent walk waits for the walk's check and the lookup of the names consumed
before it, so `$#..Wrong/$` draws the turning-point class and `$#../Nope/$` the group class rather than
the truncated one. `keyCheck` is the outcome of a key's events, which the caller resolves on this
position's classes. -/
def checkMessageGroup {model : FlatModel} (condition : ValidationMessageCondition model)
    (parameter : String) (authored : AuthoredMessageGroup)
    (remainder : MessageGroupRemainder := .none)
    (keyCheck : Except ValidationMessageTemplateError (Option CheckedSemanticIndexKey) := .ok none) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  match remainder, authored with
  | .afterWalk fault, .relative parents turningPoint names =>
      match walkMessageGroup condition parameter parents turningPoint with
      | .error error => .error error
      | .ok _ =>
          if names.isEmpty then .error (.parameterSyntax parameter fault)
          else
            match resolveMessageGroup condition parameter authored with
            | .error error => .error error
            | .ok _ => .error (.parameterSyntax parameter fault)
  | .afterWalk fault, _ => .error (.parameterSyntax parameter fault)
  | .keyed _ _ trailing, _ =>
      match resolveMessageGroup condition parameter authored with
      | .error error => .error error
      | .ok group =>
          match keyCheck with
          | .error error => .error error
          | .ok none => .error (.invalidGroupParameter parameter)
          | .ok (some key) => do
              let key := match key with
                | .literal _ (some text) =>
                    messageLiteralKey model (model.repeatableGroups.find? (·.path == group)) text
                | key => key
              let access ← admitMessageGroup condition parameter group
              checkMessageGroupMode condition parameter group (some key)
              if trailing then throw (.parameterSyntax parameter .unexpected)
              pure { access with key := some key }
  | _, _ =>
      match resolveMessageGroup condition parameter authored with
      | .error error => .error error
      | .ok group =>
          match admitMessageGroup condition parameter group with
          | .error error => .error error
          | .ok access => do
              checkMessageGroupMode condition parameter group none
              if remainder = .trailing then .error (.parameterSyntax parameter .unexpected)
              else .ok access

inductive CheckedValidationMessagePart
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  | text (value : String)
  | fieldName (reference : CheckedValidationMessageReference model condition)
  | fieldValue (reference : CheckedValidationMessageReference model condition)
  | fieldCategory (access : CheckedValidationMessageCategory model condition)
  /-- The Base Year with its authored offset already applied, beside the witnesses that the model
  declares that year and that the arithmetic is the authored one. -/
  | baseYear (offset year : Int)
      (declared : model.baseYear = some (year - offset))
  | group (access : CheckedValidationMessageGroup model condition)
  | indexField (access : CheckedMessageIndex model condition)
  /-- A form-pointer parameter, whose resolved entity carries no membership witness because the
  Kernel requires none here. -/
  | formPointer (access : CheckedValidationMessageFormPointer model condition)

structure CheckedValidationMessageTemplate
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  source : String
  parts : List (CheckedValidationMessagePart model condition)

/-- One resolved name-bearing parameter position, carrying its resolution witness but **no**
membership requirement. -/
private structure ResolvedMessageEntity
    (model : FlatModel) (condition : ValidationMessageCondition model) where
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.messageNameModel.resolveFieldDeclarationUnchecked condition.rowGroup reference =
      .ok declaration

private def lowerMessagePath (profile : ValidationMessageKeywordProfile)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError SurfaceFieldPath := do
  -- Every name-bearing position is checked, because a terminal may sit at any path level.
  match ({ authored with
      turningPoint := authored.turningPoint.map (exemptQuoting profile)
      groups := authored.groups.map (exemptQuoting profile)
      field := exemptQuoting profile authored.field
    } : AuthoredFieldPath).lower profile.path with
    | .ok reference => pure reference
    -- The lexer forms an unquoted reserved word as a keyword, which no name slot takes, so the
    -- decoder has already refused it as this token; the lowering's own refusal agrees.
    | .error (.unquotedKeyword _) => throw (.parameterSyntax parameter .unexpected)

/-- Resolve one name-bearing parameter position to a declaration, or to the declared group it names.
This is the part a keyed parameter shares with an unkeyed one: measured, an unresolvable name is
refused for both, while a group is an entity each form refuses on its own class or not at all
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). -/
private def resolveMessageEntity (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (ResolvedMessageEntity model condition ⊕ GroupPath) := do
  let reference ← lowerMessagePath profile parameter authored
  match hResolved :
      model.messageNameModel.resolveFieldDeclarationUnchecked condition.rowGroup reference with
  | .error error =>
      match error.isGroupDisplaceableMiss, model.groupNamedBy? condition.rowGroup reference with
      | true, some group => pure (.inr group)
      | _, _ => throw (.reference parameter error)
  | .ok declaration => pure (.inl { reference, declaration, resolved := hResolved })

/-- Resolve one name-position entity spec as the parser resolves it when its names end: a path to a
field or a declared group, a bare parent walk to the group it reaches, and the rule-group terminal to
nothing, since the Kernel's name check skips it. A bare walk's climb past the root and its turning
point answer on the group position's classes, measured in the name position too. -/
private def resolveMessageSpec (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (parameter : String) :
    MessageEntitySpec →
      Except ValidationMessageTemplateError
        (Option (ResolvedMessageEntity model condition ⊕ GroupPath))
  | .ruleGroup => pure none
  | .walk parents turningPoint =>
      (some ∘ .inr) <$> walkMessageGroup condition parameter parents (turningPoint.map (·.text))
  | .path authored => some <$> resolveMessageEntity model profile condition parameter authored

private def resolveMessageGroupKeyEntity (model : FlatModel)
    (profile : ValidationMessageKeywordProfile) (condition : ValidationMessageCondition model)
    (parameter : String) (spec : MessageEntitySpec) :
    Except ValidationMessageTemplateError (Option CheckedSemanticIndexKey) := do
  match condition, spec with
  | .rule _, .path authored =>
      let reference ← lowerMessagePath profile parameter authored
      match model.messageNameModel.resolveFieldDeclarationUnchecked condition.rowGroup reference with
      | .ok declaration => pure (some (.field declaration))
      | .error error =>
          if error.isGroupDisplaceableMiss && (model.groupNamedBy? condition.rowGroup reference).isSome then
            pure none
          else throw (.reference parameter error)
  | _, _ =>
      match ← resolveMessageSpec model profile condition parameter spec with
      | some (.inl entity) => pure (some (.field entity.declaration))
      | some (.inr _) => pure none
      | none => throw (.ruleGroupUnresolved parameter)

private def resolveMessageReference (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model)
    (parameter : String) (spec : MessageEntitySpec) (keyHead : Option MessageKeyHead) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageReference model condition) := do
  let entity ← match ← resolveMessageSpec model profile condition parameter spec, keyHead with
    | some (.inl entity), _ => pure entity
    | some (.inr _), some (.entity .ruleGroup) => throw (.ruleGroupUnresolved parameter)
    -- A keyed group meets the key's gate, measured beside a condition keying that group (row `b01`).
    | some (.inr _), some _ => throw (.keyNotInCondition parameter)
    | some (.inr group), none => throw (.groupInNamePosition parameter group)
    | none, _ => throw (.ruleGroupParameter parameter)
  let key ← keyHead.mapM fun
    | .literal text =>
        pure (messageLiteralKey model (model.semanticIndexGroupForPath? entity.declaration.groupPath) text)
    | .entity .ruleGroup => throw (.ruleGroupUnresolved parameter)
    | .entity keySpec => do
        match ← resolveMessageSpec model profile condition parameter keySpec with
        | some (.inl keyEntity) => pure (.field keyEntity.declaration)
        | _ => throw (.keyNotInCondition parameter)
  match hReferenced : condition.messageAdmits entity.declaration key with
  | some true =>
      pure {
        parameter
        reference := entity.reference
        declaration := entity.declaration
        resolved := entity.resolved
        key
        conditionReferenced := hReferenced
      }
  | some false =>
      throw (if key.isSome then .keyNotInCondition parameter
        else .fieldNotReferenced parameter entity.declaration.id)
  | none => throw (.groupReferenceMetadataRequired parameter)

/-- Check the category after entity resolution and condition membership, including an empty name.

The [category-order checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-category-gate-order) separates
these prerequisite failures from the missing-name refusal. Kind and declared-category checks then
reuse the existing Enumeration projection boundary. -/
private def resolveMessageCategory
    (reference : CheckedValidationMessageReference model condition)
    (parameter category : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageCategory model condition) := do
  if category.isEmpty then throw (.missingCategoryName parameter)
  match hSource : reference.declaration.enumeration with
  | none =>
      throw (.categoryFieldNotEnumeration parameter reference.declaration.id)
  | some source =>
      match elaborateEnumeration source with
      | .error _ =>
          throw (.category parameter (.unknownCategory category))
      | .ok checked =>
          match checkEnumerationProjection checked (.category category) with
          | .error error => throw (.category parameter error)
          | .ok projection =>
              if hOwned : source = projection.declaration.declaration ∧
                  projection.projectionRef =
                    EnumerationProjectionRef.category category then
                .ok {
                  reference, category, projection
                  enumerationOwned := by rw [hSource, hOwned.1]
                  categorySelected := hOwned.2 }
              else
                throw (.category parameter (.unknownCategory category))

/-- Run a parameter's events in the parser's order, stopping at the first that fails. A name inside a
group-position key is looked up by the same check as anywhere else, but an unresolved one draws the
group class there, and the rule-group terminal as such a key fails inside the Kernel, which this
fragment leaves unclassed; a root, a parent walk and a turning point keep their classes
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). -/
private def runMessageEvents (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (parameter : String) (inGroupKey : Bool) :
    List MessageParameterEvent → Except ValidationMessageTemplateError Unit
  | [] => pure ()
  | .resolve spec :: rest => do
      if inGroupKey && spec == .ruleGroup then throw (.ruleGroupUnresolved parameter)
      match (if inGroupKey then
          (resolveMessageGroupKeyEntity model profile condition parameter spec).map (fun _ => ())
        else (resolveMessageSpec model profile condition parameter spec).map (fun _ => ())) with
      | .ok _ => pure ()
      | .error error =>
          throw (if inGroupKey && error matches .reference _ (.invalidEntity _) then
            .invalidGroupParameter parameter else error)
      runMessageEvents model profile condition parameter inGroupKey rest
  | .nestedKey :: _ => throw (.nestedSemanticIndex parameter)
  | .fault fault :: _ => throw (.parameterSyntax parameter fault)

/-- A resolved member reference's suffix gates. The keyed read a keyed reference requires writes no
wildcard at its group's level, so the star gate passes a field of that group (rows `k06`, `k09`, `a05`)
but not one of a deeper group (row `v02`). -/
private def checkMessageFieldSuffix (condition : ValidationMessageCondition model)
    (parameter : String) (suffix : MessageFieldSuffix)
    (reference : CheckedValidationMessageReference model condition) :
    Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition) :=
  match suffix with
  | .none => pure (.fieldName reference)
  | .value => do
      let some unstarred := condition.messageUnstarred? reference.declaration.id
        | throw (.groupReferenceMetadataRequired parameter)
      match valueAccessRefusal .a12 {
          referencedWithoutStar := unstarred
          fieldIsString := reference.declaration.policy.kind == .string
          noValueValidation := reference.declaration.isRawString } with
      | some diagnostic => throw (.valueAccess parameter diagnostic)
      | none => pure (.fieldValue reference)
  | .category name => .fieldCategory <$> resolveMessageCategory reference parameter name

/-- The field's own check, which the Kernel runs where the field's rule ends: the rule-group terminal
first, then the membership gate, keyed or not, and the suffix's gates. A key's gate therefore answers
before a category's ([checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15),
rows `e01`–`e03`). A literal key keeps its spelling, which is what the gate compares. -/
private def checkMessageField (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (parameter : String)
    (entity : MessageEntitySpec) (suffix : MessageFieldSuffix) (keyHead : Option MessageKeyHead) :
    Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition) := do
  checkMessageFieldSuffix condition parameter suffix
    (← resolveMessageReference model profile condition parameter entity keyHead)

/-- Check one name-position parameter: its events, then its form's own check, then a fault the parser
meets at the end it requires. -/
private def checkMessageName (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (parameter : String)
    (decoded : DecodedMessageName) :
    Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition) := do
  runMessageEvents model profile condition parameter false decoded.events
  let part ← match decoded.form with
    | none => throw (.invalidParameter parameter)
    | some (.field entity suffix key) =>
        checkMessageField model profile condition parameter entity suffix key
    | some (.formPointer entity pointer) =>
        -- The one field form the Kernel admits on a field the condition never references, measured on
        -- six admitted spellings against the same model's own membership refusals.
        match ← resolveMessageSpec model profile condition parameter entity with
        | some (.inl entity) =>
            pure (.formPointer {
              parameter
              reference := entity.reference
              declaration := entity.declaration
              pointer
              resolved := entity.resolved })
        | some (.inr group) => throw (.groupInFormPointer parameter group)
        | none => throw (.ruleGroupUnresolved parameter)
    | some (.baseYear offset) =>
        match hDeclared : model.baseYear with
        | none => throw .noBaseYear
        | some base =>
            pure (.baseYear offset (base + offset) (by rw [hDeclared, Int.add_sub_cancel]))
    | some (.indexField entity suffix) =>
        -- The service compares the authored entity spelling with a short name, rather than
        -- resolving it as a field path (FullChecks_ErrorTextParameterParser.checkIndexFieldRef).
        let name := match entity with
          | .path { base := .relative 0, groups := [], turningPoint := none, field } =>
              if field.quoted then "'" ++ field.text ++ "'" else field.text
          | _ => ""
        match checkMessageIndex condition name suffix with
        | .ok access => pure (.indexField access)
        | .error error => throw (.indexParameter parameter error)
  match decoded.trailing with
  | some fault => throw (.parameterSyntax parameter fault)
  | none => pure part

/-- Check one parameter body on its own, as the Kernel's service parses each with a parser of its own.
The position marker selects the grammar: a body whose first token is `#` is the group position. -/
private def checkMessageParameter (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (parameter : String) :
    Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition) :=
  let keywords := profile.parameterKeywords
  match ParameterToken.ofParameter keywords parameter with
  | .hash :: rest =>
      match decodeMessageGroupTokens keywords rest with
      | .error (.syntax fault) => .error (.parameterSyntax parameter fault)
      | .error (.retired terminal) => .error (.retiredGroupTerminal parameter terminal)
      | .ok (authored, remainder) =>
          let keyCheck := match remainder with
            | .keyed events key _ => do
                runMessageEvents model profile condition parameter true events
                match key with
                | none => pure none
                | some (.literal text) => pure (some (.literal (.text text) (some text)))
                | some (.entity spec) => resolveMessageGroupKeyEntity model profile condition parameter spec
            | _ => .ok none
          .group <$> checkMessageGroup condition parameter authored remainder keyCheck
  | tokens =>
      checkMessageName model profile condition parameter
        (decodeMessageName keywords profile.nameTerminals tokens)

/-- Every part of a balanced template, each parameter checked independently. -/
private def checkMessageSegments (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) :
    List String →
      List (Except ValidationMessageTemplateError (CheckedValidationMessagePart model condition))
  | [] => []
  | [text] => if text.isEmpty then [] else [.ok (.text text)]
  | text :: parameter :: rest =>
      (if text.isEmpty then [] else [.ok (.text text)]) ++
        [if parameter.isEmpty then .ok (.text "$")
          else checkMessageParameter model profile condition parameter] ++
        checkMessageSegments model profile condition rest

/-- Every refusal a rule message's template draws: the template-level gate that stops it, or one
refusal for each parameter that fails, in written order. The Kernel's service parses each parameter on
its own and reports each one's first failure, so `$Nope$ and $Nope2$` draws two
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). The codeless
repertoire finding is not among them; `withMessageRepertoire` keeps it beside the first. -/
def validationMessageTemplateRefusals (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (source : String) :
    List ValidationMessageTemplateError :=
  match validateMessageTemplateSource source with
  | .error error => [error]
  | .ok segments =>
      (checkMessageSegments model profile condition segments).filterMap fun
        | .error error => some error
        | .ok _ => none

/-- Check a rule message's template. A refused template reports its first refusal in written order;
`validationMessageTemplateRefusals` lists the rest. -/
def elaborateValidationMessageTemplate (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (source : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) :=
  let checked : Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) := do
    let segments ← validateMessageTemplateSource source
    pure { source, parts := ← (checkMessageSegments model profile condition segments).mapM id }
  withMessageRepertoire source checked

/-- What the caller supplies for substitution. Values and stored tokens are read at a cell, because a
parameter renders the row it reads: the firing row, an enclosing row, a parallel partner or a keyed
selection ([checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15)). -/
structure ValidationMessageInputs where
  fieldName : FieldId → MessageNameInput
  fieldValue : CellAddr → MessageValueInput
  /-- The cell's current stored token. The category mapping is applied by the checked part, not by
  the caller, because the mapping is the declaration's and is measured. -/
  fieldStoredToken : CellAddr → Option String
  /-- What a form pointer renders. Caller-supplied because it is unmeasured; the field and which of
  the two terminals was written are both passed, so a caller need not re-derive either. -/
  formPointer : FieldId → MessageFormPointer → String

/-- Render already-selected inputs. Repeatable callers must supply the resolved group coordinate and
each read reference's row path; `toRenderPlanAt` owns the addressed selection before this final
substitution. -/
def CheckedValidationMessagePart.toRenderPartWithGroupIndex
    (inputs : ValidationMessageInputs) (groupIndex : GroupPath → Nat)
    (rowPath : CheckedValidationMessageReference model condition → List Nat) :
    CheckedValidationMessagePart model condition → MessageRenderPart
  | .text value => .text value
  | .fieldName reference => .fieldName (inputs.fieldName reference.declaration.id)
  | .fieldValue reference =>
      .fieldValue (inputs.fieldValue { field := reference.declaration.id, path := rowPath reference })
  | .fieldCategory access =>
      .fieldCategory {
        categoryToken :=
          (inputs.fieldStoredToken
              { field := access.reference.declaration.id, path := rowPath access.reference }).bind
            (access.projection.declaration.categoryTokenFor? access.category) }
  | .baseYear _ year _ => .baseYear year
  | .group access => .group { repetitionIndex := groupIndex access.group }
  | .indexField access =>
      match access.suffix with
      | .value => .fieldValue {
          displayValue := (inputs.fieldValue { field := access.binding.declaration.id, path := [] }).displayValue
          defaultDisplay := "" }
      | .category name => .fieldCategory {
          categoryToken := do
            let source ← access.binding.declaration.enumeration
            let checked ← (elaborateEnumeration source).toOption
            let stored ← inputs.fieldStoredToken { field := access.binding.declaration.id, path := [] }
            checked.categoryTokenFor? name stored }
      | .none => .text ""
  | .formPointer access =>
      .formPointer { text := inputs.formPointer access.declaration.id access.pointer }

def CheckedValidationMessagePart.toRenderPart
    {condition : CheckedFlatCondition model}
    (inputs : ValidationMessageInputs)
    (part : CheckedValidationMessagePart model condition) : MessageRenderPart :=
  part.toRenderPartWithGroupIndex inputs (fun _ => 1) (fun _ => [])

def CheckedValidationMessageTemplate.toRenderPlan
    {condition : CheckedFlatCondition model}
    (template : CheckedValidationMessageTemplate model condition)
    (inputs : ValidationMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

end A12Kernel
