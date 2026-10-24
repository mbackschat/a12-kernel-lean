import A12Kernel.Elaboration.ValidationCondition.StaticIteration

/-! # Validation-condition iteration legality and addressed execution -/

namespace A12Kernel

namespace DecodedNumericLiteral

/-- Compatibility specialization for the established iteration-legality consumer. -/
def iterationHostInt32? := javaRoundedInt32?

end DecodedNumericLiteral

/-- Whether the ordinary iteration guard skips this level: Kernel
`IterationNotValidVisitor.getIterationLevels` leaves out a level whose group repeats exactly twice and
declares an index field, on A12 models, so a negative read there needs no positive guard; a level
nested in a judged one stays skipped while its parent is judged
([capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04)
rows `e01`–`e11`, `g04`). H models, whose two-row levels need no index field, are not modelled. -/
def FlatModel.iterationGuardSkips (model : FlatModel) (level : RepeatableLevel) : Bool :=
  (model.repeatableGroupAtLevel? level).any fun group =>
    group.repeatability == some 2 && group.indexField.isSome

namespace ValidationCondition

/-- A selected entity still references its enclosing parent and dynamic key scopes. The selected level itself is supplied by lookup (`SemanticIndex.bindingScopes`); the Kernel's `IterationNotValidVisitor.isIteration(IEntityId)` also follows the key's iteration. -/
private def selectedEntityGuardScope
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    List RepeatableLevel :=
  (match source with | .inl source => source.bindingScopes | .inr source => source.bindingScopes).flatten

/-- A fully starred operand has a known empty binding scope. Keeping that empty entry is
necessary for the mixed-reference refusal in the retained iteration-domain binding matrix. -/
private def numberEntityOperandReferenceScope :
    CheckedNumberEntityOperand model → List RepeatableLevel
  | .field source => source.declaration.repeatableScope
  | .selected source => selectedEntityGuardScope source.source
  | .star checked => checked.source.bindingScope
  | .starHaving checked => checked.source.source.bindingScope
  | .group slot => slot.source.bindingScope

private def numberEntityReferenceScopes
    (source : CheckedNumberEntitySource model) : List (List RepeatableLevel) :=
  source.operands.map numberEntityOperandReferenceScope

private def tokenEntityOperandReferenceScope :
    CheckedTokenEntityOperand model → List RepeatableLevel
  | .field source => source.declaration.repeatableScope
  | .selected source => selectedEntityGuardScope source.source
  | .star checked => checked.source.bindingScope
  | .group slot => slot.source.bindingScope

private def tokenEntityReferenceScopes
    (source : CheckedTokenEntitySource model) : List (List RepeatableLevel) :=
  source.operands.map tokenEntityOperandReferenceScope

private def booleanValueCountOperandReferenceScope :
    CheckedBooleanValueCountOperand model expected → List RepeatableLevel
  | .field source => source.declaration.repeatableScope
  | .selected source => selectedEntityGuardScope source.source
  | .star source => source.source.bindingScope
  | .group slot => slot.source.bindingScope

private def booleanValueCountReferenceScopes
    (source : CheckedBooleanValueCountSource model) : List (List RepeatableLevel) :=
  source.operands.map booleanValueCountOperandReferenceScope

private def productReferenceScopes :
    CheckedNumericProductAggregate model → List (List RepeatableLevel)
  | .selected source => [source.left.source.bindingScopes.flatten,
      source.right.source.bindingScopes.flatten]
  | .row source => [source.left.source.bindingScope, source.right.source.bindingScope]

/-- Whether a count compared with a positive literal leaves its iteration unguarded: an upper bound
or an inequality, read from the count's side. -/
def positiveCountThresholdIsUnguarded
    (entityOnLeft : Bool) : NumericValidationOp → Bool
  | .tolerance _ => true
  | .ordinary comparison =>
      if entityOnLeft then
        match comparison with
        | .less | .lessEqual | .notEqual => true
        | .equal | .greater | .greaterEqual => false
      else
        match comparison with
        | .greater | .greaterEqual | .notEqual => true
        | .equal | .less | .lessEqual => false

/-- What the Kernel's comparison visitor reads off one operand's top operation
(`IterationNotValidVisitor.visit(IComparisonCondition)`): a count lets its leaf fire on an unfilled
row below a positive constant, a value operation beside a zero, and an operation mixing iterated
and other reads beside any number constant. The Kernel's parse tree keeps no bracket, so grouping is
transparent ([capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04)
rows `u07`, `u27`, `u30`). -/
private structure ComparisonOperandProfile where
  /-- Each entity reference's binding scope, or `none` where this carrier keeps no per-reference
  scope; a reference iterates exactly the levels its scope contains. -/
  references : Option (List (List RepeatableLevel)) := some []
  belowPositive : Bool := false
  equalsZero : Bool := false
  mixedAgainstConstant : Bool := false
  /-- The scope of each `CurrentRepetition` read, which refuses at every level it iterates. -/
  currentRepetitions : List (List RepeatableLevel) := []
  /-- The host-converted value when the operand is a number constant, and `some none` for a
  constant outside the checked decimal shape, whose conversion is not modelled. -/
  constant? : Option (Option Int) := none

private def ComparisonOperandProfile.combine (profiles : List ComparisonOperandProfile) :
    ComparisonOperandProfile :=
  { references := profiles.foldr (fun profile all => do pure ((← profile.references) ++ (← all))) (some [])
    currentRepetitions := profiles.flatMap (·.currentRepetitions) }

private def ordinaryAtomProfile (model : FlatModel) : NumericValidationAtom → ComparisonOperandProfile
  | .boundCurrentRepetition repetition =>
      { references := some [repetition.scope], currentRepetitions := [repetition.scope] }
  | .filledGroupCount groups =>
      { references := some (groups.map (·.boundRepeatableScope)), belowPositive := true,
        mixedAgainstConstant := true }
  | .aggregate op _ =>
      { references := none, belowPositive := op == .distinctCount,
        equalsZero := op != .distinctCount, mixedAgainstConstant := true }
  | source =>
      match ordinaryNumericAtomFieldDeclarations? model source with
      | some declarations =>
          { references := some (declarations.map (·.repeatableScope)), equalsZero := true }
      | none => {}

private def entityListProfile (references : List (List RepeatableLevel))
    (belowPositive equalsZero mixedAgainstConstant : Bool) : ComparisonOperandProfile :=
  { references := some references, belowPositive, equalsZero, mixedAgainstConstant }

private def atomProfile : OrderedNumericValidationAtom model → ComparisonOperandProfile
  | .ordinary source => ordinaryAtomProfile model source
  -- A selected read and a temporal operation are value operations whose per-reference scopes this
  -- carrier does not keep, so a check that needs them stays unjudged.
  | .indexed _ | .indexedString _ | .temporalExpression _ => { references := none, equalsZero := true }
  | .firstFilled source => entityListProfile (numberEntityReferenceScopes source) false true true
  | .valueCount _ source => entityListProfile (numberEntityReferenceScopes source) true true true
  | .tokenValueCount source => entityListProfile (tokenEntityReferenceScopes source.source) true true true
  | .booleanValueCount source => entityListProfile (booleanValueCountReferenceScopes source) true true true
  | .aggregate op source =>
      entityListProfile (numberEntityReferenceScopes source)
        (op == .distinctCount) (op != .distinctCount) true
  -- The Kernel exempts `SumOfProducts` from the mixed-read refusal and keeps its zero refusal.
  | .sumOfProducts source => entityListProfile (productReferenceScopes source) false true false
  | .filledGroupCountMixed operands => entityListProfile (operands.map (·.bindingScope)) true false true
  | .filledFieldCount source => entityListProfile (source.operands.map (·.bindingScope)) true false true
  | .tokenDistinctCount source => entityListProfile (tokenEntityReferenceScopes source) true false true
  | .temporalDistinctCount _ => { references := none, belowPositive := true, mixedAgainstConstant := true }

/-- An operand list (`Min`/`Max`, `Abs`, rounding) is a value operation over every read beneath it;
arithmetic is none of the visitor's operation kinds, so it carries no check of its own. -/
private def operandProfile : AuthoredNumericExpr (OrderedNumericValidationAtom model) →
    ComparisonOperandProfile
  | .atom atom => atomProfile atom
  | .literal literal => { constant? := some literal.iterationHostInt32? }
  | .group body => operandProfile body
  | .abs body | .round _ _ body | .extremumCall _ body =>
      { ComparisonOperandProfile.combine [operandProfile body] with
        equalsZero := true, mixedAgainstConstant := true }
  | .extremum _ left right =>
      { ComparisonOperandProfile.combine [operandProfile left, operandProfile right] with
        equalsZero := true, mixedAgainstConstant := true }
  | .binary _ left right | .power left right =>
      ComparisonOperandProfile.combine [operandProfile left, operandProfile right]

/-- Whether every read of an operand iterates `level`; `none` where the operand keeps no
per-reference scopes. -/
private def ComparisonOperandProfile.allIterate (profile : ComparisonOperandProfile)
    (level : RepeatableLevel) : Option Bool :=
  profile.references.map fun scopes => scopes.any (·.contains level) && scopes.all (·.contains level)

/-- Whether an operand's reads mix ones iterating `level` with others; `none` as above. -/
private def ComparisonOperandProfile.mixesIterated (profile : ComparisonOperandProfile)
    (level : RepeatableLevel) : Option Bool :=
  profile.references.map fun scopes => scopes.any (·.contains level) && scopes.any (!·.contains level)

/-- `some true` when one of the visitor's checks lets the comparison fire on an unfilled row, `none`
when a check depends on a scope or constant this carrier does not keep. A non-constant operand
reads as no constant, as the Kernel reads it as `-1`. -/
private def comparisonFiresUnfilled (level : RepeatableLevel) (op : NumericValidationOp)
    (left right : ComparisonOperandProfile) : Option Bool :=
  let belowPositive (side other : ComparisonOperandProfile) (sideOnLeft : Bool) : Option Bool :=
    if !side.belowPositive then some false else
      match other.constant? with
      | some (some value) =>
          if 0 < value && positiveCountThresholdIsUnguarded sideOnLeft op then side.allIterate level
          else some false
      | some none => none
      | none => some false
  -- The visitor reads the zero check off the first value operand only.
  let equalsZero : Option Bool :=
    let pair := if left.equalsZero then some (left, right) else if right.equalsZero then some (right, left) else none
    match pair, op.zeroSensitiveIteration with
    | some (side, other), true =>
        match other.constant? with
        | some (some 0) => side.allIterate level
        | some (some _) | none => some false
        | some none => none
    | _, _ => some false
  let mixedAgainstConstant (side other : ComparisonOperandProfile) : Option Bool :=
    if side.mixedAgainstConstant && other.constant?.isSome then side.mixesIterated level else some false
  let checks := [belowPositive left right true, belowPositive right left false, equalsZero,
    mixedAgainstConstant left right, mixedAgainstConstant right left]
  if checks.any (· == some true) then some true
  else if checks.any (·.isNone) then none
  else some false

private def orderedNumericGuardAt (level : RepeatableLevel)
    (comparison : OrderedNumericComparison model) : IterationGuardStatus :=
  match orderedNumericComparisonIterationScope comparison with
  | .error _ => .unclassified
  | .ok none => .noReference
  | .ok (some scope) =>
      let left := operandProfile comparison.left
      let right := operandProfile comparison.right
      -- The visitor's own reference test skips filter bodies (`AnalyseService.isIteration` with
      -- `useFilterCondition = false`), so a `$` read inside a `Having` lists the level without
      -- referencing it; the per-reference scopes leave those reads out. A carrier keeping no such
      -- scopes falls back to the whole iteration scope, which still counts a `$` read of its own.
      let references := match (ComparisonOperandProfile.combine [left, right]).references with
        | some scopes => scopes.any (·.contains level)
        | none => scope.contains level
      if !references then .noReference else
        if (left.currentRepetitions ++ right.currentRepetitions).any (·.contains level) then .unguarded
        else match comparisonFiresUnfilled level comparison.op left right with
          | some true => .unguarded
          | some false => .guarded
          | none => .unclassified

/-- Kernel `IterationNotValidVisitor.visit(IEntityListAndValueListCondition)`: `No…` refuses whenever
it iterates, `NotAll…` when a subject reads outside the iteration, and `AtLeastOne…` when a subject
and a value also do, a literal value counting as one. -/
private def valueListGuardAt (level : RepeatableLevel) (source : CheckedValueListCondition model) :
    IterationGuardStatus :=
  let (subjects, values, literals) := match source with
    | .number source => (numberEntityReferenceScopes source.fields, numberEntityReferenceScopes source.values, false)
    | .token source => (tokenEntityReferenceScopes source.fields, tokenEntityReferenceScopes source.values, false)
    | .literals source => (tokenEntityReferenceScopes source.fields, [], true)
  let outside (scopes : List (List RepeatableLevel)) := scopes.any (!·.contains level)
  -- As for a comparison, a `$` read inside a filter does not reference the level.
  if !(subjects ++ values).flatten.contains level then .noReference
  else match source.quantifier with
    | .no => .unguarded
    | .notAll => if outside subjects then .unguarded else .guarded
    | .atLeastOne => if outside subjects && (outside values || literals) then .unguarded else .guarded

def ResolvedGroupListOperands.iterationGuardAt
    (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) : IterationGuardStatus :=
  let references := operands.map fun operand =>
    match ResolvedGroupListOperand.iterationScope operand with
    | some scope => scope.contains level
    | none => false
  if !references.any id then
    .noReference
  else
    match operator with
    | .noGroupFilled => .unguarded
    | .atLeastOneGroupFilled =>
        if references.all id then .guarded else .unguarded
    | .allGroupsFilled | .notAllGroupsFilled
    | .groupsNotCollectivelyFilled => .unclassified

/-- Static wildcard multiplicity is declared capacity, independent of the filter's runtime selection
(IterationNotValidVisitor's entity-list gate; the H10 iteration-guard matrix). Captured reads bind the
rule's row but do not turn its selected wildcard operand into an ordinary row read. -/
private def starIterationExtent? (source : CheckedStarFieldPath model) :
    Option (List RepeatableLevel × Nat) :=
  (model.declarationSlots? source.path.firstStar source.declaration).map (source.bindingScope, ·)

/-- A group operand supplies, per field it expands to, the row combinations its repeatable levels
below the operand's own depth reach, as a wildcard does below its star: a starred repeatable group
weighs its own level too (`uniqueness-iteration-guard-2026-10-13` row `GDEEPSTAR`). -/
private def groupIterationExtents? (model : FlatModel) (source : CheckedEntityGroupSource model) :
    Option (List (List RepeatableLevel × Nat)) :=
  (model.groupSubtreeFields source.groupPath).mapM fun declaration =>
    (model.declarationSlots? source.boundLevelCount declaration).map (declaration.repeatableScope, ·)

/-- A semantic-index selection reads one row of its keyed level; each selected field supplies the
row combinations of its repeatable levels below that row. Its scope is the parent and key levels it
reads at the rule's row plus those lower levels, never the selected level, so a constant selection
of the iterated group's own field is an independent slot too
([capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04)
rows `v4`–`v6`, `v15`, `v16`). -/
private def selectedIterationExtents?
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Option (List (List RepeatableLevel × Nat)) :=
  let (enclosing, declarations) := match source with
    | .inl source => ((model.repeatableScopeForGroupPath source.group.path).length, [source.targetDeclaration])
    | .inr source =>
        ((model.repeatableScopeForGroupPath source.selection.group.path).length, source.declarations)
  declarations.mapM fun declaration =>
    (model.declarationSlots? enclosing declaration).map
      (selectedEntityGuardScope source ++ declaration.repeatableScope.drop enclosing, ·)

/-- A selection weighs as in the uniqueness guard, one slot per row below its selected row, so a
constant selection of a row's own field is one independent slot
([capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04)
rows `s4`, `s5`). -/
private def fieldFillIterationExtents? (source : CheckedFieldFillList model) :
    Option (List (List RepeatableLevel × Nat)) :=
  (·.flatten) <$> source.operands.mapM fun
    | .field declaration => some [(declaration.repeatableScope, 1)]
    | .star source => (starIterationExtent? source.source).map ([·])
    | .indexed source => selectedIterationExtents? (.inl source)
    | .keyed source => selectedIterationExtents? (.inr source)
    -- A group weighs the fields it reads, as on the uniqueness carrier, so `NoFieldFilled(RuleGroup)`
    -- at the row is unguarded (capture `rulegroup-field-fill-2026-10-24`, row `ungnone`).
    | .group source => groupIterationExtents? model source.source

/-- Every overload weighs its operands alike: direct fields, wildcards and selections as for field
fill, and groups by the fields they read (`uniqueness-iteration-guard-2026-10-13`). -/
private def uniquenessIterationExtents? : CheckedValuesNotUniqueCondition model →
    Option (List (List RepeatableLevel × Nat))
  | .number source => (·.flatten) <$> source.operands.mapM fun
      | .field source => some [(source.declaration.repeatableScope, 1)]
      | .star source => (starIterationExtent? source.source).map ([·])
      | .starHaving source => (starIterationExtent? source.source.source).map ([·])
      | .selected source => selectedIterationExtents? source.source
      | .group source => groupIterationExtents? model source.source
  | .token source => (·.flatten) <$> source.source.operands.mapM fun
      | .field source => some [(source.declaration.repeatableScope, 1)]
      | .star source => (starIterationExtent? source.source).map ([·])
      | .selected source => selectedIterationExtents? source.source
      | .group source => groupIterationExtents? model source.source
  | .temporal source => (·.flatten) <$> source.operands.mapM fun
      | .field source => some [(source.declaration.repeatableScope, 1)]
      | .star path _ _ => (starIterationExtent? path).map ([·])
      | .selected source _ => selectedIterationExtents? source.source
      | .group source => groupIterationExtents? model source.source

private def independentIterationSlots (level : RepeatableLevel)
    (extents : List (List RepeatableLevel × Nat)) : Nat :=
  (extents.map fun (scope, capacity) => if scope.contains level then 0 else capacity).sum

private def fieldFillIterationGuardAt (level : RepeatableLevel) (operator : FieldFillQuantifier)
    (source : CheckedFieldFillList model) : IterationGuardStatus :=
  if !source.bindingScope.contains level then .noReference
  else match fieldFillIterationExtents? source with
    | none => .unclassified
    | some extents =>
        let independent := independentIterationSlots level extents
        let violatesGuard : Bool := match operator with
          | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled =>
              extents.any fun (scope, _) => scope.contains level
          | .atLeastOneFieldFilled | .fieldsNotCollectivelyFilled => 0 < independent
          | .moreThanOneFieldFilled => 1 < independent
          | .allFieldsFilled =>
              match source.operands with
              | [.field _] => 0 < independent
              | _ => false
        if violatesGuard then .unguarded else .guarded

private def uniquenessIterationGuardAt (level : RepeatableLevel)
    (source : CheckedValuesNotUniqueCondition model) : IterationGuardStatus :=
  if !((ordinaryIterationScope (.leaf (.valuesNotUnique source))).toOption.bind id).any (·.contains level) then .noReference
  else match uniquenessIterationExtents? source with
    | none => .unclassified
    | some extents =>
        if 1 < independentIterationSlots level extents then .unguarded else .guarded

/-- One flat leaf's guard, given which fields iterate: a comparison guards when any of its fields
does. Scalar membership's subject guards either polarity; without it, Included needs every member
to iterate and NotIncluded is unguarded (Kernel IterationNotValidVisitor.visit(IValueListCondition)).
The ordinary and parallel carriers share this classification. -/
def _root_.A12Kernel.FlatConditionLeaf.iterationGuard (iterates : FieldId → Bool) :
    FlatConditionLeaf → IterationGuardStatus
  | .compare comparison =>
      if comparison.fields.any (iterates ·.id) then .guarded else .noReference
  | .numberValueList quantifier subjects members .membership =>
      membership quantifier (subjects.map (·.id)) (members.operands.map (·.id))
  | .tokenValueList quantifier subjects members .membership =>
      membership quantifier (subjects.map (·.field.id)) (members.operands.map (·.field.id))
  | _ => .noReference
where
  membership (quantifier : ValueListQuantifier) (subjects members : List FieldId) : IterationGuardStatus :=
    if !(subjects ++ members).any iterates then .noReference
    else if subjects.any iterates then .guarded
    else if quantifier == .atLeastOne && members.all iterates then .guarded else .unguarded

private def ValidationConditionLeaf.iterationGuardAt
    (level : RepeatableLevel) :
    ValidationConditionLeaf model → IterationGuardStatus
  | .flat condition => condition.iterationGuard fun field => (model.fieldRepeatableScope field).contains level
  | .numeric _ _ | .guardedRootCurrentRepetition _ _ _
  | .customCondition _ => .noReference
  | .customFieldValidity leaf =>
      if leaf.operand.declaration.repeatableScope.contains level then .guarded else .noReference
  | .indexedStringPattern leaf =>
      if leaf.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .indexedCustomFieldValidity leaf =>
      if leaf.source.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .constructedDateValidity operation source =>
      if source.scalarBindingScopes.any (·.contains level) then
        match operation with
        | .valid => .guarded
        | .invalid => .unguarded
      else .noReference
  | .stringPattern leaf =>
      if (model.fieldRepeatableScope leaf.condition.field.id).contains level then .guarded else .noReference
  | .scalarTemporal comparison =>
      if comparison.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .guardedRepeatableCurrentRepetition guard _ _ =>
      if guard.repeatableScope.contains level then .guarded else .noReference
  | .groupList operator operands =>
      ResolvedGroupListOperands.iterationGuardAt operator operands level
  | .fieldFill operator source => fieldFillIterationGuardAt level operator source
  -- A String, token or first-filled comparison has no number constant or count for the visitor's
  -- comparison checks to read, so it guards every level it iterates.
  | .stringExpression comparison =>
      if comparison.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .firstFilledComparison comparison =>
      if comparison.bindingScopes.flatten.contains level then .guarded else .noReference
  | .tokenComparison comparison =>
      if comparison.bindingScopes.flatten.contains level then .guarded else .noReference
  | .valueList source => valueListGuardAt level source
  | .valuesNotUnique source => uniquenessIterationGuardAt level source
  | .orderedNumeric _ comparison => orderedNumericGuardAt level comparison
  | .groupPresence operator reference =>
      if (model.repeatableScopeForGroupPath reference.path).contains level then
        match operator with
        | .filled => .guarded
        | .notFilled => .unguarded
      else
        .noReference
  -- A selection references its parent's and its key's rows, not the row it selects, with a
  -- presence leaf's polarity, for a field and a group alike
  -- ([capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04)
  -- rows `s1`, `s6`, `d6`, `v1`–`v3`, `v7`–`v11`, `v17`, `v18`).
  | .indexedFieldPresence operator source =>
      if (selectedEntityGuardScope (.inl source)).contains level then
        match operator with
        | .filled => .guarded
        | .notFilled => .unguarded
      else .noReference
  | .keyedGroupPresence operator source =>
      if (selectedEntityGuardScope (.inr source)).contains level then
        match operator with
        | .filled => .guarded
        | .notFilled => .unguarded
      else .noReference
  | .repeatableFieldPresence operator declaration =>
      if declaration.repeatableScope.contains level then
        match operator with
        | .filled => .guarded
        | .notFilled => .unguarded
      else
        .noReference
  | .repetitionNotUnique source =>
      if (source.topology.path.axes.map (·.level)).contains level then
        .guarded
      else
        .noReference
  | .iteratedDateRange condition =>
      -- A value comparison guards its own level at every polarity. The Kernel refuses a negated
      -- *presence* leaf at an iterated level, and the same model admits `==`, `!=`, and the order
      -- operators on a repeatable operand, so polarity is not this leaf's question.
      if condition.bindingScopes.any (·.contains level) then
        .guarded
      else
        .noReference

def iterationGuardStatusAt (condition : ValidationCondition model)
    (level : RepeatableLevel) : IterationGuardStatus :=
  condition.iterationGuardStatus
    (ValidationConditionLeaf.iterationGuardAt level)

private def iterationLegalityForLevels
    (condition : ValidationCondition model) :
    List RepeatableLevel → IterationLegality
  | [] => .legal
  | level :: remaining =>
      match condition.iterationGuardStatusAt level with
      | .guarded => iterationLegalityForLevels condition remaining
      | .unguarded => .invalid level
      | .noReference | .unclassified => .insufficient level

/-- Analyze the levels already derived from the complete checked condition, outermost first, except the
ones the guard skips. Scope incompatibility remains the existing separate assembly error. -/
def iterationLegality (condition : ValidationCondition model) :
    Except RuleIterationScopeError IterationLegality := do
  match ← condition.ordinaryIterationScope with
  | none => pure .legal
  | some scope => pure (iterationLegalityForLevels condition (scope.filter (!model.iterationGuardSkips ·)))

/-- Ordinary repeatable Number declarations retained by one ordered expression in authored order. -/
private def ordinaryNumericAtomRepeatableFields
    (model : FlatModel) :
    OrderedNumericValidationAtom model → List FlatFieldDecl
  | .ordinary source =>
      match ordinaryNumericAtomFieldDeclarations? model source with
      | none => []
      | some declarations =>
          declarations.filter fun declaration =>
            !declaration.repeatableScope.isEmpty
  | _ => []

private def authoredNumericRepeatableFields
    (fieldsOf : Atom → List FlatFieldDecl) :
    AuthoredNumericExpr Atom → List FlatFieldDecl
  | .atom atom => fieldsOf atom
  | .literal _ => []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      authoredNumericRepeatableFields fieldsOf body
  | .binary _ left right | .power left right | .extremum _ left right =>
      authoredNumericRepeatableFields fieldsOf left ++
        authoredNumericRepeatableFields fieldsOf right

/-- Ordinary repeatable field declarations in authored tree order. Whole-rule checked-document execution resolves these exact cells before evaluation so a structural address failure cannot be collapsed into semantic UNKNOWN. -/
def ordinaryRepeatableFields (condition : ValidationCondition model) :
    List FlatFieldDecl :=
  match condition with
  | .leaf (.flat condition) => model.fields.filter fun field =>
      condition.referencesField field.id && !field.repeatableScope.isEmpty
  | .leaf (.repeatableFieldPresence _ declaration) => [declaration]
  | .leaf (.constructedDateValidity _ source) =>
      source.scalarBoundFieldIds.filterMap fun field =>
        (model.lookupUniqueId field).toOption.filter (fun declaration => !declaration.repeatableScope.isEmpty)
  | .leaf (.stringExpression comparison) =>
      comparison.boundDeclarations.filter fun field => !field.repeatableScope.isEmpty
  | .leaf (.scalarTemporal comparison) =>
      (comparison.left.boundFieldIds ++ comparison.right.boundFieldIds).filterMap fun field =>
        (model.lookupUniqueId field).toOption.filter (fun declaration => !declaration.repeatableScope.isEmpty)
  | .leaf (.orderedNumeric _ comparison) =>
      authoredNumericRepeatableFields
          (ordinaryNumericAtomRepeatableFields model) comparison.left ++
        authoredNumericRepeatableFields
          (ordinaryNumericAtomRepeatableFields model) comparison.right
  | .leaf (.repetitionNotUnique source) =>
      source.keys.map fun key => key.source.declaration
  | .leaf (.guardedRepeatableCurrentRepetition guard _ _) => [guard]
  | .leaf (.iteratedDateRange condition) =>
      condition.repeatableDeclarations
  | .leaf _ => []
  | .and left right | .or left right =>
      ordinaryRepeatableFields left ++ ordinaryRepeatableFields right

/-- Whether every leaf can consume the complete environment selected by ordinary nonparallel rule iteration. Specialized star sources remain with their family owners. -/
def supportsOrdinaryIteration
    (condition : ValidationCondition model) : Bool :=
  condition.allLeaves fun
    | .flat _ | .groupPresence _ _ | .groupList _ _
    | .keyedGroupPresence _ _ | .indexedFieldPresence _ _ | .repeatableFieldPresence _ _
    | .guardedRootCurrentRepetition _ _ _ => true
    | .guardedRepeatableCurrentRepetition _ _ _ => true
    | .iteratedDateRange _ => true
    | .orderedNumeric .sameGroupAddressed _ => true
    | .repetitionNotUnique _ => true
    | .customCondition _ | .constructedDateValidity _ _ | .customFieldValidity _ | .indexedCustomFieldValidity _ => true
    | .stringPattern _ | .indexedStringPattern _ => true
    | .stringExpression _ | .scalarTemporal _ | .firstFilledComparison _ | .tokenComparison _ | .fieldFill _ _ | .valueList _ | .valuesNotUnique _ => true
    | _ => false

/-- Discover a filtered source across the complete checked connective tree. Unlike verdict evaluation, this static traversal never short-circuits on a decisive branch. -/
def hasHaving (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.hasHaving

/-- Public execution-mode query for checked consumers. A true result requires the full addressed evaluator; choosing the scalar route is an explicit context error rather than semantic UNKNOWN. -/
def requiresAddressedValidation
    (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.requiresAddressedValidation

def wellFormedBool (condition : ValidationCondition model)
    (rowGroup : GroupPath) (declaringGroup : GroupPath := rowGroup) : Bool :=
  condition.repetitionNotUniqueSources.length < 2 &&
    condition.allLeaves fun leaf => leaf.wellFormedBool rowGroup declaringGroup

/-- Reached temporal runtime failure aborts the enclosing rule, rather than entering the
truth algebra as an ordinary fired leaf (temporal review grid, 2026-10-03). Structural failures
remain in the caller's error domain. -/
def evalWithTemporalResult (condition : ValidationCondition model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance)
    (evaluate : ValidationConditionLeaf model → Except Error Verdict)
    (onTemporalUnavailable : Except Error Verdict := .ok .unknown)
    (temporalFields : CheckedScalarTemporalComparison model → Except Error FlatContext :=
      fun _ => pure context.fields)
    (onTemporalValueFailure : ScalarTemporalEvaluationFault → Except Error Verdict :=
      fun _ => .ok (.fired .value))
    (numericResult : OrderedNumericComparison model → Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
      fun comparison => (comparison.evalSelectedResult context isRelevant).mapError Sum.inr)
    (leafRuntimeFault? : Error → Option ScalarTemporalEvaluationFault := fun _ => none)
    (firstFilledResult : CheckedFirstFilledComparison model → Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
      fun _ => pure .unknown)
    (customResult : String → Except Error Verdict := fun name =>
      pure ((context.customResult name).toOption.getD .unknown))
    (temporalFiltered : FilteredShiftAmountReader model := .unavailable)
    (temporalAddressed : CheckedScalarTemporalComparison model → Except Error (Option ComputationFillContext × Env) :=
      fun _ => pure (none, []))
    (temporalPartialResult? : ValidationConditionLeaf model → Option (Except (Sum Error ScalarTemporalEvaluationFault) Verdict) :=
      fun _ => none) :
    Except Error Verdict :=
  let readLeaf : ValidationConditionLeaf model → Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
    fun leaf => match temporalPartialResult? leaf with
      | some result => result
      | none => match leaf with
        | .customCondition name => (customResult name.value).mapError Sum.inl
        | .firstFilledComparison comparison => firstFilledResult comparison
        | .scalarTemporal comparison =>
            if comparison.fieldIds.all isRelevant then do
              let fields ← (temporalFields comparison).mapError Sum.inl
              let (addressed, row) ← (temporalAddressed comparison).mapError Sum.inl
              (comparison.evalResult .validation fields addressed row (filtered := temporalFiltered)).mapError Sum.inr
            else pure .unknown
        | leaf@(.orderedNumeric _ comparison) =>
            if comparison.hasTemporalExpression then numericResult comparison
            else (evaluate leaf).mapError Sum.inl
        | leaf => (evaluate leaf).mapError Sum.inl
  let readLeaf := fun leaf => (readLeaf leaf).mapError fun
    | .inl error => match leafRuntimeFault? error with
        | some fault => .inr fault
        | none => .inl error
    | .inr fault => .inr fault
  let hasCustom := condition.anyLeaf fun | .customCondition _ => true | _ => false
  let result : Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
    if hasCustom then condition.evalObservedM
      (condition.anyLeaf ValidationConditionLeaf.requiresClassificationPass) readLeaf
    else match condition with
    | .leaf leaf => readLeaf leaf
    | _ => do
      let holds ← condition.evalBoolExcept fun leaf => do
        pure (match ← readLeaf leaf with | .fired _ => true | _ => false)
      if holds then
        if condition.anyLeaf ValidationConditionLeaf.requiresClassificationPass then
          condition.evalClassificationExcept readLeaf
        else condition.evalVerdictExcept readLeaf
      else
        -- Non-firing still retains the theory's UNKNOWN distinction. This projection cannot raise
        -- a runtime failure the generated Boolean pass has already skipped; context faults remain
        -- explicit. `CodeGenRuleDefinition.st` enters classification only after a true condition.
        condition.evalVerdictExcept fun leaf =>
          match readLeaf leaf with
          | .error (.inr .dateTimeLabelUnresolved) | .error (.inr .componentNumberInvalid)
          | .error (.inr (.addressing .typeValidityValueFailure))
          | .error (.inr (.addressing (.stringExpression .emptyPattern))) => .ok .unknown
          | result => result
  match result with
  | .ok verdict => .ok verdict
  | .error (.inl error) => .error error
  | .error (.inr fault@(.dateTimeLabelUnresolved))
  | .error (.inr fault@(.componentNumberInvalid))
  | .error (.inr fault@(.addressing .typeValidityValueFailure))
  | .error (.inr fault@(.addressing (.stringExpression .emptyPattern)))
  | .error (.inr fault@(.addressing (.customCondition (.missingRegistration _)))) => onTemporalValueFailure fault
  | .error (.inr .calendarUnavailable) | .error (.inr .indexedOperandNotSupported)
  | .error (.inr (.addressing _)) => onTemporalUnavailable

/-- Preserve a caught value failure until message emission; the verdict-only API below deliberately forgets its origin. -/
def evalSelectedResult (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance := fun _ => true) : Except ScalarTemporalEvaluationFault Verdict :=
  condition.evalWithTemporalResult context isRelevant
      (fun leaf => Except.ok (ε := ScalarTemporalEvaluationFault) (leaf.evalSelected context isRelevant))
      (onTemporalValueFailure := Except.error)
      (temporalPartialResult? := fun
        | .stringPattern leaf => some do
            leaf.condition.pattern.checkExecution.mapError
              (fun _ => .inr (.addressing (.stringExpression .emptyPattern)))
            pure (if isRelevant leaf.condition.field.id then leaf.condition.evalSelected context.fields else .unknown)
        | .customFieldValidity leaf => some do
            if !isRelevant leaf.operand.source then return .unknown
            (leaf.evalValidationObservation (observeCell .validation
              (context.fields.read leaf.operand.source))).mapError
                (fun _ => .inr (.addressing .typeValidityValueFailure))
        | _ => none)

/-- The scalar verdict view retains historical value-error polarity while message emitters consume the effectful result. -/
def evalSelected (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance := fun _ => true) : Verdict :=
  (condition.evalSelectedResult context isRelevant).toOption.getD (.fired .value)

/-- Apply the ordinary full-validation content gate to a mixed resolved tree. -/
def evalFull (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context
  else .notFired

/-- Bind only a reached temporal leaf to exact row cells; the row-binding grid separates this view from the scalar context without changing the temporal evaluator. -/
private def addressedTemporalFields (context : AddressedValidationEvaluationContext model)
    (comparison : CheckedScalarTemporalComparison model) : Except CheckedAddressingError FlatContext := do
  for scope in comparison.bindingScopes do
    discard <| (context.outer.pathForScope scope).mapError CheckedAddressingError.environment
  let fields := comparison.fieldIds.filter fun field =>
    (context.outer.pathForScope (model.fieldRepeatableScope field)).isOk
  let cells ← fields.mapM fun field => do
    pure (field, ← context.readCell context.outer field)
  let storedText ← match context.input with
    | .checked document | .partialView document _ => pure (document.storedTextIn context.outer)
    | .legacy _ _ => do
        let rawFields := comparison.left.storedTextFields ++ comparison.right.storedTextFields
        if rawFields.any (fun field => (model.lookupUniqueId field).toOption.any
            (fun declaration => !declaration.repeatableScope.isEmpty)) then
          throw (.checkedDocumentRequired [])
        pure context.scalar.fields.storedText
  pure { context.scalar.fields with
    storedText
    read := fun field => ((cells.find? (·.1 == field)).map (·.2)).getD malformedCheckedCell }

private def addressedTemporalContext (context : AddressedValidationEvaluationContext model)
    (comparison : CheckedScalarTemporalComparison model) :
    Except CheckedAddressingError (Option ComputationFillContext × Env) := do
  if !comparison.left.requiresAddressed && !comparison.right.requiresAddressed then return (none, context.outer)
  match context.input with
  | .checked document => pure (some document.indexedComputationFillContext, context.outer)
  | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired [])

/-- The failures a rule's whole-rule handler catches: the value failures, and a reached custom condition
no factory registers. The Kernel reports that rule under its own code as a value error with empty
reference channels and raises nothing (peer KF52; rules `C09`, `C10` and `M01`–`M03` of the
[custom-condition capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-custom-condition-calls)).
The verdict-only APIs keep the missing registration structural. -/
def ruleRuntimeFailure? : CheckedAddressingError → Option ScalarTemporalEvaluationFault
  | .customCondition (.missingRegistration name) => some (.addressing (.customCondition (.missingRegistration name)))
  | error => addressedValueFailure? error

/-- Whether the whole-rule handler catches a reported addressing fault, as `ruleRuntimeFailure?`
reports it, rather than leaving it structural. -/
def caughtByRule : CheckedAddressingError → Bool
  | .typeValidityValueFailure | .stringExpression .emptyPattern
  | .customCondition (.missingRegistration _) => true
  | _ => false

/-- Evaluate one row-selected checked tree while retaining structural addressing failure outside the verdict algebra. Truth testing and conditional classification retain their separate failure boundaries. -/
def evalAddressed (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError Verdict :=
  condition.evalWithTemporalResult context.scalar context.directRelevant
    (fun leaf => leaf.evalAddressed context) (.error .temporalUnavailable)
    (addressedTemporalFields context)
    (temporalAddressed := addressedTemporalContext context)
    (temporalFiltered := OrderedNumericValidationAtom.filteredAmountReader context)
    (numericResult := fun comparison => comparison.evalAddressedResult context)
    (leafRuntimeFault? := addressedValueFailure?)
    (firstFilledResult := ValidationConditionLeaf.evalFirstFilledComparisonAddressedResult context)
    (customResult := fun name => (context.scalar.customResult name).mapError CheckedAddressingError.customCondition)

/-- Evaluate the same connective tree with one already-prepared current-row RNU result. Duplicate construction remains outside and branch-independent. -/
def evalAddressedWithRepetitionNotUnique
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    Except CheckedAddressingError Verdict :=
  condition.evalWithTemporalResult context.scalar context.directRelevant
    (fun leaf => leaf.evalAddressedWithRepetitionNotUnique context result?) (.error .temporalUnavailable)
    (addressedTemporalFields context)
    (temporalAddressed := addressedTemporalContext context)
    (temporalFiltered := OrderedNumericValidationAtom.filteredAmountReader context)
    (numericResult := fun comparison => comparison.evalAddressedResult context)
    (leafRuntimeFault? := addressedValueFailure?)
    (firstFilledResult := ValidationConditionLeaf.evalFirstFilledComparisonAddressedResult context)
    (customResult := fun name => (context.scalar.customResult name).mapError CheckedAddressingError.customCondition)

/-- Keep reached temporal failure distinct from a row verdict until the rule's iteration handler.
The generated Java `CodeGenRuleDefinition.st` catches outside its row loop. -/
def evalAddressedWithRepetitionNotUniqueResult
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict :=
  condition.evalWithTemporalResult context.scalar context.directRelevant
    (fun leaf => (leaf.evalAddressedWithRepetitionNotUnique context result?).mapError Sum.inl)
    (.error (.inl .temporalUnavailable))
    (fun comparison => (addressedTemporalFields context comparison).mapError Sum.inl)
    (fun fault => .error (.inr fault))
    (temporalAddressed := fun comparison => (addressedTemporalContext context comparison).mapError Sum.inl)
    (temporalFiltered := OrderedNumericValidationAtom.filteredAmountReader context)
    (numericResult := fun comparison => (comparison.evalAddressedResult context).mapError fun
      | .inl error => .inl (.inl error)
      | .inr fault => .inr fault)
    (leafRuntimeFault? := fun
      | .inl error => ruleRuntimeFailure? error
      | .inr fault => some fault)
    (firstFilledResult := fun comparison =>
      (ValidationConditionLeaf.evalFirstFilledComparisonAddressedResult context comparison).mapError fun
        | .inl error => .inl (.inl error)
        | .inr fault => .inr fault)
    (customResult := fun name => (context.scalar.customResult name).mapError
      (fun error => .inl (.customCondition error)))

/-- Apply the ordinary full-validation content gate to the addressed tree without sampling any repeatable source on an ineligible empty row. -/
def evalAddressedFull (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except CheckedAddressingError Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalAddressed context
  else pure .notFired

/-- Apply the ordinary content gate before the RNU-aware addressed connective walk. -/
def evalAddressedFullWithRepetitionNotUnique
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) (result? : Option RepetitionNotUniqueResult) :
    Except CheckedAddressingError Verdict :=
  if hasContent || condition.canFireOnEmpty then
    condition.evalAddressedWithRepetitionNotUnique context result?
  else
    pure .notFired

end ValidationCondition

end A12Kernel
