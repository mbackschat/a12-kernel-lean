import A12Kernel.Elaboration.ParallelFieldRule
import A12Kernel.Elaboration.ValidationCondition.Omission

/-! # Message references of a fired parallel field-pair row

A fired row's reference channels are the condition's structural inventory, independent of cell values (spec/01, spec/07), plus the index field of every joined side the inventory reads. Each joined side's fields point at that side's matched row, the unknown joined level when the side is unmatched, or the cache row of a duplicate key; fields outside both joined groups point through the outer environment.

A group operand expands by the ordinary depth rule: a group above the joined groups wildcards every joined level through the outer environment, and a group at or below one keeps the joined row and wildcards each repeatable level inside it (`parallel-group-references-2026-10-13`).
-/

namespace A12Kernel

/-- Why a fired parallel row has no reference projection. -/
inductive ParallelReferenceError where
  | join (error : CheckedIndexColumnError)
  | outer (error : ReferenceProjectionError)
  | repeatableOperand (path : GroupPath)
  deriving Repr, DecidableEq

/-- One authored read: a field pointed at through the joined row, or an ancestor group's expansion,
already pointed at through the outer environment. -/
inductive ParallelRead where
  | joined (declaration : FlatFieldDecl)
  | expanded (pointer : MessagePointer)

/-- The reads one leaf authors and the subset whose filling could repair an omission. The subset is
projected only for an omission, since a filtered leaf's projection can fail where a value message
needs none. -/
structure ParallelLeafReads where
  referenced : List ParallelRead
  responsible : Except ParallelReferenceError (List ParallelRead)

namespace ParallelFieldLeaf

private def isCount : ParallelNumericAtom model → Bool
  | .aggregate .distinctCount _ | .filledCount _ => true
  | _ => false

/-- A group operand's whole subtree. Below a joined group each field keeps the joined row; above both,
the ordinary expansion through the outer environment wildcards the joined levels. A repeatable
operand group would bound the depth inside the join, which the presence gate admits unstarred only at a
rule's error group's level, the error group or a fixed group inside it: its fields take the first row
the pair pins (`group-level`, `t8`). -/
private def groupReads (pair : CheckedParallelFieldPair model) (outer : Env)
    (reference : ResolvedGroupReference) : Except ParallelReferenceError (List ParallelRead) :=
  match [pair.groups.leftGroup, pair.groups.rightGroup].find? (·.path.isPrefixOf reference.path) with
  | none => (·.map .expanded) <$> (fixedGroupPointers model reference outer).mapError .outer
  | some joined =>
      let scope := model.repeatableScopeForGroupPath reference.path
      let joinedScope := model.repeatableScopeForGroupPath joined.path
      if scope != joinedScope && !(pair.errorGroup.any (·.isPrefixOf reference.path) &&
          scope == joinedScope ++ pair.pinnedLevel?.toList) then
        throw (.repeatableOperand reference.path)
      else pure ((model.groupSubtreeFields reference.path).map .joined)

/-- The authored reads of one leaf. A filled-presence operator can never be repaired by filling more,
and a distinct or filled count asked to be larger contributes no omission-responsible operand
(spec/01 §3.1); both mirror the ordinary carrier's omission selection. The root group's filled-presence names no field. -/
def reads (pair : CheckedParallelFieldPair model) (document : CheckedDocument model)
    (row : ResolvedParallelIndexRow) (outer : Env)
    (inputs : Option MessageReferenceInputs) : ParallelFieldLeaf model →
    Except ParallelReferenceError ParallelLeafReads
  | .groupPresence op reference => do
      match op with
      | .filled =>
          if reference.path.length == 1 then pure ⟨[], pure []⟩
          else pure ⟨← groupReads pair outer reference, pure []⟩
      | .notFilled =>
          let fields ← groupReads pair outer reference
          pure ⟨fields, pure fields⟩
  | .presence field op =>
      let declaration := ParallelRead.joined (pair.declaration field)
      match op with
      | .filled => pure ⟨[declaration], pure []⟩
      | .notFilled => pure ⟨[declaration], pure [declaration]⟩
  | .numeric _ lhs rhs =>
      let both := [lhs, rhs].map (.joined ∘ pair.declaration)
      pure ⟨both, pure both⟩
  | .fill op lhs rhs =>
      let both := [lhs, rhs].map (.joined ∘ pair.declaration)
      match op with
      | .allFieldsFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled => pure ⟨both, pure []⟩
      | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled
      | .fieldsNotCollectivelyFilled => pure ⟨both, pure both⟩
  -- An ordinary atom adds its one-atom leaf's ordinary reads.
  | leaf@(.comparison value) => do
      let all := ((value.left.atoms ++ value.right.atoms).flatMap (·.operands)).map (.joined ∘ pair.declaration)
      let atoms ← leaf.atomLeaves.mapM (ordinaryReads pair document row outer inputs)
      pure ⟨all ++ atoms.flatMap (·.referenced), do
        let responsible ← atoms.mapM (·.responsible)
        pure ((if upwardOmissionCount isCount value then [] else all) ++ responsible.flatten)⟩
  | .customCondition _ => pure ⟨[], pure []⟩
  | .valuesNotUnique operands =>
      let all := operands.map (.joined ∘ pair.declaration)
      pure ⟨all, pure all⟩
  -- The ordinary carrier's flat rule: every read is referenced and, presence aside, fills to fix.
  | .flat condition reads =>
      let all := reads.map (.joined ∘ pair.declaration)
      match condition with
      | .fieldFilled _ => pure ⟨all, pure []⟩
      | _ => pure ⟨all, pure all⟩
  | .ordinary leaf => ordinaryReads pair document row outer inputs leaf
where
  -- The ordinary projection at the leaf's binding; a keyed read names the row the index context
  -- places. A read of the bound side's own row, or below it through stars and fixed groups, is a
  -- joined read: it brings that side's index field (KF539) and names an unmatched side's row at the
  -- unknown level (parallel-child capture, `q01`, `q02`, `q08`, 2026-10-14).
  ordinaryReads (pair : CheckedParallelFieldPair model) (document : CheckedDocument model)
      (row : ResolvedParallelIndexRow) (outer : Env) (inputs : Option MessageReferenceInputs)
      (leaf : ValidationConditionLeaf model) : Except ParallelReferenceError ParallelLeafReads := do
    let condition : ValidationCondition model := .leaf leaf
    let environment := ((ordinaryEnvironment? pair document row outer leaf).map (·.1)).getD outer
    let classify := fun (pointer : MessagePointer) =>
      match pair.ordinaryBinding? leaf, model.lookupUniqueId pointer.field with
      | some (.side side), .ok declaration =>
          let (joined, index) := match side with
            | .left => (row.left, pair.groups.leftIndexDeclaration)
            | .right => (row.right, pair.groups.rightIndexDeclaration)
          let depth := index.repeatableScope.length
          if joined.group.path.isPrefixOf declaration.groupPath &&
              ((concreteFieldPointer index environment).toOption.map (·.coordinates)) ==
                some (pointer.coordinates.take depth) &&
              (pointer.coordinates.drop depth).all (· == .wildcard) then .joined declaration
          else .expanded pointer
      | _, _ => .expanded pointer
    pure ⟨(← condition.referencePointers environment inputs |>.mapError .outer).map classify,
      (·.map classify) <$> (condition.omissionPointers environment inputs).mapError .outer⟩

end ParallelFieldLeaf

namespace ParallelFieldCondition

private def leafReads (pair : CheckedParallelFieldPair model) (document : CheckedDocument model)
    (row : ResolvedParallelIndexRow) (outer : Env) (inputs : Option MessageReferenceInputs) :
    ParallelFieldCondition model → Except ParallelReferenceError (List ParallelLeafReads)
  | .leaf leaf => (fun reads => [reads]) <$> leaf.reads pair document row outer inputs
  | .and left right | .or left right => do
      pure ((← leafReads pair document row outer inputs left) ++
        (← leafReads pair document row outer inputs right))

/-- Each joined side that contributes a field also contributes its index field (KF539). -/
private def withIndexFields (pair : CheckedParallelFieldPair model)
    (fields : List FlatFieldDecl) : List FlatFieldDecl :=
  let side := fun (group : RepeatableGroupDecl) (index : FlatFieldDecl) =>
    if fields.any (group.path.isPrefixOf ·.groupPath) then [index] else []
  fields ++ side pair.groups.leftGroup pair.groups.leftIndexDeclaration ++
    side pair.groups.rightGroup pair.groups.rightIndexDeclaration

/-- A joined side's field takes that side's row coordinates, which its index field carries, and a
repeatable level inside the joined row is wildcarded unless the row binds it, as an error field's
level below the join is bound
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join),
`nested-join`). An unmatched side has no environment but still binds the nested rows it visits, so
its references name the visited row
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-nested-join-capacity),
`capacity-five`). -/
private def fieldPointer (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (outer : Env) (cache : Option MessageIndexContext) (declaration : FlatFieldDecl) :
    Except ParallelReferenceError MessagePointer :=
  match [(row.left, pair.groups.leftIndexDeclaration), (row.right, pair.groups.rightIndexDeclaration)].find?
      (·.1.group.path.isPrefixOf declaration.groupPath) with
  | some (side, index) => do
      let joined ← side.messagePointer model outer index.id (cache.map (·, row.key)) |>.mapError .join
      let deeper := (declaration.repeatableScope.drop joined.coordinates.length).map fun level =>
        ((side.environment.getD side.inner).uniqueRowAt? level).map MessageRepetitionCoordinate.concrete
          |>.getD .wildcard
      pure { field := declaration.id, coordinates := joined.coordinates ++ deeper }
  | none => concreteFieldPointer declaration outer |>.mapError .outer

/-- The reference channels of one message fired at a resolved row. `cache` is the message-cache
context the row's error pointer used, which a duplicate-key side needs to name its row; `inputs` place
the row a keyed group read beside the join selects. -/
def messageReferences (pair : CheckedParallelFieldPair model) (document : CheckedDocument model)
    (condition : ParallelFieldCondition model)
    (row : ResolvedParallelIndexRow) (outer : Env) (cache : Option MessageIndexContext)
    (message : FlatRuleMessage) (inputs : Option MessageReferenceInputs := none) :
    Except ParallelReferenceError ValidationMessageReferences := do
  -- The whole-rule handler's report names no reads, as on the ordinary carrier.
  if message.origin == .runtimeFailure then return { referenced := [], fillToFix := [] }
  let reads ← leafReads pair document row outer inputs condition
  let project := fun (reads : List ParallelRead) => do
    let joined := reads.filterMap fun | .joined declaration => some declaration | .expanded _ => none
    let pointed ← ((withIndexFields pair joined).eraseDups).mapM (fieldPointer pair row outer cache)
    pure (pointed ++ reads.filterMap fun | .expanded pointer => some pointer | .joined _ => none)
  let referenced ← project (reads.flatMap (·.referenced))
  let fillToFix ← match message.messageType with
    | .value => pure []
    | .omission => project (← reads.mapM (·.responsible)).flatten
  pure { referenced, fillToFix }

end ParallelFieldCondition

end A12Kernel
