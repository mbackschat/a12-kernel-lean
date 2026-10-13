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

/-- The reads one leaf authors and the subset whose filling could repair an omission. -/
structure ParallelLeafReads where
  referenced : List ParallelRead
  responsible : List ParallelRead

namespace ParallelFieldLeaf

private def isDistinctCount : ParallelNumericAtomOf ParallelFieldOperand → Bool
  | .aggregate .distinctCount _ => true
  | _ => false

/-- A group operand's whole subtree. Below a joined group each field keeps the joined row; above both,
the ordinary expansion through the outer environment wildcards the joined levels. A repeatable
operand group would bound the depth inside the join, which the presence gate never admits unstarred. -/
private def groupReads (pair : CheckedParallelFieldPair model) (outer : Env)
    (reference : ResolvedGroupReference) : Except ParallelReferenceError (List ParallelRead) :=
  match [pair.groups.leftGroup, pair.groups.rightGroup].find? (·.path.isPrefixOf reference.path) with
  | none => (·.map .expanded) <$> (fixedGroupPointers model reference outer).mapError .outer
  | some joined =>
      if (model.repeatableScopeForGroupPath reference.path).length !=
          (model.repeatableScopeForGroupPath joined.path).length then
        throw (.repeatableOperand reference.path)
      else pure ((model.groupSubtreeFields reference.path).map .joined)

/-- The authored reads of one leaf. A filled-presence operator can never be repaired by filling more,
and a distinct count asked to be larger is repaired by changing values, not by filling; both mirror
the ordinary carrier's omission selection. The root group's filled-presence names no field. -/
def reads (pair : CheckedParallelFieldPair model) (outer : Env) : ParallelFieldLeaf →
    Except ParallelReferenceError ParallelLeafReads
  | .groupPresence op reference => do
      match op with
      | .filled =>
          if reference.path.length == 1 then pure ⟨[], []⟩
          else pure ⟨← groupReads pair outer reference, []⟩
      | .notFilled =>
          let fields ← groupReads pair outer reference
          pure ⟨fields, fields⟩
  | .presence field op =>
      let declaration := ParallelRead.joined (pair.declaration field)
      match op with
      | .filled => pure ⟨[declaration], []⟩
      | .notFilled => pure ⟨[declaration], [declaration]⟩
  | .numeric _ lhs rhs =>
      let both := [lhs, rhs].map (.joined ∘ pair.declaration)
      pure ⟨both, both⟩
  | .fill op lhs rhs =>
      let both := [lhs, rhs].map (.joined ∘ pair.declaration)
      match op with
      | .allFieldsFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled => pure ⟨both, []⟩
      | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled
      | .fieldsNotCollectivelyFilled => pure ⟨both, both⟩
  | .comparison value =>
      let all := ((value.left.atoms ++ value.right.atoms).flatMap (·.operands)).map (.joined ∘ pair.declaration)
      pure ⟨all, if upwardOmissionCount isDistinctCount value then [] else all⟩

end ParallelFieldLeaf

namespace ParallelFieldCondition

private def leafReads (pair : CheckedParallelFieldPair model) (outer : Env) :
    ParallelFieldCondition → Except ParallelReferenceError (List ParallelLeafReads)
  | .leaf leaf => (fun reads => [reads]) <$> leaf.reads pair outer
  | .and left right | .or left right => do
      pure ((← leafReads pair outer left) ++ (← leafReads pair outer right))

/-- Each joined side that contributes a field also contributes its index field (KF539). -/
private def withIndexFields (pair : CheckedParallelFieldPair model)
    (fields : List FlatFieldDecl) : List FlatFieldDecl :=
  let side := fun (group : RepeatableGroupDecl) (index : FlatFieldDecl) =>
    if fields.any (group.path.isPrefixOf ·.groupPath) then [index] else []
  fields ++ side pair.groups.leftGroup pair.groups.leftIndexDeclaration ++
    side pair.groups.rightGroup pair.groups.rightIndexDeclaration

/-- A joined side's field takes that side's row coordinates, which its index field carries, and a
repeatable level inside the joined row is wildcarded. -/
private def fieldPointer (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (outer : Env) (cache : Option MessageIndexContext) (declaration : FlatFieldDecl) :
    Except ParallelReferenceError MessagePointer :=
  match [(row.left, pair.groups.leftIndexDeclaration), (row.right, pair.groups.rightIndexDeclaration)].find?
      (·.1.group.path.isPrefixOf declaration.groupPath) with
  | some (side, index) => do
      let joined ← side.messagePointer model outer index.id (cache.map (·, row.key)) |>.mapError .join
      let deeper := declaration.repeatableScope.length - joined.coordinates.length
      pure { field := declaration.id, coordinates := joined.coordinates ++ List.replicate deeper .wildcard }
  | none => concreteFieldPointer declaration outer |>.mapError .outer

/-- The reference channels of one message fired at a resolved row. `cache` is the message-cache
context the row's error pointer used, which a duplicate-key side needs to name its row. -/
def messageReferences (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition)
    (row : ResolvedParallelIndexRow) (outer : Env) (cache : Option MessageIndexContext)
    (message : FlatRuleMessage) : Except ParallelReferenceError ValidationMessageReferences := do
  let reads ← leafReads pair outer condition
  let project := fun (reads : List ParallelRead) => do
    let joined := reads.filterMap fun | .joined declaration => some declaration | .expanded _ => none
    let pointed ← ((withIndexFields pair joined).eraseDups).mapM (fieldPointer pair row outer cache)
    pure (pointed ++ reads.filterMap fun | .expanded pointer => some pointer | .joined _ => none)
  let referenced ← project (reads.flatMap (·.referenced))
  let fillToFix ← match message.messageType with
    | .value => pure []
    | .omission => project (reads.flatMap (·.responsible))
  pure { referenced, fillToFix }

end ParallelFieldCondition

end A12Kernel
