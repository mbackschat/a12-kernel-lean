import A12Kernel.Elaboration.ParallelFieldRule
import A12Kernel.Elaboration.ValidationCondition.Omission

/-! # Message references of a fired parallel field-pair row

A fired row's reference channels are the condition's structural inventory, independent of cell values (spec/01, spec/07), plus the index field of every joined side the inventory reads. Each joined side's fields point at that side's matched row, the unknown joined level when the side is unmatched, or the cache row of a duplicate key; fields outside both joined groups point through the outer environment.

Group-presence expansions are projected only where a retained population settles their coordinates: a descendant field of a joined group. A group above the joined groups, and a descendant repeatable below the joined level, are refused rather than guessed.
-/

namespace A12Kernel

/-- Why a fired parallel row has no reference projection. -/
inductive ParallelReferenceError where
  | join (error : CheckedIndexColumnError)
  | outer (error : ReferenceProjectionError)
  | groupAboveJoin (path : GroupPath)
  | repeatableBelowJoin (field : FieldId)
  deriving Repr, DecidableEq

/-- The fields one leaf authors and the subset whose filling could repair an omission. -/
structure ParallelLeafReads where
  referenced : List FlatFieldDecl
  responsible : List FlatFieldDecl

namespace ParallelFieldLeaf

private def isDistinctCount : ParallelNumericAtomOf ParallelFieldOperand → Bool
  | .aggregate .distinctCount _ => true
  | _ => false

/-- A group operand expands to its whole subtree. Below a joined group the expansion is the joined
side's own fields; a deeper repeatable would need a coordinate no retained population fixes. -/
private def groupReads (pair : CheckedParallelFieldPair model) (reference : ResolvedGroupReference) :
    Except ParallelReferenceError (List FlatFieldDecl) :=
  match [pair.groups.leftGroup, pair.groups.rightGroup].find? (·.path.isPrefixOf reference.path) with
  | none => throw (.groupAboveJoin reference.path)
  | some joined =>
      let fields := model.groupSubtreeFields reference.path
      let depth := (model.repeatableScopeForGroupPath joined.path).length
      match fields.find? (depth < ·.repeatableScope.length) with
      | some deeper => throw (.repeatableBelowJoin deeper.id)
      | none => pure fields

/-- The authored reads of one leaf. A filled-presence operator can never be repaired by filling more,
and a distinct count asked to be larger is repaired by changing values, not by filling; both mirror
the ordinary carrier's omission selection. The root group's filled-presence names no field. -/
def reads (pair : CheckedParallelFieldPair model) : ParallelFieldLeaf →
    Except ParallelReferenceError ParallelLeafReads
  | .groupPresence op reference => do
      match op with
      | .filled =>
          if reference.path.length == 1 then pure ⟨[], []⟩
          else pure ⟨← groupReads pair reference, []⟩
      | .notFilled =>
          let fields ← groupReads pair reference
          pure ⟨fields, fields⟩
  | .presence field op =>
      let declaration := pair.declaration field
      match op with
      | .filled => pure ⟨[declaration], []⟩
      | .notFilled => pure ⟨[declaration], [declaration]⟩
  | .numeric _ lhs rhs =>
      let both := [lhs, rhs].map pair.declaration
      pure ⟨both, both⟩
  | .fill op lhs rhs =>
      let both := [lhs, rhs].map pair.declaration
      match op with
      | .allFieldsFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled => pure ⟨both, []⟩
      | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled
      | .fieldsNotCollectivelyFilled => pure ⟨both, both⟩
  | .comparison value =>
      let all := ((value.left.atoms ++ value.right.atoms).flatMap (·.operands)).map pair.declaration
      pure ⟨all, if upwardOmissionCount isDistinctCount value then [] else all⟩

end ParallelFieldLeaf

namespace ParallelFieldCondition

private def leafReads (pair : CheckedParallelFieldPair model) :
    ParallelFieldCondition → Except ParallelReferenceError (List ParallelLeafReads)
  | .leaf leaf => (fun reads => [reads]) <$> leaf.reads pair
  | .and left right | .or left right => do
      pure ((← leafReads pair left) ++ (← leafReads pair right))

/-- Each joined side that contributes a field also contributes its index field (KF539). -/
private def withIndexFields (pair : CheckedParallelFieldPair model)
    (fields : List FlatFieldDecl) : List FlatFieldDecl :=
  let side := fun (group : RepeatableGroupDecl) (index : FlatFieldDecl) =>
    if fields.any (group.path.isPrefixOf ·.groupPath) then [index] else []
  fields ++ side pair.groups.leftGroup pair.groups.leftIndexDeclaration ++
    side pair.groups.rightGroup pair.groups.rightIndexDeclaration

private def fieldPointer (model : FlatModel) (row : ResolvedParallelIndexRow)
    (outer : Env) (cache : Option MessageIndexContext) (declaration : FlatFieldDecl) :
    Except ParallelReferenceError MessagePointer :=
  match [row.left, row.right].find? (·.group.path.isPrefixOf declaration.groupPath) with
  | some side => side.messagePointer model outer declaration.id (cache.map (·, row.key))
      |>.mapError .join
  | none => concreteFieldPointer declaration outer |>.mapError .outer

/-- The reference channels of one message fired at a resolved row. `cache` is the message-cache
context the row's error pointer used, which a duplicate-key side needs to name its row. -/
def messageReferences (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition)
    (row : ResolvedParallelIndexRow) (outer : Env) (cache : Option MessageIndexContext)
    (message : FlatRuleMessage) : Except ParallelReferenceError ValidationMessageReferences := do
  let reads ← leafReads pair condition
  let project := fun (fields : List FlatFieldDecl) =>
    ((withIndexFields pair fields).eraseDups).mapM (fieldPointer model row outer cache)
  let referenced ← project (reads.flatMap (·.referenced))
  let fillToFix ← match message.messageType with
    | .value => pure []
    | .omission => project (reads.flatMap (·.responsible))
  pure { referenced, fillToFix }

end ParallelFieldCondition

end A12Kernel
