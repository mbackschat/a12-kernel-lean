import A12Kernel.Elaboration.ValidationRelevance

/-! # Wholly relevant group instances under partial validation

Kernel 31.1.1 decides a partial `NumberOfFilledGroups` on the counted group's wholly relevant
instances (spec/10 §5.6, a12-dmkits KF667). A group instance is wholly relevant when each of its direct
members is: a field by any covering selection, a sub-group by its own wholly relevant instances. The
judgment runs bottom-up from the deepest groups, and three rules shape it:

- The members' covered instance sets intersect, so a selection of one member at a row and another
  member at every row cover that row only.
- A repeatable sub-group contributes to its parent only through instances wildcarded at its own level;
  a fixed sub-group always contributes.
- Concrete instances of a repeatable group naming every declared slot under one parent fold into that
  level's wildcard when the capacity is at least two. A capacity-one or unbounded level never folds; the
  Kernel admits no such repeatable level, since repeatability `1` declares a fixed group and a star over
  it is refused, so the guard only keeps the function total.

A selection naming a group stands for every field below it. A group with no field below it, declared
empty, is a member of its parent but never wholly relevant itself, so its parent never is either:
measured on a counted repeatable level and on a counted fixed group by a12-dmkits
"PartialWhollyRelevantBoundaryDiffTest" at "6fcdbfcdf", kernel 31.1.1.
-/

namespace A12Kernel

namespace RelevantEntityPattern

/-- The pattern with every nonrepeatable segment wildcarded, where its index is observationally inert,
    so that equal instances compare equal. -/
private def normalized (model : FlatModel) (entity : RelevantEntityPattern) : RelevantEntityPattern :=
  { entity with indices := (List.range entity.path.length).zip entity.indices |>.map fun (depth, index) =>
      if model.repeatableGroups.any (·.path == entity.path.take (depth + 1)) then index else .all }

/-- The common instances of two patterns of one path, if any: a wildcard meets anything, and two
    concrete coordinates meet only when equal. -/
private def meet? (left right : RelevantEntityPattern) : Option RelevantEntityPattern := do
  if left.path != right.path || left.indices.length != right.indices.length then none
  let indices ← (left.indices.zip right.indices).mapM fun
    | (.all, index) | (index, .all) => some index
    | (.concrete a, .concrete b) => if a == b then some (.concrete a) else none
  pure { left with indices }

end RelevantEntityPattern

namespace ValidationRelevanceScope

open RelevantEntityPattern

/-- The direct members of a group: its own fields and its immediate sub-groups, by path. -/
private def directMembers (model : FlatModel) (groupPath : GroupPath) : List (List String) :=
  let groups := (model.fields.map (·.groupPath) ++ model.repeatableGroups.map (·.path) ++
      model.emptyNonrepeatableGroups).filterMap
    fun path => if groupPath.isPrefixOf path && path.length > groupPath.length then
      some (path.take (groupPath.length + 1)) else none
  ((model.fields.filter (·.groupPath == groupPath)).map (·.path) ++ groups).eraseDups

/-- Fold the concrete instances of a repeatable group that name every declared slot under one parent
    into that level's wildcard when the capacity is at least two; drop a coordinate past the capacity. -/
private def foldDeclaredRows (model : FlatModel) (groupPath : GroupPath)
    (instances : List RelevantEntityPattern) : List RelevantEntityPattern :=
  match model.repeatableGroups.find? (·.path == groupPath) |>.bind (·.repeatability) with
  | none | some 0 | some 1 => instances
  | some capacity =>
      let parent (entity : RelevantEntityPattern) := entity.indices.dropLast
      let concrete := instances.filterMap fun entity => match entity.indices.getLast? with
        | some (.concrete row) => if row ≤ capacity then some (entity, row) else none
        | _ => none
      let wildcarded := instances.filter (·.indices.getLast? == some .all)
      let parents := (concrete.map (parent ·.1)).eraseDups
      wildcarded ++ parents.flatMap fun key =>
        let rows := (concrete.filter (parent ·.1 == key)).map (·.2) |>.eraseDups
        if rows.length ≥ capacity then [{ path := groupPath, indices := key ++ [.all] }]
        else (concrete.filter (parent ·.1 == key)).map (·.1)

/-- The wholly relevant instances of `groupPath` among `fields`, the call's selections expanded to
    and normalized at field level. Each recursion descends one segment, so `depth`, the model's
    deepest path length, bounds it; an exhausted bound answers no instance. -/
private def whollyRelevant (model : FlatModel) (fields : List RelevantEntityPattern) :
    Nat → GroupPath → List RelevantEntityPattern
  | 0, _ => []
  | depth + 1, groupPath =>
  let members := directMembers model groupPath
  -- Each member's covered instances, cut back to this group's depth.
  let covered : List (List RelevantEntityPattern) := members.map fun member =>
    let own :=
      if model.fields.any (·.path == member) then fields.filter (·.path == member)
      else
        let repeatable := model.repeatableGroups.any (·.path == member)
        (whollyRelevant model fields depth member).filter fun entity =>
          !repeatable || entity.indices.getLast? == some .all
    own.map fun entity => { path := groupPath, indices := entity.indices.take groupPath.length }
  if members.isEmpty || covered.any (·.isEmpty) then [] else
  let candidates := covered.head!.eraseDups
  let intersected := covered.tail.foldl (fun current next =>
    (current.flatMap fun left => next.filterMap (meet? left ·)).eraseDups) candidates
  reduceWildcardDominance (foldDeclaredRows model groupPath intersected)

/-- The counted group's wholly relevant instances in a partial call. -/
def whollyRelevantGroups (entities : List RelevantEntityPattern) (model : FlatModel)
    (groupPath : GroupPath) : List RelevantEntityPattern :=
  let fields := model.fields.flatMap fun declaration =>
    entities.filterMap fun entity => (entity.projectOntoTarget? declaration.path).map (normalized model)
  let depth := (model.fields.map (·.path.length)).foldl max 0
  whollyRelevant model fields.eraseDups depth groupPath

/-- Kernel 31.1.1's extent gate of a partial group count: the counted group's wholly relevant
    instances inside the current iteration subtree are nonempty and wildcard every reopened level. -/
def coversGroupCountExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (groupPath : List String) (boundLevels reopenedLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      reducedUniversalCovers
        (retainedExtentPatterns (whollyRelevantGroups entities model groupPath) model boundLevels outer some)
        model reopenedLevels

end ValidationRelevanceScope

end A12Kernel
