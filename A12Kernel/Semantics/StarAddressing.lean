import A12Kernel.Semantics.Iteration
import A12Kernel.Semantics.StarCompleteness

/-! # Checked repeatable-star topology resolution

This boundary starts after path syntax and model lookup have identified one outer-to-inner repeatable ancestry and the first starred axis. It binds only the named axes strictly above that star, derives canonical 1-based child order from explicit document rows, and constructs the existing reopened-domain tree and leaf environment stream together.
-/

namespace A12Kernel

/-- One model-owned repeatable axis on a resolved field path. `none` is an unbounded declaration. -/
structure StarAxis where
  level : RepeatableLevel
  repeatability : Option Nat
  deriving Repr, DecidableEq

/-- A resolved repeatable ancestry plus the zero-based position of its first star. -/
structure StarPath where
  axes : List StarAxis
  firstStar : Nat
  deriving Repr, DecidableEq

inductive StarAddressingError where
  | invalidStarPosition (firstStar axisCount : Nat)
  | duplicateAxis (level : RepeatableLevel)
  | invalidRepeatability (level : RepeatableLevel)
  | missingBinding (level : RepeatableLevel)
  | invalidBinding (level : RepeatableLevel) (coordinate : Nat)
  | invalidRowDepth (level : RepeatableLevel) (path : List Nat) (expected : Nat)
  | orphanRow (level : RepeatableLevel) (path : List Nat) (parentLevel : RepeatableLevel)
  | nonprefixRows (level : RepeatableLevel) (parent actual : List Nat)
  deriving Repr, DecidableEq

namespace StarPath

private def invalidRepeatability? : List StarAxis → Option RepeatableLevel
  | [] => none
  | axis :: rest =>
      if axis.repeatability == some 0 then some axis.level else invalidRepeatability? rest

/-- Validate the model-independent invariants that checked path lowering must establish. -/
def validate (path : StarPath) : Except StarAddressingError Unit := do
  if path.firstStar >= path.axes.length then
    throw (.invalidStarPosition path.firstStar path.axes.length)
  match RowIndex.firstDuplicate? (path.axes.map (·.level)) with
  | some level => throw (.duplicateAxis level)
  | none => pure ()
  match invalidRepeatability? path.axes with
  | some level => throw (.invalidRepeatability level)
  | none => pure ()

private def bind : List StarAxis → Env → Except StarAddressingError Env
  | [], _ => pure []
  | axis :: _, [] => throw (.missingBinding axis.level)
  | axis :: axes, (level, coordinate) :: environment => do
      if level != axis.level then throw (.missingBinding axis.level)
      if coordinate == 0 then throw (.invalidBinding level coordinate)
      pure ((level, coordinate) :: (← bind axes environment))

/-- Keep only the exact named outer bindings above the first star. Bindings at the starred level and below are deliberately discarded. -/
def boundEnvironment (path : StarPath) (outer : Env) : Except StarAddressingError Env :=
  bind (path.axes.take path.firstStar) outer

end StarPath

structure ResolvedStarTopology where
  domain : ReopenedStarDomain
  environments : List Env

namespace ResolvedStarTopology

/-- Classify selected leaves in the same canonical order used to construct the reopened tree. -/
def toResolvedSide (resolved : ResolvedStarTopology)
    (read : Env → ValueListCell kind) (hasHaving : Bool := false) : ResolvedValueListSide kind :=
  resolved.domain.toResolvedSide (resolved.environments.map read) hasHaving

end ResolvedStarTopology

namespace Document

private def rowWithWrongDepth? (document : Document) (axis : StarAxis) (depth : Nat) : Option RowAddr :=
  document.instantiatedRows.find? fun row => row.group == axis.level && row.path.length != depth

private def orphanRow? (document : Document) (axis : StarAxis) (parentLevel : RepeatableLevel) (depth : Nat) : Option RowAddr :=
  document.instantiatedRows.find? fun row =>
    row.group == axis.level && !document.instantiatedRows.contains {
      group := parentLevel
      path := row.path.take (depth - 1)
    }

private def validateRows (document : Document) :
    List StarAxis → Nat → Option RepeatableLevel → Except StarAddressingError Unit
  | [], _, _ => pure ()
  | axis :: axes, depth, parentLevel => do
      match document.rowWithWrongDepth? axis depth with
      | some row => throw (.invalidRowDepth axis.level row.path depth)
      | none => pure ()
      match parentLevel with
      | none => pure ()
      | some parent =>
          match document.orphanRow? axis parent depth with
          | some row => throw (.orphanRow axis.level row.path parent)
          | none => pure ()
      validateRows document axes (depth + 1) (some axis.level)

private def coordinatesAt (document : Document) (level : RepeatableLevel) (parent : List Nat) : List Nat :=
  document.instantiatedRows.filterMap fun row =>
    if row.group == level && row.path.take parent.length == parent then
      match row.path.drop parent.length with
      | [coordinate] => some coordinate
      | _ => none
    else
      none

private def expectedCoordinates (count : Nat) : List Nat :=
  (List.range count).map (· + 1)

private def canonicalCoordinates (level : RepeatableLevel) (parent coordinates : List Nat) :
    Except StarAddressingError (List Nat) := do
  let expected := expectedCoordinates coordinates.length
  if RowIndex.hasDuplicates coordinates || !expected.all coordinates.contains then
    throw (.nonprefixRows level parent coordinates)
  pure expected

private def resolveAxes (document : Document) :
    List StarAxis → List Nat → Env → Except StarAddressingError ResolvedStarTopology
  | [], _, environment => pure { domain := .selectedLeaf, environments := [environment] }
  | axis :: axes, parent, environment => do
      let coordinates ← canonicalCoordinates axis.level parent (document.coordinatesAt axis.level parent)
      let children ← coordinates.mapM fun coordinate => do
        let child ← resolveAxes document axes (parent ++ [coordinate])
          (environment ++ [(axis.level, coordinate)])
        pure (coordinate, child)
      let rows := children.foldr
        (fun child rest => .cons child.1 child.2.domain rest) ReopenedStarRows.nil
      pure {
        domain := .repeatable axis.repeatability rows
        environments := children.flatMap (·.2.environments)
      }

/-- Resolve the actual nested rows selected by one checked starred path. The result is independent of storage encounter order and never materializes a declared Cartesian tail. -/
def resolveStarPath (document : Document) (path : StarPath) (outer : Env) :
    Except StarAddressingError ResolvedStarTopology := do
  path.validate
  validateRows document path.axes 1 none
  let bound ← path.boundEnvironment outer
  resolveAxes document (path.axes.drop path.firstStar) (bound.map (·.2)) bound

end Document

def StarPath.resolve (path : StarPath) (document : Document) (outer : Env) :
    Except StarAddressingError ResolvedStarTopology :=
  document.resolveStarPath path outer

end A12Kernel
