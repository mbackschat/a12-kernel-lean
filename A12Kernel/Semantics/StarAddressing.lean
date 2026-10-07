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

namespace StarAxis

/-- Whether one binding exceeds this exact axis's declared capacity. A missing capacity is unbounded; level mismatches are not silently treated as the same axis. -/
def bindingOverLimit (axis : StarAxis)
    (binding : RepeatableLevel × Nat) : Bool :=
  axis.level == binding.1 && match axis.repeatability with
    | none => false
    | some limit => binding.2 > limit

end StarAxis

namespace StarAxes

/-- Whether aligned outer-to-inner axes and bindings contain any over-capacity coordinate. Address-shape validation remains the caller's responsibility. -/
def environmentOverLimit (axes : List StarAxis) (environment : Env) : Bool :=
  (axes.zip environment).any fun binding =>
    binding.1.bindingOverLimit binding.2

end StarAxes

/-- Replace scalar admission with the path-owned over-repetition result when an address exceeds any declared repeatability. Structural row existence remains outside the cell. -/
def CheckedCell.withOverRepetitionIf {α : Type} (cell : CheckedCell α)
    (overLimit : Bool) : CheckedCell α :=
  if overLimit then
    { cell with parsed := none, findings := [.overRepetition] }
  else
    cell

/-- A resolved repeatable ancestry plus the zero-based position of its first star. -/
structure StarPath where
  axes : List StarAxis
  firstStar : Nat
  deriving Repr, DecidableEq

inductive StarAddressingError where
  | temporalValueFailure
  | worldUnavailable
  | typeValidityValueFailure
  /-- Reached filter arithmetic can exceed the implemented calendar profile; this is a support fault, not a cell finding. -/
  | unsupportedDateCalendar
  | invalidStarPosition (firstStar axisCount : Nat)
  | duplicateAxis (level : RepeatableLevel)
  | invalidRepeatability (level : RepeatableLevel)
  | missingBinding (level : RepeatableLevel)
  | duplicateBinding (level : RepeatableLevel)
  | invalidBinding (level : RepeatableLevel) (coordinate : Nat)
  | invalidRowDepth (level : RepeatableLevel) (path : List Nat) (expected : Nat)
  | orphanRow (level : RepeatableLevel) (path : List Nat) (parentLevel : RepeatableLevel)
  | nonprefixRows (level : RepeatableLevel) (parent actual : List Nat)
  /-- A group-scope operand has no addressing plan in this theory yet. It exists so that such an operand can never be *answered* — an empty stream would read as "the group contributed no values", which is a wrong result rather than a missing one. This is a representation boundary and not a Kernel refusal. -/
  | unsupportedGroupOperand (group : List String)
  deriving Repr, DecidableEq

def StarAddressingError.isFilterValueFailure : StarAddressingError → Bool
  | .temporalValueFailure | .typeValidityValueFailure => true
  | _ => false

namespace StarPath

/-- Repeatable levels strictly above the first star, which stay fixed by the surrounding rule environment. The starred level and every deeper axis are operand-local.

    This splits a plan the same way whatever the plan addresses, so a starred field path and a starred group path answer it identically rather than each restating the arithmetic. -/
def bindingScope (path : StarPath) : List RepeatableLevel :=
  (path.axes.take path.firstStar).map (·.level)

/-- Repeatable levels this plan reopens, beginning at its first star. -/
def reopenedScope (path : StarPath) : List RepeatableLevel :=
  (path.axes.drop path.firstStar).map (·.level)

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

/-- An environment binding failure is the star-addressing failure of the same level. -/
def _root_.A12Kernel.EnvBindingError.toStarAddressingError : EnvBindingError → StarAddressingError
  | .missingBinding level => .missingBinding level
  | .duplicateBinding level => .duplicateBinding level
  | .zeroBinding level => .invalidBinding level 0

/-- Keep only the exact named outer bindings above the first star. Bindings at the starred level and below are deliberately discarded. -/
def boundEnvironment (path : StarPath) (outer : Env) : Except StarAddressingError Env :=
  (path.axes.take path.firstStar).mapM fun axis => do
    let coordinate ←
      (outer.bindingAt axis.level).mapError EnvBindingError.toStarAddressingError
    pure (axis.level, coordinate)

/-- Enumerate a finite declared suffix without materializing rows. Field-fill filters use this
same coordinate space in validation and computation (filtered-fill grids, 2026-10-03/04). -/
def declaredEnvironments? (path : StarPath) (outer : Env) :
    Except StarAddressingError (Option (List Env)) := do
  let bound ← path.boundEnvironment outer
  if StarAxes.environmentOverLimit path.axes bound then return some []
  let mut environments := [bound]
  for axis in path.axes.drop path.firstStar do
    let some capacity := axis.repeatability | return none
    environments := environments.flatMap fun parent =>
      (List.range capacity).map fun index => parent ++ [(axis.level, index + 1)]
  pure (some environments)

end StarPath

structure ResolvedStarTopology where
  domain : ReopenedStarDomain
  environments : List Env

mutual
  /-- Ordered correspondence between one reopened tree and its complete named leaf environments. Each tree coordinate extends the exact outer prefix at its named level. -/
  inductive ReopenedStarDomain.EnvironmentCorrespondence :
      List RepeatableLevel → Env → ReopenedStarDomain → List Env → Prop
    | selected (base : Env) :
        ReopenedStarDomain.EnvironmentCorrespondence
          [] base .selectedLeaf [base]
    | repeatable (level : RepeatableLevel)
        (levels : List RepeatableLevel) (base : Env)
        (repeatability : Option Nat) (rows : ReopenedStarRows)
        (environments : List Env)
        (correspondence :
          ReopenedStarRows.EnvironmentCorrespondence
            level levels base rows environments) :
        ReopenedStarDomain.EnvironmentCorrespondence
          (level :: levels) base
          (.repeatable repeatability rows) environments

  /-- Ordered sibling correspondence. A child contributes all of its leaf environments before the remaining sibling rows. -/
  inductive ReopenedStarRows.EnvironmentCorrespondence :
      RepeatableLevel → List RepeatableLevel → Env →
        ReopenedStarRows → List Env → Prop
    | nil (level : RepeatableLevel) (levels : List RepeatableLevel)
        (base : Env) :
        ReopenedStarRows.EnvironmentCorrespondence
          level levels base .nil []
    | cons (level : RepeatableLevel) (levels : List RepeatableLevel)
        (base : Env) (coordinate : Nat) (child : ReopenedStarDomain)
        (rest : ReopenedStarRows) (childEnvironments restEnvironments : List Env)
        (childCorrespondence :
          ReopenedStarDomain.EnvironmentCorrespondence levels
            (base ++ [(level, coordinate)])
            child childEnvironments)
        (restCorrespondence :
          ReopenedStarRows.EnvironmentCorrespondence level levels base
            rest restEnvironments) :
        ReopenedStarRows.EnvironmentCorrespondence level levels base
          (.cons coordinate child rest)
          (childEnvironments ++ restEnvironments)
end

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

private theorem resolveAxes_environmentCorrespondence
    (document : Document) (axes : List StarAxis)
    (parent : List Nat) (base : Env)
    (resolved : ResolvedStarTopology)
    (resolution :
      document.resolveAxes axes parent base = .ok resolved) :
    ReopenedStarDomain.EnvironmentCorrespondence
      (axes.map (·.level)) base
      resolved.domain resolved.environments := by
  induction axes generalizing parent base resolved with
  | nil =>
      cases resolution
      exact .selected base
  | cons axis axes induction =>
      simp only [resolveAxes] at resolution
      cases coordinatesResult :
          canonicalCoordinates axis.level parent
            (document.coordinatesAt axis.level parent) with
      | error cause =>
          simp [coordinatesResult, bind, Except.bind] at resolution
      | ok coordinates =>
          simp only [coordinatesResult, bind, Except.bind] at resolution
          split at resolution
          · contradiction
          · rename_i children mappedChildren
            cases resolution
            apply ReopenedStarDomain.EnvironmentCorrespondence.repeatable
            clear coordinatesResult
            induction coordinates generalizing children with
              | nil =>
                  simp only [List.mapM_nil, pure, Except.pure]
                    at mappedChildren
                  cases mappedChildren
                  exact .nil axis.level (axes.map (·.level)) base
              | cons coordinate coordinates coordinateInduction =>
                  simp only [List.mapM_cons, bind, Except.bind]
                    at mappedChildren
                  cases childResult :
                      document.resolveAxes axes
                        (parent ++ [coordinate])
                        (base ++ [(axis.level, coordinate)]) with
                  | error cause =>
                      simp [childResult] at mappedChildren
                  | ok child =>
                      simp only [childResult, pure, Except.pure]
                        at mappedChildren
                      split at mappedChildren
                      · contradiction
                      · rename_i rest restResult
                        cases mappedChildren
                        exact .cons axis.level (axes.map (·.level)) base
                          coordinate child.domain
                          (rest.foldr
                            (fun current remaining =>
                              .cons current.1 current.2.domain remaining)
                            ReopenedStarRows.nil)
                          child.environments
                          (rest.flatMap (·.2.environments))
                          (induction
                            (parent := parent ++ [coordinate])
                            (base := base ++ [(axis.level, coordinate)])
                            (resolved := child) childResult)
                          (coordinateInduction rest restResult)

end Document

/-- The physical topology a star addresses, over-limit rows included: the actual nested rows the
checked path selects, independent of storage encounter order and never materializing a declared
Cartesian tail. Only a reader of the topology itself takes it, such as a row count or the rows a rule
iterates; an operand stream reads `resolveInCapacity`, so the two names carry the choice every caller
must make. -/
def StarPath.resolveTopology (path : StarPath) (document : Document) (outer : Env) :
    Except StarAddressingError ResolvedStarTopology := do
  path.validate
  document.validateRows path.axes 1 none
  let bound ← path.boundEnvironment outer
  document.resolveAxes (path.axes.drop path.firstStar) (bound.map (·.2)) bound

/-- Keep only the leaf environments within every declared repeatability. A row beyond its level's
capacity stays in the physical topology but lies outside the evaluation domain of an operand that
expands rows, on the validation and the computation arm alike, so its cell contributes neither a value
nor a formal poison ([`spec/07`](../../spec/07-repetition-and-iteration.md)). The domain stays the
physical tree, over-limit rows included, so the environment correspondence
`StarPath.resolveTopology_environmentCorrespondence` states holds for the resolved topology and not for this
projection; consumers read only the domain's open-tail state, which is unchanged because a level
holding an over-limit row is full. -/
def ResolvedStarTopology.inCapacity (resolved : ResolvedStarTopology)
    (axes : List StarAxis) : ResolvedStarTopology :=
  { resolved with
    environments := resolved.environments.filter fun environment =>
      !StarAxes.environmentOverLimit axes environment }

/-- Resolve the topology and narrow it to the declared-capacity extent. -/
def StarPath.resolveInCapacity (path : StarPath) (document : Document) (outer : Env) :
    Except StarAddressingError ResolvedStarTopology :=
  (·.inCapacity path.axes) <$> path.resolveTopology document outer

/-- Resolve one declaration under an operand's bound depth. Fully bound repeated declarations
contribute only an instantiated in-capacity row; reopened declarations retain their omitted tail. -/
def StarAxes.resolveOperandExtent (axes : List StarAxis) (document : Document)
    (outer : Env) (boundCount : Nat) : Except StarAddressingError (List Env × Bool) := do
  if axes.isEmpty then return ([[]], false)
  if boundCount < axes.length then
    let resolved ← ({ axes, firstStar := boundCount } : StarPath).resolveInCapacity document outer
    return (resolved.environments, resolved.domain.hasOpenTail)
  let scope := axes.map (·.level)
  let path ← (outer.pathForScope scope).mapError (·.toStarAddressingError)
  let environment := scope.zip path
  let instantiated := document.instantiatedRows.any fun row =>
    row.group == scope.getLast?.getD 0 && row.path == path
  return (if instantiated && !StarAxes.environmentOverLimit axes environment then [environment] else [], false)

/-- A successful checked star resolution constructs its hierarchical tree and ordered leaf environments from the same named axes and exact bound outer prefix. -/
theorem StarPath.resolveTopology_environmentCorrespondence
    (path : StarPath) (document : Document) (outer : Env)
    (resolved : ResolvedStarTopology)
    (resolution : path.resolveTopology document outer = .ok resolved) :
    ∃ bound,
      path.boundEnvironment outer = .ok bound ∧
      ReopenedStarDomain.EnvironmentCorrespondence
        ((path.axes.drop path.firstStar).map (·.level))
        bound resolved.domain resolved.environments := by
  simp only [StarPath.resolveTopology] at resolution
  cases validation : path.validate with
  | error cause =>
      rw [validation] at resolution
      cases resolution
  | ok validated =>
      rw [validation] at resolution
      cases rowValidation :
          Document.validateRows document path.axes 1 none with
      | error cause =>
          rw [rowValidation] at resolution
          cases resolution
      | ok validRows =>
          rw [rowValidation] at resolution
          cases boundResult : path.boundEnvironment outer with
          | error cause =>
              rw [boundResult] at resolution
              cases resolution
          | ok bound =>
              rw [boundResult] at resolution
              change document.resolveAxes
                  (path.axes.drop path.firstStar)
                  (bound.map (·.2)) bound = .ok resolved at resolution
              exact ⟨bound, rfl,
                Document.resolveAxes_environmentCorrespondence
                  document (path.axes.drop path.firstStar)
                  (bound.map (·.2)) bound resolved resolution⟩

end A12Kernel
