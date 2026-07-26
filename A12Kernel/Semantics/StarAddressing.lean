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
  | invalidStarPosition (firstStar axisCount : Nat)
  | duplicateAxis (level : RepeatableLevel)
  | invalidRepeatability (level : RepeatableLevel)
  | missingBinding (level : RepeatableLevel)
  | duplicateBinding (level : RepeatableLevel)
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

private def toStarAddressingError : EnvBindingError → StarAddressingError
  | .missingBinding level => .missingBinding level
  | .duplicateBinding level => .duplicateBinding level
  | .zeroBinding level => .invalidBinding level 0

/-- Keep only the exact named outer bindings above the first star. Bindings at the starred level and below are deliberately discarded. -/
def boundEnvironment (path : StarPath) (outer : Env) : Except StarAddressingError Env :=
  (path.axes.take path.firstStar).mapM fun axis => do
    let coordinate ←
      (outer.bindingAt axis.level).mapError toStarAddressingError
    pure (axis.level, coordinate)

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

/-- A successful checked star resolution constructs its hierarchical tree and ordered leaf environments from the same named axes and exact bound outer prefix. -/
theorem StarPath.resolve_environmentCorrespondence
    (path : StarPath) (document : Document) (outer : Env)
    (resolved : ResolvedStarTopology)
    (resolution : path.resolve document outer = .ok resolved) :
    ∃ bound,
      path.boundEnvironment outer = .ok bound ∧
      ReopenedStarDomain.EnvironmentCorrespondence
        ((path.axes.drop path.firstStar).map (·.level))
        bound resolved.domain resolved.environments := by
  simp only [StarPath.resolve, Document.resolveStarPath] at resolution
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
