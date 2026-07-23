import A12Kernel.Semantics.StarAddressing

namespace A12Kernel.Conformance.StarAddressing

open A12Kernel

private def outer : StarAxis := { level := 10, repeatability := some 2 }
private def inner : StarAxis := { level := 20, repeatability := some 2 }
private def allRows : StarPath := { axes := [outer, inner], firstStar := 0 }

private def partialDocument : Document where
  instantiatedRows := [
    { group := 20, path := [1, 2] },
    { group := 10, path := [2] },
    { group := 20, path := [2, 1] },
    { group := 10, path := [1] },
    { group := 20, path := [1, 1] }]
  rawCells := fun _ => none

private def completeDocument : Document :=
  { partialDocument with instantiatedRows :=
      { group := 20, path := [2, 2] } :: partialDocument.instantiatedRows }

private def envsAndTail (path : StarPath) (document : Document) (environment : Env) :=
  match path.resolve document environment with
  | .error _ => none
  | .ok resolved => some (resolved.environments, resolved.domain.hasOpenTail)

private def rejectsAs (expected : StarAddressingError)
    (path : StarPath) (document : Document := partialDocument) (environment : Env := []) : Bool :=
  match path.resolve document environment with
  | .error actual => actual == expected
  | .ok _ => false

private inductive EnvPathSnapshot where
  | path (coordinates : List Nat)
  | missing (level : RepeatableLevel)
  | duplicate (level : RepeatableLevel)
  | zero (level : RepeatableLevel)
  deriving Repr, DecidableEq

private def envPathSnapshot (environment : Env)
    (scope : List RepeatableLevel) : EnvPathSnapshot :=
  match environment.pathForScope scope with
  | .ok coordinates => .path coordinates
  | .error (.missingBinding level) => .missing level
  | .error (.duplicateBinding level) => .duplicate level
  | .error (.zeroBinding level) => .zero level

/- A complete environment projects an arbitrary model scope by named level and in scope order; extra/deeper bindings do not become part of an ancestor address. Missing, repeated, and zero coordinates are distinct structural failures. -/
example :
    let environment : Env := [(20, 2), (30, 3), (10, 1)]
    envPathSnapshot environment [10, 20] = .path [1, 2] ∧
      envPathSnapshot environment [20] = .path [2] := by
  native_decide

example :
    envPathSnapshot [(10, 1)] [40] = .missing 40 := by
  native_decide

example :
    envPathSnapshot [(10, 1), (10, 2)] [10] = .duplicate 10 := by
  native_decide

example :
    envPathSnapshot [(10, 0)] [10] = .zero 10 := by
  native_decide

/- Caller-supplied plans and raw bindings fail closed before row enumeration. -/
example :
    rejectsAs (.invalidStarPosition 1 1) { axes := [outer], firstStar := 1 } ∧
    rejectsAs (.duplicateAxis 10) { axes := [outer, outer], firstStar := 0 } ∧
    rejectsAs (.invalidRepeatability 10)
      { axes := [{ outer with repeatability := some 0 }], firstStar := 0 } ∧
    rejectsAs (.invalidBinding 10 0) { axes := [outer, inner], firstStar := 1 }
      partialDocument [(10, 0)] := by
  native_decide

/- Storage encounter order cannot change canonical nested coordinate order. -/
example : envsAndTail allRows partialDocument [] = some (
    [[(10, 1), (20, 1)], [(10, 1), (20, 2)], [(10, 2), (20, 1)]], true) := by
  native_decide

/- Exhausting each finite axis under every actual parent closes the hierarchical tail. -/
example : envsAndTail allRows completeDocument [] = some (
    [[(10, 1), (20, 1)], [(10, 1), (20, 2)],
      [(10, 2), (20, 1)], [(10, 2), (20, 2)]], false) := by
  native_decide

/- A level above the first star remains bound by identity; deeper outer bindings are discarded. -/
example : envsAndTail { allRows with firstStar := 1 } partialDocument [(10, 2), (20, 9)] =
    some ([[(10, 2), (20, 1)]], true) := by
  native_decide

/- A same-level star reopens the current level instead of correlating it. -/
example :
    let path : StarPath := { axes := [outer], firstStar := 0 }
    envsAndTail path partialDocument [(10, 2)] = some ([[(10, 1)], [(10, 2)]], false) := by
  native_decide

/- Over-limit rows remain addressable so later formal checking can classify them; they do not manufacture a missing declared row. -/
example :
    let document : Document := {
      instantiatedRows := (List.range 3).map fun offset => { group := 10, path := [offset + 1] }
      rawCells := fun _ => none }
    let path : StarPath := { axes := [outer], firstStar := 0 }
    envsAndTail path document [] = some ([[(10, 1)], [(10, 2)], [(10, 3)]], false) := by
  native_decide

/- Positional reuse across unrelated branches is rejected as a missing named binding. -/
example :
    let path : StarPath := { axes := [outer, inner], firstStar := 1 }
    (match path.resolve partialDocument [(99, 2)] with
    | .error (.missingBinding 10) => true
    | _ => false) = true := by
  native_decide

/- A gap is invalid topology rather than a silently reordered or flattened row set. -/
example :
    let document : Document := {
      instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [3] }]
      rawCells := fun _ => none }
    let path : StarPath := { axes := [outer], firstStar := 0 }
    (match path.resolve document [] with
    | .error (.nonprefixRows 10 [] [1, 3]) => true
    | _ => false) = true := by
  native_decide

/- A syntactically deep inner row cannot be silently dropped when its parent row is absent. -/
example :
    let document : Document := {
      instantiatedRows := [{ group := 10, path := [1] }, { group := 20, path := [2, 1] }]
      rawCells := fun _ => none }
    (match allRows.resolve document [] with
    | .error (.orphanRow 20 [2, 1] 10) => true
    | _ => false) = true := by
  native_decide

/- The shared bridge derives cells from the same environment order as the tree. -/
example :
    (match allRows.resolve partialDocument [] with
    | .error _ => []
    | .ok resolved =>
        (resolved.toResolvedSide (kind := .number)
          (fun env => .present (env.foldl (fun n binding => n + binding.2) 0))).cells.map
            fun cell => match cell with | .present value => some value | _ => none) =
      [some 2, some 3, some 3] := by
  native_decide

end A12Kernel.Conformance.StarAddressing
