import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Checked parallel-computation clearing-plan locks -/

namespace A12Kernel.Conformance.ParallelComputationClearingPlan

open A12Kernel

private def indexDeclaration (id : FieldId) (path : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name := "Key"
  policy := { kind := .string }
  repeatableScope := scope
}

private def numberDeclaration (id : FieldId) (path : GroupPath)
    (name : String) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := path
  name
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := scope
}

private def frame : RepeatableGroupDecl := {
  level := 50
  path := ["Plan", "Frame"]
  repeatability := some 2
}

private def targetGroup : RepeatableGroupDecl := {
  level := 60
  path := ["Plan", "Frame", "Target"]
  repeatability := some 2
  indexField := some 1
}

private def operandGroup : RepeatableGroupDecl := {
  level := 70
  path := ["Plan", "Operand"]
  repeatability := some 2
  indexField := some 3
}

private def model : FlatModel := {
  fields := [
    indexDeclaration 1 targetGroup.path [50, 60],
    numberDeclaration 2 targetGroup.path "Result" [50, 60],
    numberDeclaration 5 targetGroup.path "Peer" [50, 60],
    indexDeclaration 3 operandGroup.path [70],
    numberDeclaration 4 operandGroup.path "Input" [70]
  ]
  repeatableGroups := [frame, targetGroup, operandGroup]
}

private def operandPath : SurfaceFieldPath := {
  base := .absolute
  groups := operandGroup.path
  field := "Input"
}

private def checked? :=
  (checkParallelNumericComputationClearingPlan
    model ["Plan"] 2 operandPath).toOption

/- The ordinary non-starred operand and repeatable target determine both indexed groups and scopes without caller-supplied groups or a route bit. -/
example :
    (checked?.map fun checked =>
      (checked.groups.leftGroup.path,
        checked.groups.rightGroup.path,
        checked.targetDeclaration.repeatableScope,
        checked.operandDeclaration.repeatableScope)) =
      some (targetGroup.path, operandGroup.path, [50, 60], [70]) := by
  native_decide

/- A second ordinary field in the target's own indexed group is not a parallel route. -/
example :
    (match checkParallelNumericComputationClearingPlan model ["Plan"] 2 {
        base := .absolute
        groups := targetGroup.path
        field := "Peer"
      } with
    | .error error => some error
    | .ok _ => none) =
      some (.join (.incompatibleGroups targetGroup.path targetGroup.path)) := by
  native_decide

end A12Kernel.Conformance.ParallelComputationClearingPlan
