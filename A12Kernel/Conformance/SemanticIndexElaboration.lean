import A12Kernel.Elaboration.SemanticIndex

/-! # Checked one-group Number semantic-index conformance -/

namespace A12Kernel

private def keyId : FieldId := 1
private def targetId : FieldId := 2

private def keyField : FlatNumberField := {
  id := keyId
  info := { scale := 2, signed := false }
}

private def targetField : FlatNumberField := {
  id := targetId
  info := { scale := 2, signed := true }
}

private def keyDecl : FlatFieldDecl := {
  id := keyId
  groupPath := ["Order", "Items"]
  name := "LineNo"
  policy := { kind := .number { scale := 2, signed := false } }
  repeatableScope := [10]
}

private def targetDecl : FlatFieldDecl := {
  id := targetId
  groupPath := ["Order", "Items"]
  name := "Amount"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def items : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Items"]
  repeatability := some 20
  indexField := some keyId
}

private def model : FlatModel := {
  fields := [keyDecl, targetDecl]
  repeatableGroups := [items]
}

private def authored (key : Rat) : SurfaceNumberSemanticIndex := {
  target := {
    base := .absolute
    groups := ["Order", "Items"]
    field := "Amount"
  }
  key
}

private def raw (rows : List RowIndex)
    (key : RowIndex → RawCell) (target : RowIndex → RawCell) :
    RawSingleGroupContext := {
  candidates := rows
  read row id :=
    if id == keyId then key row
    else if id == targetId then target row
    else .empty
}

private def contextErrorOf {value : Type} :
    Except SemanticIndexContextError value → Option SemanticIndexContextError
  | .ok _ => none
  | .error error => some error

private def resolveErrorOf {value : Type} :
    Except ResolveError value → Option ResolveError
  | .ok _ => none
  | .error error => some error

private def semanticIndexErrorOf {value : Type} :
    Except SemanticIndexElabError value → Option SemanticIndexElabError
  | .ok _ => none
  | .error error => some error

private def checked : CheckedNumberSemanticIndexSource model :=
  {
    group := items
    indexField := keyField
    targetField
    key := 5
    modelWellFormed := by native_decide
    groupOwned := by native_decide
    indexDeclared := by native_decide
    indexOwned := by native_decide
    targetOwned := by native_decide
  }

/- The authored route reconstructs that exact checked source from model-owned metadata. -/
example :
    (elaborateNumberSemanticIndexSource model ["Order"] (authored 5)).isOk = true := by
  native_decide

/- Numeric key equality is value-based: 5 and 5.00 select the same admitted row. -/
example :
    (checked.lookupValue
      (raw [1, 2]
        (fun row => if row == 1 then .parsed (.num 5.00) else .parsed (.num 6))
        (fun row => if row == 1 then .parsed (.num 7) else .parsed (.num 8)))
      .validation).toOption = some (.value (.num 7)) := by
  native_decide

/- A duplicate numeric key excludes every participant and makes validation unresolved. -/
example :
    (checked.lookupValue
      (raw [1, 2]
        (fun _ => .parsed (.num 5))
        (fun row => .parsed (.num row)))
      .validation).toOption = some (.unknown .duplicateIndex) := by
  native_decide

/- Validation accepts an unrelated clean match before an invalid key; computation poisons on the column first. -/
example :
    let context := raw [1, 2]
      (fun row => if row == 1 then .parsed (.num 5) else .rejected .malformed)
      (fun row => if row == 1 then .parsed (.num 7) else .parsed (.num 8))
    (checked.lookupValue context .validation).toOption = some (.value (.num 7)) ∧
      (checked.lookupValue context .computation).toOption = some (.poison .malformed) := by
  native_decide

/- Empty index cells are auto-required and therefore make the column unavailable. -/
example :
    let context := raw [1]
      (fun _ => .presentEmpty)
      (fun _ => .parsed (.num 7))
    (checked.lookupValue context .validation).toOption = some (.unknown .required) ∧
      (checked.lookupValue context .computation).toOption = some (.poison .required) := by
  native_decide

/- A checked clean no-match reaches the established signed Number empty projection and comparison polarity. -/
example :
    let context := raw [1]
      (fun _ => .parsed (.num 6))
      (fun _ => .parsed (.num 8))
    (checked.validationNumberOperand context).toOption =
        some (.value 0 (.emptyNumber true)) ∧
      (checked.validationNumberOperand context).toOption.map
        (fun operand => NumericComparisonOp.equal.evalFixedRight operand 0) =
          some (.fired .omission) := by
  native_decide

/- The one-group context guard rejects malformed row identity before reading cells. -/
example :
    contextErrorOf (checked.lookupValue
      (raw [1, 1] (fun _ => .parsed (.num 5)) (fun _ => .parsed (.num 7)))
      .validation) = some (.topology (.duplicateCandidate 1)) := by
  native_decide

/- Numeric normalization does not leak into exact-text keys with the same visible spelling. -/
example :
    let column : ResolvedSemanticIndexColumn := {
      entries := [{ token := .text "5", target := {
        rawPresent := true, parsed := some (.num 7), findings := [] } }]
      unavailableKey := none
    }
    column.lookupNumberValue .validation 5 = .empty := by
  native_decide

/- The checked source requires a model-declared index field on the selected target group. -/
example :
    let noIndexModel := { model with
      repeatableGroups := [{ items with indexField := none }] }
    semanticIndexErrorOf
      (elaborateNumberSemanticIndexSource noIndexModel ["Order"] (authored 5)) =
        some (.missingIndexField ["Order", "Items"]) := by
  native_decide

/- Unknown index metadata is rejected at model validation instead of becoming a guessed row selector. -/
example :
    let badModel := { model with
      repeatableGroups := [{ items with indexField := some 999 }] }
    resolveErrorOf badModel.validate =
      some (.invalidIndexField ["Order", "Items"] 999) := by
  native_decide

/- This capsule fails closed on a valid non-Number index declaration while leaving that broader model profile available to its future typed owner. -/
example :
    let stringKey : FlatFieldDecl := {
      keyDecl with policy := { kind := .string }
    }
    let stringModel : FlatModel := { model with fields := [stringKey, targetDecl] }
    stringModel.validate.isOk = true ∧
      semanticIndexErrorOf
        (elaborateNumberSemanticIndexSource stringModel ["Order"] (authored 5)) =
          some (.indexFieldNotNumber ["Order", "Items", "LineNo"]) := by
  native_decide

/- General model validation retains a nested index declaration; only this one-level consumer rejects its wider scope. -/
example :
    let sections : RepeatableGroupDecl := {
      level := 5, path := ["Order", "Sections"]
    }
    let nestedItems : RepeatableGroupDecl := {
      items with path := ["Order", "Sections", "Items"]
    }
    let nestedKey := {
      keyDecl with groupPath := nestedItems.path, repeatableScope := [5, 10]
    }
    let nestedTarget := {
      targetDecl with groupPath := nestedItems.path, repeatableScope := [5, 10]
    }
    let nestedModel : FlatModel := {
      fields := [nestedKey, nestedTarget]
      repeatableGroups := [sections, nestedItems]
    }
    let nestedAuthored : SurfaceNumberSemanticIndex := {
      target := { base := .absolute, groups := nestedItems.path, field := "Amount" }
      key := 5
    }
    nestedModel.validate.isOk = true ∧
      (elaborateNumberSemanticIndexSource nestedModel ["Order"] nestedAuthored).isOk = false := by
  native_decide

end A12Kernel
