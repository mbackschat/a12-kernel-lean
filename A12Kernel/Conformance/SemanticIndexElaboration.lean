import A12Kernel.Elaboration.SemanticIndex

/-! # Checked one-group semantic-index conformance

The index field's kind is not narrowed here; the reduced raw-context route's Number requirement is,
and the two are separated below.
-/

namespace A12Kernel

private def keyId : FieldId := 1
private def targetId : FieldId := 2
private def selectorId : FieldId := 3

private def keyField : FlatNumberField := {
  id := keyId
  info := { scale := 2, signed := false }
}

private def targetField : FlatNumberField := {
  id := targetId
  info := { scale := 2, signed := true }
}

private def selectorField : FlatNumberField := {
  id := selectorId
  info := { scale := 2, signed := false }
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

private def selectorDecl : FlatFieldDecl := {
  id := selectorId
  groupPath := ["Order"]
  name := "RequestedLine"
  policy := { kind := .number { scale := 2, signed := false } }
}

private def items : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Items"]
  repeatability := some 20
  indexField := some keyId
}

private def model : FlatModel := {
  fields := [keyDecl, targetDecl, selectorDecl]
  repeatableGroups := [items]
}

private def skuId : FieldId := 4

private def skuDecl : FlatFieldDecl := {
  id := skuId
  groupPath := ["Order", "Items"]
  name := "Sku"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def indexedRuleGroupModel : FlatModel := {
  fields := [skuDecl, targetDecl, selectorDecl]
  repeatableGroups := [{ items with indexField := some skuId }]
}

private def countDecl : FlatFieldDecl := {
  id := 5
  groupPath := ["Order", "Items"]
  name := "Count"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [10]
}

private def unitWeightDecl : FlatFieldDecl := {
  id := 6
  groupPath := ["Order", "Items"]
  name := "UnitWeight"
  policy := { kind := .number { scale := 2, signed := false } }
  repeatableScope := [10]
}

private def indexedFieldCountModel : FlatModel := {
  fields := [skuDecl, countDecl, unitWeightDecl]
  repeatableGroups := [{ items with indexField := some skuId }]
}

private def otherSkuDecl : FlatFieldDecl := {
  id := 7
  groupPath := ["Order", "OtherItems"]
  name := "Sku"
  policy := { kind := .string }
  repeatableScope := [20]
}

private def otherWeightDecl : FlatFieldDecl := {
  id := 8
  groupPath := ["Order", "OtherItems"]
  name := "UnitWeight"
  policy := { kind := .number { scale := 2, signed := false } }
  repeatableScope := [20]
}

private def twoIndexedGroupModel : FlatModel := {
  fields := [skuDecl, countDecl, otherSkuDecl, otherWeightDecl]
  repeatableGroups := [
    { items with indexField := some skuId },
    { level := 20, path := ["Order", "OtherItems"], indexField := some 7 }]
}

private def itemTarget (field : String) : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order", "Items"]
  field
}

private def otherItemTarget (field : String) : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order", "OtherItems"]
  field
}

private def filledFieldSemanticIndexPair :
    SurfaceFilledFieldCountSemanticIndexPair := {
  firstTarget := itemTarget "Count"
  secondTarget := itemTarget "UnitWeight"
  token := "SKU-1"
}

private def ruleGroupSemanticIndex : SurfaceRuleGroupSemanticIndex := {
  token := "SKU-1"
}

private def authored (key : Rat) : SurfaceSemanticIndex := {
  target := {
    base := .absolute
    groups := ["Order", "Items"]
    field := "Amount"
  }
  key := .literal (.number key)
}

private def fieldAuthored : SurfaceSemanticIndex := {
  target := {
    base := .absolute
    groups := ["Order", "Items"]
    field := "Amount"
  }
  key := .field {
    base := .absolute
    groups := ["Order"]
    field := "RequestedLine"
  }
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

private def emptyKeyContext : RawFlatContext := {
  read _ := .empty
}

private def keyContext (raw : RawCell) : RawFlatContext := {
  read id := if id == selectorId then raw else .empty
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

private def checkedRuleGroupSemanticIndex? :
    Option (CheckedRuleGroupSemanticIndexSource indexedRuleGroupModel) :=
  (elaborateRuleGroupSemanticIndexSource indexedRuleGroupModel
    ["Order", "Items"] ruleGroupSemanticIndex).toOption

private def checkedFilledFieldSemanticIndexPair? :
    Option (CheckedFilledFieldCountSemanticIndexPair indexedFieldCountModel) :=
  (elaborateFilledFieldCountSemanticIndexPair indexedFieldCountModel ["Order"]
    filledFieldSemanticIndexPair).toOption

private def filledFieldSemanticIndexPairError? :
    Option FilledFieldCountSemanticIndexPairElabError :=
  match elaborateFilledFieldCountSemanticIndexPair indexedFieldCountModel ["Order"]
      { filledFieldSemanticIndexPair with secondTarget := itemTarget "Count" } with
  | .ok _ => none
  | .error error => some error

private def crossGroupFilledFieldSemanticIndexPairError? :
    Option FilledFieldCountSemanticIndexPairElabError :=
  match elaborateFilledFieldCountSemanticIndexPair twoIndexedGroupModel ["Order"] {
      firstTarget := itemTarget "Count"
      secondTarget := otherItemTarget "UnitWeight"
      token := "SKU-1" } with
  | .ok _ => none
  | .error error => some error

private def checked : CheckedNumberSemanticIndexSource model :=
  {
    toCheckedSemanticIndexSource := {
      group := items
      indexDeclaration := keyDecl
      targetDeclaration := targetDecl
      key := .literal (.number 5)
      modelWellFormed := by native_decide
      groupOwned := by native_decide
      indexDeclared := by native_decide
      indexOwned := by native_decide
      targetOwned := by native_decide
      keyOwned := by native_decide
    }
    indexNumber := by native_decide
    targetNumber := by native_decide
  }

private def fieldChecked : CheckedNumberSemanticIndexSource model :=
  {
    toCheckedSemanticIndexSource := {
      group := items
      indexDeclaration := keyDecl
      targetDeclaration := targetDecl
      key := .field selectorDecl
      modelWellFormed := by native_decide
      groupOwned := by native_decide
      indexDeclared := by native_decide
      indexOwned := by native_decide
      targetOwned := by native_decide
      keyOwned := by native_decide
    }
    indexNumber := by native_decide
    targetNumber := by native_decide
  }

/- The authored route reconstructs that exact checked source from model-owned metadata. -/
example :
    (elaborateNumberSemanticIndexSource model ["Order"] (authored 5)).isOk = true := by
  native_decide

/- The literal suffix selects the containing group through its model-owned index declaration and
retains the exact token for Analyze/Transform consumers. It does not claim a runtime selected row. -/
example : checkedRuleGroupSemanticIndex?.map (fun checked =>
    checked.ruleGroup == ["Order", "Items"] &&
      checked.selection.group.path == ["Order", "Items"] &&
      checked.selection.indexDeclaration == skuDecl &&
      checked.selection.key == .literal (.text "SKU-1")) = some true := by
  native_decide

/- The measured `NumberOfFilledFields` carrier retains the two selected declarations in authored
order and one exact group/index/token identity. Runtime counting is deliberately absent. -/
example : checkedFilledFieldSemanticIndexPair?.map (fun checked =>
    checked.first.targetDeclaration == countDecl &&
      checked.second.targetDeclaration == unitWeightDecl &&
      checked.first.group == checked.second.group &&
      checked.first.indexDeclaration == skuDecl &&
      checked.second.indexDeclaration == skuDecl &&
      checked.first.key == .literal (.text "SKU-1") &&
      checked.second.key == .literal (.text "SKU-1")) = some true := by
  native_decide

/- Reusing one selected target twice is outside the reviewed pair and cannot manufacture a checked
two-field carrier merely because each individual semantic-index source is valid. -/
example : filledFieldSemanticIndexPairError? =
    some (.duplicateTarget countDecl.path) := by
  native_decide

/- Two independently valid selected fields from different indexed groups stay outside the exact
pair carrier instead of being normalized into an unordered model-wide set. -/
example : crossGroupFilledFieldSemanticIndexPairError? =
    some (.differentGroup ["Order", "Items"] ["Order", "OtherItems"]) := by
  native_decide

/- An otherwise present but unindexed containing group reaches the measured semantic-index refusal
rather than silently erasing the suffix into bare `RuleGroup`. -/
example :
    semanticIndexErrorOf
        (elaborateRuleGroupSemanticIndexSource model ["Order"]
          ruleGroupSemanticIndex) =
      some (.missingIndexField ["Order"]) ∧
    (semanticIndexErrorOf
        (elaborateRuleGroupSemanticIndexSource model ["Order"]
          ruleGroupSemanticIndex)).bind
        SemanticIndexElabError.ruleGroupDiagnostic? =
      some .noIndexField ∧
    KernelStaticDiagnostic.noIndexField.kernelCode = "MVK_NO_INDEX_FIELD" := by
  native_decide

/- The suffix does not widen the reserved keyword's surface: bare `RuleGroup` still resolves to the
declaring group, while `RuleGroup*` still reaches its dedicated refusal before semantic indexing. -/
example :
    (match ((.ruleGroup false : SurfaceGroupReference).resolveAgainst ["Order"]),
        ((.ruleGroup true : SurfaceGroupReference).resolveAgainst ["Order"]) with
    | .ok bare, .error starred =>
        bare.path == ["Order"] && bare.origin == .ruleGroup &&
          starred == .wildcardOnRuleGroup
    | _, _ => false) = true := by
  native_decide

/- Numeric key equality is value-based: 5 and 5.00 select the same admitted row. -/
example :
    (checked.lookupValue
      (raw [1, 2]
        (fun row => if row == 1 then .parsed (.num 5.00) else .parsed (.num 6))
        (fun row => if row == 1 then .parsed (.num 7) else .parsed (.num 8)))
      emptyKeyContext .validation).toOption = some (.value (.num 7)) := by
  native_decide

/- A duplicate numeric key excludes every participant and makes validation unresolved. -/
example :
    (checked.lookupValue
      (raw [1, 2]
        (fun _ => .parsed (.num 5))
        (fun row => .parsed (.num row)))
      emptyKeyContext .validation).toOption = some (.unknown .duplicateIndex) := by
  native_decide

/- Validation accepts an unrelated clean match before an invalid key; computation poisons on the column first. -/
example :
    let context := raw [1, 2]
      (fun row => if row == 1 then .parsed (.num 5) else .rejected .malformed)
      (fun row => if row == 1 then .parsed (.num 7) else .parsed (.num 8))
    (checked.lookupValue context emptyKeyContext .validation).toOption =
        some (.value (.num 7)) ∧
      (checked.lookupValue context emptyKeyContext .computation).toOption =
        some (.poison .malformed) := by
  native_decide

/- Empty index cells are auto-required and therefore make the column unavailable. -/
example :
    let context := raw [1]
      (fun _ => .presentEmpty)
      (fun _ => .parsed (.num 7))
    (checked.lookupValue context emptyKeyContext .validation).toOption =
        some (.unknown .required) ∧
      (checked.lookupValue context emptyKeyContext .computation).toOption =
        some (.poison .required) := by
  native_decide

/- A checked clean no-match reaches the established signed Number empty projection and comparison polarity. -/
example :
    let context := raw [1]
      (fun _ => .parsed (.num 6))
      (fun _ => .parsed (.num 8))
    (checked.validationNumberOperand context emptyKeyContext).toOption =
        some (.value 0 (.emptyNumber true)) ∧
      (checked.validationNumberOperand context emptyKeyContext).toOption.map
        (fun operand => NumericComparisonOp.equal.evalFixedRight operand 0) =
          some (.fired .omission) := by
  native_decide

/- The one-group context guard rejects malformed row identity before reading cells. -/
example :
    contextErrorOf (checked.lookupValue
      (raw [1, 1] (fun _ => .parsed (.num 5)) (fun _ => .parsed (.num 7)))
      emptyKeyContext .validation) = some (.topology (.duplicateCandidate 1)) := by
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

private def textAuthored : SurfaceSemanticIndex := {
  target := { base := .absolute, groups := ["Order", "Items"], field := "Amount" }
  key := .literal (.text "L1")
}

/- A **non-Number index** field is admitted by the general route, which is the measured Kernel rule:
the index kind and the selected target's kind are independent. Three rows separate the three
decisions this makes. The literal's identity domain must be the index field's own, so a numeric
literal against a text-identity index is refused rather than silently never matching; and the
**reduced raw-context route** still needs a Number index, because it rebuilds the column from a
one-group scan rather than projecting the shared one. -/
example :
    let stringKey : FlatFieldDecl := {
      keyDecl with policy := { kind := .string }
    }
    let stringModel : FlatModel := { model with fields := [stringKey, targetDecl] }
    stringModel.validate.isOk = true ∧
      (elaborateSemanticIndexSource stringModel ["Order"] textAuthored).isOk = true ∧
      semanticIndexErrorOf
        (elaborateSemanticIndexSource stringModel ["Order"] (authored 5)) =
          some (.indexKeyDomainMismatch ["Order", "Items", "LineNo"] (.number 5)) ∧
      semanticIndexErrorOf
        (elaborateNumberSemanticIndexSource stringModel ["Order"] textAuthored) =
          some (.reducedRouteNeedsNumber ["Order", "Items", "LineNo"]) := by
  native_decide

/- The mirror of the domain gate: a text literal against a **Number** index is refused too, so the
gate is the index's identity rather than a preference for one literal shape. -/
example :
    semanticIndexErrorOf
      (elaborateSemanticIndexSource model ["Order"] textAuthored) =
        some (.indexKeyDomainMismatch ["Order", "Items", "LineNo"] (.text "L1")) := by
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
    let nestedAuthored : SurfaceSemanticIndex := {
      target := { base := .absolute, groups := nestedItems.path, field := "Amount" }
      key := .literal (.number 5)
    }
    nestedModel.validate.isOk = true ∧
      (elaborateNumberSemanticIndexSource nestedModel ["Order"] nestedAuthored).isOk = false := by
  native_decide

/- The same checked source admits a nonrepeatable Number field as the semantic-index key. -/
example :
    (elaborateNumberSemanticIndexSource model ["Order"] fieldAuthored).isOk = true := by
  native_decide

/- A field-valued Number key uses normalized numeric identity just like the literal route. -/
example :
    (fieldChecked.lookupValue
      (raw [1, 2]
        (fun row => if row == 1 then .parsed (.num 5.00) else .parsed (.num 6))
        (fun row => if row == 1 then .parsed (.num 7) else .parsed (.num 8)))
      (keyContext (.parsed (.num 5))) .validation).toOption =
        some (.value (.num 7)) := by
  native_decide

/- An empty field key performs a no-match without bypassing the column policy; on a clean column the target's signed empty policy remains the owner of comparison polarity. -/
example :
    let column := raw [1]
      (fun _ => .parsed (.num 5))
      (fun _ => .parsed (.num 7))
    let unavailableColumn := raw [1, 2]
      (fun row =>
        if row == 1 then .parsed (.num 5) else .rejected .malformed)
      (fun _ => .parsed (.num 7))
    (fieldChecked.lookupValue column (keyContext .presentEmpty) .validation).toOption =
        some .empty ∧
      (fieldChecked.validationNumberOperand column
        (keyContext .presentEmpty)).toOption =
          some (.value 0 (.emptyNumber true)) ∧
      (fieldChecked.lookupValue unavailableColumn
        (keyContext .presentEmpty) .validation).toOption =
          some (.unknown .malformed) ∧
      (fieldChecked.lookupValue unavailableColumn
        (keyContext .presentEmpty) .computation).toOption =
          some (.poison .malformed) := by
  native_decide

/- A formally unavailable key field suppresses validation and poisons computation before row selection. -/
example :
    let column := raw [1]
      (fun _ => .parsed (.num 5))
      (fun _ => .parsed (.num 7))
    let invalidKey := keyContext (.rejected .declaredConstraint)
    (fieldChecked.lookupValue column invalidKey .validation).toOption =
        some (.unknown .declaredConstraint) ∧
      (fieldChecked.lookupValue column invalidKey .computation).toOption =
        some (.poison .declaredConstraint) := by
  native_decide

/- The field-valued route checks the key declaration's Number kind instead of coercing stored text. -/
example :
    let stringSelector := {
      selectorDecl with policy := { kind := .string }
    }
    let stringModel : FlatModel := {
      model with fields := [keyDecl, targetDecl, stringSelector]
    }
    semanticIndexErrorOf
      (elaborateNumberSemanticIndexSource stringModel ["Order"] fieldAuthored) =
        some (.keyFieldNotNumber ["Order", "RequestedLine"]) := by
  native_decide

/- A key field read from inside the indexed group carries its own measured placement class rather
than the generic repeatable-reference one, and projects to the Kernel identifier a checker reports.
The distinction is observable: the two classes would send a consumer to different remedies. -/
example :
    let containedKey : SurfaceSemanticIndex := {
      fieldAuthored with
        key := .field {
          base := .absolute
          groups := ["Order", "Items"]
          field := "LineNo"
        }
    }
    semanticIndexErrorOf
        (elaborateNumberSemanticIndexSource model ["Order"] containedKey) =
      some (.keyContainedInIndexedGroup ["Order", "Items", "LineNo"]
        ["Order", "Items"]) ∧
    (semanticIndexErrorOf
        (elaborateNumberSemanticIndexSource model ["Order"] containedKey)).bind
        SemanticIndexElabError.diagnostic? =
      some .semanticIndexContainedInIndex := by
  native_decide

/- A repeatable key field *outside* the indexed group still requires a row-addressed route, so the
placement class above did not swallow the ordinary nonrepeatable-key boundary. -/
example :
    let otherGroup : RepeatableGroupDecl := {
      level := 11
      path := ["Order", "Notes"]
      repeatability := some 20
      indexField := none
    }
    let noteDecl : FlatFieldDecl := {
      id := 4
      groupPath := ["Order", "Notes"]
      name := "LineNo"
      policy := { kind := .number { scale := 2, signed := false } }
      repeatableScope := [11]
    }
    let twoGroupModel : FlatModel := {
      fields := [keyDecl, targetDecl, selectorDecl, noteDecl]
      repeatableGroups := [items, otherGroup]
    }
    let siblingKey : SurfaceSemanticIndex := {
      fieldAuthored with
        key := .field {
          base := .absolute
          groups := ["Order", "Notes"]
          field := "LineNo"
        }
    }
    semanticIndexErrorOf
      (elaborateNumberSemanticIndexSource twoGroupModel ["Order"] siblingKey) =
        some (.resolve (.repeatableReference ["Order", "Notes", "LineNo"])) := by
  native_decide

end A12Kernel
