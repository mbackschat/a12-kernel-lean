import A12Kernel.Elaboration.StringComputationRunPlan

/-! # Checked String-computation table locks

These cases separate model-certified direct-presence guards from unresolved IDs and repeatable fields, retain raw String presence, and lock terminal first-selection before the checked run exists.
-/

namespace A12Kernel.Conformance.StringComputationTable

open A12Kernel

private def source : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Source",
    policy := { kind := .string } }

private def rawGate : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "RawGate",
    policy := { kind := .string }, stringValueMode := .raw,
    stringPolicy := { lineBreaksPermitted := true } }

private def target : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Target",
    policy := { kind := .string } }

private def otherTarget : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "OtherTarget",
    policy := { kind := .string } }

private def repeatedGate : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "RepeatedGate",
    policy := { kind := .string }, repeatableScope := [10] }

private def rulesMarker : FlatFieldDecl :=
  { id := 5, groupPath := ["Rules"], name := "Marker",
    policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [source, rawGate, target, otherTarget, repeatedGate, rulesMarker]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def operation (targetField : FieldId) (expression : StringExpr SurfaceFieldPath String) : Option (CheckedStringComputationOperation model) :=
  (elaborateStringComputationOperation model ["Form"] targetField expression).toOption

private def operationAt (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : StringExpr SurfaceFieldPath String) :
    Option (CheckedStringComputationOperation model) :=
  (elaborateStringComputationOperation model declaringGroup targetField expression).toOption

private def alternative (guard : (CheckedComputationCondition model)) (op : CheckedStringComputationOperation model) :
    CheckedComputationAlternative model (CheckedStringComputationOperation model) :=
  { precondition := guard, operation := op }

private def unguarded (op : CheckedStringComputationOperation model) :
    CheckedComputationAlternative model (CheckedStringComputationOperation model) :=
  { precondition := none, operation := op }

private def tableError
    (alternatives : List (CheckedComputationAlternative model
      (CheckedStringComputationOperation model))) :
    Option StringComputationTableError :=
  match certifyStringComputationTable alternatives with
  | .ok _ => none
  | .error error => some error

private def tableOutcome
    (alternatives : List (CheckedComputationAlternative model
      (CheckedStringComputationOperation model)))
    (context : StringComputationContext) : Option StringTargetOutcome := do
  let table ← (certifyStringComputationTable alternatives).toOption
  (table.evaluateOutcomeWithPattern none context context).toOption

private def tableReferencesField
    (alternatives : List (CheckedComputationAlternative model
      (CheckedStringComputationOperation model)))
    (field : FieldId) : Option Bool := do
  let table ← (certifyStringComputationTable alternatives).toOption
  pure (table.referencesField field)

private def tableDeclaringGroups
    (alternatives : List (CheckedComputationAlternative model
      (CheckedStringComputationOperation model))) : Option (List GroupPath) := do
  let table ← (certifyStringComputationTable alternatives).toOption
  pure table.declaringGroups

private def context (sourceCell rawGateCell : RawCell) :
    StringComputationContext where
  read field :=
    if field == source.id then formalCheck source.policy sourceCell
    else if field == rawGate.id then formalCheck rawGate.policy rawGateCell
    else formalCheck target.policy .empty

private def copySource : CheckedStringComputationOperation model :=
  (operation target.id (.field (bare "Source"))).get (by native_decide)

private def literalFallback : CheckedStringComputationOperation model :=
  (operation target.id (.literal "FALLBACK")).get (by native_decide)

private def otherLiteral : CheckedStringComputationOperation model :=
  (operation otherTarget.id (.literal "OTHER")).get (by native_decide)

private def rulesLiteral : CheckedStringComputationOperation model :=
  (operationAt ["Rules"] target.id (.literal "RULES")).get (by native_decide)

/- Empty tables are unrepresentable after certification. -/
example : tableError [] = some .empty := by
  native_decide

/- Only a sole alternative may omit its precondition. It selects without consulting a malformed field that a fabricated tautological guard would read. -/
example :
    tableOutcome [unguarded copySource]
        (context (.parsed (.str "VALUE")) (.rejected .malformed)) =
      some (.accepted ⟨"VALUE", by decide⟩) ∧
    tableReferencesField [unguarded copySource] source.id = some true ∧
    tableReferencesField [unguarded copySource] rawGate.id = some false ∧
    tableError [unguarded copySource,
      alternative (.fieldNotFilled rawGate.id) literalFallback] =
        some (.unguardedAlternative 1) ∧
    tableError [alternative (.fieldNotFilled rawGate.id) copySource,
      unguarded literalFallback] = some (.unguardedAlternative 2) := by
  native_decide

/- An unresolved guard ID cannot cross the checked table boundary. -/
example :
    tableError [alternative (.fieldFilled 99) copySource] =
      some (.guardNotAdmitted 1) := by
  native_decide

/- The first table admits only nonrepeatable direct-presence guards. -/
example :
    tableError [alternative (.fieldFilled repeatedGate.id) copySource] =
      some (.guardNotAdmitted 1) := by
  native_decide

/- Presence remains legal for a raw String declaration even though value reads are not. -/
example :
    tableOutcome [alternative (.fieldNotFilled rawGate.id) copySource]
      (context (.parsed (.str "VALUE")) .empty) =
        some (.accepted ⟨"VALUE", by decide⟩) := by
  native_decide

/- Guard-side target self-reference fails before evaluation and draws the reference class
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)). -/
example :
    tableError [alternative (.fieldFilled target.id) copySource] =
      some (.guardTargetReference 1) ∧
    (tableError [alternative (.fieldFilled target.id) copySource]).bind (·.diagnostic?) =
      some .errorReferenceToCalculatedField ∧
    (tableError [alternative (.fieldFilled repeatedGate.id) copySource]).bind (·.diagnostic?) =
      none := by
  native_decide

/- Every row must retain the first row's checked target and declaration policy. -/
example :
    tableError
      [alternative (.fieldNotFilled rawGate.id) copySource,
       alternative (.fieldNotFilled rawGate.id) otherLiteral] =
        some (.targetMismatch 2 target.id otherTarget.id) := by
  native_decide

/- Table assembly may erase placement from runtime evaluation, but it retains every authored row's
declaration group for Analyze and Transform consumers, including a cross-group literal. -/
example :
    tableDeclaringGroups
      [alternative (.fieldFilled rawGate.id) copySource,
       alternative (.fieldNotFilled rawGate.id) rulesLiteral] =
      some [["Form"], ["Rules"]] := by
  native_decide

/- Selection is terminal even when the selected copy stores no value. -/
example :
    tableOutcome
      [alternative (.fieldNotFilled rawGate.id) copySource,
       alternative (.fieldNotFilled rawGate.id) literalFallback]
      (context .empty .empty) = some .noValue := by
  native_decide

/- A reached poisoned guard aborts before the later holding literal. -/
example :
    tableOutcome
      [alternative (.fieldFilled rawGate.id) copySource,
       alternative (.fieldNotFilled rawGate.id) literalFallback]
      (context .empty (.rejected .malformed)) =
        some (.poison .malformed) := by
  native_decide

/- A common precondition is no alternative's own guard, and its reads of the target are judged once,
at the first row: two rows without their own refuse as unguarded under any common precondition, one
self-reading included, and a guarded first row or a sole unguarded one meets the common self-read.
The rows measured write a Number target (`self-read-alternative-walk-2026-10-02/static.tsv` C01,
C05, C07, C11); a String target carries the same walk by assumption. -/
example :
    let common (field : FieldId) := some (CheckedComputationCondition.fieldFilled field)
    let error (field : FieldId) alternatives :=
      match certifyStringComputationTable alternatives (common field) with
      | .ok _ => none
      | .error error => some error
    [error source.id [unguarded copySource, unguarded literalFallback],
      error target.id [unguarded copySource, unguarded literalFallback],
      error target.id [alternative (.fieldFilled source.id) copySource, unguarded literalFallback],
      error source.id [unguarded copySource], error target.id [unguarded copySource]] =
      [some (.unguardedAlternative 1), some (.unguardedAlternative 1),
        some (.guardTargetReference 1), none, some (.guardTargetReference 1)] ∧
    (StringComputationTableError.unguardedAlternative 1).diagnostic? = some .errorEmptyPrecondition := by
  native_decide

end A12Kernel.Conformance.StringComputationTable
