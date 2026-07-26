import A12Kernel.Elaboration.StringComputationTable

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

private def model : FlatModel :=
  { fields := [source, rawGate, target, otherTarget, repeatedGate]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def operation (targetField : FieldId) (expression : StringExpr SurfaceFieldPath) : Option (CheckedStringComputationOperation model) :=
  (elaborateStringComputationOperation model ["Form"] targetField expression).toOption

private def alternative (guard : ComputationCondition) (op : CheckedStringComputationOperation model) :
    ComputationAlternative (CheckedStringComputationOperation model) :=
  { precondition := guard, operation := op }

private def tableError
    (alternatives : List (ComputationAlternative
      (CheckedStringComputationOperation model))) :
    Option StringComputationTableError :=
  match certifyStringComputationTable alternatives with
  | .ok _ => none
  | .error error => some error

private def tableOutcome
    (alternatives : List (ComputationAlternative
      (CheckedStringComputationOperation model)))
    (context : StringComputationContext) : Option StringTargetOutcome := do
  let table ← (certifyStringComputationTable alternatives).toOption
  (table.evaluateOutcomeWithPattern none context).toOption

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

/- Empty guarded tables are unrepresentable after certification. -/
example : tableError [] = some .empty := by
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

/- Guard-side target self-reference fails before evaluation. -/
example :
    tableError [alternative (.fieldFilled target.id) copySource] =
      some (.guardTargetReference 1) := by
  native_decide

/- Every row must retain the first row's checked target and declaration policy. -/
example :
    tableError
      [alternative (.fieldNotFilled rawGate.id) copySource,
       alternative (.fieldNotFilled rawGate.id) otherLiteral] =
        some (.targetMismatch 2 target.id otherTarget.id) := by
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

end A12Kernel.Conformance.StringComputationTable
