import A12Kernel.Elaboration.StringComputationRun

/-! # Dependency-enabled checked String-run relation

This capsule gives the checked String run an independently meaningful successful-step relation. A step may choose any plan table whose target is still pending and whose statically referenced computed targets are complete. Its label is only the target and rich outcome already observable from that atomic computation. The relation therefore admits independent schedules the fixed executor does not choose without adding a read trace or a generic state-machine framework.
-/

namespace A12Kernel

abbrev StringComputationRunLabel := FieldId × StringTargetOutcome

namespace StringComputationRunState

def targetFields (state : StringComputationRunState) : List FieldId :=
  state.completed.map (·.targetField)

end StringComputationRunState

/-- Every computed target structurally referenced by this table has already completed. The plan graph orders even a reference that runtime short-circuiting may not reach. -/
def StringComputationDependenciesEnabled (run : CheckedStringComputationRun model)
    (table : CheckedStringComputationTable model)
    (state : StringComputationRunState) : Prop :=
  ∀ dependency ∈ run.tables,
    table.referencesField dependency.targetField = true →
      dependency.targetField ∈ state.targetFields

/-- One successful atomic table evaluation chosen independently of the fixed executor's list fold. -/
inductive StringComputationRunStep
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    StringComputationRunState → StringComputationRunLabel →
      StringComputationRunState → Prop where
  | compute
      (table : CheckedStringComputationTable model)
      (member : table ∈ run.tables)
      (pending : table.targetField ∉ state.targetFields)
      (enabled : StringComputationDependenciesEnabled run table state)
      (completion : StringComputationRunCompletion)
      (evaluated : run.evaluateTable patterns input state table = .ok completion) :
      StringComputationRunStep run patterns input state
        (completion.targetField, completion.outcome)
        { completed := state.completed ++ [completion] }

/-- The purpose-specific finite closure used only to state correspondence between successful fixed execution and independent steps. -/
inductive StringComputationRunTrace
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    StringComputationRunState → List StringComputationRunLabel →
      StringComputationRunState → Prop where
  | nil (state) : StringComputationRunTrace run patterns input state [] state
  | cons
      (step : StringComputationRunStep run patterns input state label next)
      (rest : StringComputationRunTrace run patterns input next labels final) :
      StringComputationRunTrace run patterns input state (label :: labels) final

end A12Kernel
