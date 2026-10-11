import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm

/-- Run the complete model or refuse before execution. Dropping a refused producer would expose
its stale stored value; dropping another declaration for the same target would truncate its
alternative table (spec/09 §§1, 3.1). `runComputations`
remains a fragment evaluator and cannot certify completeness against a DM model. -/
def runModelComputations (model : DmModel) (language : Language) (world : World)
    (prepared : PreparedFlatStringContext model.flat compilePattern)
    (checked : CheckedDocument model.flat) : Lowering (List ComputedOutcome) := do
  admitDeclarations model.declarations
  if !model.refusals.isEmpty then
    throw { construct := "ComputationModel", detail := "model contains refused declarations" }
  let lowered ← model.computations.mapM fun computation =>
    (lowerComputation model.flat language computation).map (·.2)
  if lowered.isEmpty then return []
  runComputations world prepared checked lowered

end A12Kernel.Dm
