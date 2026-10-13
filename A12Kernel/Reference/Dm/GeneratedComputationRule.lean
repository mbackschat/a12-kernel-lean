import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Print

/-! # The validation rule a computation generates

A computation also acts as a validation rule of one exact generated shape
([spec/09 §6](../../../spec/09-computations.md#6-the-implicit-validation-rule-precisely)): a gate that
the computed field is filled, the common precondition, then either the lone alternative's
precondition and mismatch or the disjunction of every alternative's guarded mismatch. The rule is
declared in the computation's group, anchors at the computed field, and fires under the
computation's own name, so its message type, error pointer and reference channels are the ordinary
rule arm's projections of that condition; peer [KF522](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf522)
measures that the computation-check message's lists follow the rule arm's static selection.

Members are kept as authored text and joined into one condition, as the Kernel parses them in one
text; the line breaks the shape writes are whitespace to the grammar. A computation's suppressed
warnings travel with its generated comparisons.
-/

namespace A12Kernel.Dm

/-- The computed field as its declaring group reads it. The target path is written relative to the
computation element, one level below that group, so a leading `..` is dropped; an absolute path is
kept. Any other spelling has no group-relative reading here. -/
private def generatedTargetReference (language : Language) (computation : DmComputation) :
    Option String := do
  let path ← (parseModelPath language computation.targetRelPath).toOption
  if path.absolute then return printPath language path
  if path.ups == 0 || path.turningPoint.isSome || path.correlated then none
  pure (printPath language { path with ups := path.ups - 1 })

/-- The generated rule of `computation`, or `none` when its target path has no group-relative
reading. -/
def DmComputation.generatedRule? (language : Language) (computation : DmComputation) :
    Option DmRule := do
  let target ← generatedTargetReference language computation
  let and := s!" {keywordSpelling language "And"} "
  let mismatch (alternative : DmAlternative) : String :=
    let op := match alternative.toleranceRangeOp with
      | some name => keywordSpelling language name
      | none => "!="
    s!"[{target}] {op} {alternative.operation}"
  let guarded (alternative : DmAlternative) : String := match alternative.precondition with
    | some precondition => s!"({precondition}\n){and}{mismatch alternative}"
    | none => mismatch alternative
  let common := (computation.commonPrecondition.map fun text => s!"({text}\n){and}").getD ""
  let body ← match computation.alternatives with
    | [] => none
    | [alternative] => pure (guarded alternative)
    | alternatives => pure ("(\n" ++
        s!"\n{keywordSpelling language "Or"}\n".intercalate
          (alternatives.map fun alternative => s!"({guarded alternative}\n)") ++ "\n)")
  let suppression := if computation.errorCodesToSuppress.isEmpty then "" else
    s!"{keywordSpelling language "@SuppressWarning"}({",".intercalate computation.errorCodesToSuppress}) "
  pure {
    group := computation.group, name := computation.name
    errorEntityRelPath := computation.targetRelPath, errorCode := computation.name
    condition := suppression ++
      s!"{keywordSpelling language "FieldFilled"}({target}){and}{common}{body}"
    severity := "ERROR" }

end A12Kernel.Dm
