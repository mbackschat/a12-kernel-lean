import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Replaying one retained observation row through Lean

For one document row this compares, rule by rule, the messages Lean fires against the messages the
Kernel reported under the same code. A rule is the unit of comparison because it is the unit a
divergence is fixed in, and a code the Kernel reports for no rule (a formal check, a mandatory
field) is outside this comparison. Each rule ends in one of the replay's tiers: it matches, it
diverges (tier 1: a different message set), or Lean cannot represent it (tier 2: the refusal names
the construct no carrier admits).
-/

namespace A12Kernel.Dm

inductive RuleStatus
  | matched
  | diverged (lean kernel : List ObservedMessage)
  | refused (refusal : Refusal)
  | runFault (detail : String)
  deriving Repr

structure RuleVerdict where
  rule : DmRule
  status : RuleStatus
  deriving Repr

def RuleStatus.tier : RuleStatus → String
  | .matched => "match"
  | .diverged _ _ => "tier1"
  | .refused _ => "tier2"
  | .runFault _ => "fault"

def RuleStatus.detail : RuleStatus → String
  | .matched => ""
  | .diverged lean kernel => s!"Divergence\tlean={lean} kernel={kernel}"
  | .refused refusal => s!"{refusal.construct}\t{oneLine refusal.detail}"
  | .runFault detail => s!"Fault\t{oneLine detail}"

/-- Compare every rule of `model` on one checked document against the Kernel's messages. -/
def replayRules (model : DmModel) (language : Language) (world : World)
    (checked : CheckedDocument model.flat) (kernel : List ObservedMessage) : List RuleVerdict :=
  -- Authored rules read required-empty cells as formally unavailable (spec/03 §B.2), so they run
  -- on the document carrying full validation's generated `.required` findings.
  let authored := checked.fullRequiredEvaluations.map checked.withRequiredFindings
  model.rules.map fun rule =>
    let expected := (kernel.filter (·.code == rule.errorCode)).mergeSort (compare · · != .gt)
    -- Messages are attributed by code, so a code two rules share cannot be told apart.
    let shared := (model.rules.filter (·.errorCode == rule.errorCode)).length > 1
    let status := if shared then .refused { construct := "ErrorCode", detail := s!"{rule.errorCode} is shared" }
      else match checkValidationRule model language rule world with
      | .error refusal => .refused refusal
      | .ok checked' =>
          match authored with
          | .error error => .runFault (repr error).pretty
          | .ok document =>
          match runValidationRule world document checked' with
          | .error detail => .runFault detail
          | .ok messages =>
              let actual := (messages.map (observe model.flat)).mergeSort (compare · · != .gt)
              if actual == expected then .matched else .diverged actual expected
    { rule, status }

end A12Kernel.Dm
