import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.GeneratedComputationRule

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

/-- The rules full validation runs: the authored ones, then each computation's generated rule. A
computation whose target path has no group-relative reading keeps an unparsable condition, so it is
refused rather than silently dropped. -/
def validationRules (model : DmModel) (language : Language) : List DmRule :=
  model.rules ++ model.computations.map fun computation =>
    (computation.generatedRule? language).getD
      { group := computation.group, name := computation.name, errorEntityRelPath := computation.targetRelPath
        errorCode := computation.name, condition := "(", severity := "ERROR" }

/-- The model path of a rule's error field as an unindexed message pointer spells it. The path is
written relative to the rule element, one level below its declaring group. -/
def errorFieldPath (rule : DmRule) : String :=
  let segments := rule.errorEntityRelPath.splitOn "/"
  let path := if segments.head? == some "" then segments.drop 1 else
    let ups := (segments.takeWhile (· == "..")).length
    rule.group.take (rule.group.length + 1 - ups) ++ segments.drop ups
  "/".intercalate path

/-- A message pointer without its row coordinates or partial-pointer prefix. -/
def unindexedPointer (pointer : String) : String :=
  "/".intercalate (((pointer.splitOn "/").filter (· != "")).map fun segment => (segment.splitOn "[").head!)

private def errorAt (group : GroupPath) (errorEntityRelPath : String) : DmRule :=
  { group, name := "", errorEntityRelPath, errorCode := "", condition := "", severity := "" }

example : errorFieldPath (errorAt ["Form", "Rows"] "../../Total") = "Form/Total" ∧
    errorFieldPath (errorAt ["Form"] "../Rows/X") = "Form/Rows/X" ∧
    unindexedPointer "/Form[1]/Rows[0]/X" = "Form/Rows/X" := by native_decide

/-- Compare every authored and generated rule of `model` on one checked document against the
Kernel's messages, attributed by code and error field. -/
def replayRules (model : DmModel) (language : Language) (world : World)
    (checked : CheckedDocument model.flat) (kernel : List ObservedMessage) : List RuleVerdict :=
  -- Rules read required-empty cells as formally unavailable (spec/03 §B.2), so they run on the
  -- document carrying full validation's generated `.required` findings.
  let validated := checked.fullRequiredEvaluations.map checked.withRequiredFindings
  let rules := validationRules model language
  rules.map fun rule =>
    let attributed (message : ObservedMessage) :=
      message.code == rule.errorCode && unindexedPointer message.pointer == errorFieldPath rule
    let expected := (kernel.filter attributed).mergeSort (compare · · != .gt)
    -- A message names its code and error field, so only two rules sharing both cannot be told apart.
    let shared := (rules.filter fun other =>
      other.errorCode == rule.errorCode && errorFieldPath other == errorFieldPath rule).length > 1
    let status := if shared then .refused { construct := "ErrorCode", detail := s!"{rule.errorCode} is shared" }
      else match checkValidationRule model language rule world with
      | .error refusal => .refused refusal
      | .ok checked' =>
          match validated with
          | .error error => .runFault (repr error).pretty
          | .ok document =>
          match runValidationRule world document checked' with
          | .error detail => .runFault detail
          | .ok messages =>
              let actual := (messages.map (observe model.flat)).mergeSort (compare · · != .gt)
              if actual == expected then .matched else .diverged actual expected
    { rule, status }

end A12Kernel.Dm
