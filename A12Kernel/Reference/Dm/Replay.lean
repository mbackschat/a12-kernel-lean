import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Elaboration.ValidationCondition.Omission
import A12Kernel.Elaboration.ValidationMessageRendering

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
  | divergedReferences (lean kernel : List String)
  | refused (refusal : Refusal)
  | runFault (detail : String)
  deriving Repr

/-- A rule's verdict, and separately its fired messages' reference channels, compared only where the
messages themselves matched: the channels are a separate observation of the same messages. -/
structure RuleVerdict where
  rule : DmRule
  status : RuleStatus
  references : Option RuleStatus := none
  deriving Repr

def RuleStatus.tier : RuleStatus → String
  | .matched => "match"
  | .diverged _ _ | .divergedReferences _ _ => "tier1"
  | .refused _ => "tier2"
  | .runFault _ => "fault"

def RuleStatus.detail : RuleStatus → String
  | .matched => ""
  | .diverged lean kernel => s!"Divergence\tlean={lean} kernel={kernel}"
  | .divergedReferences lean kernel => s!"References\tlean={lean} kernel={kernel}"
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

/-- One message's reference channels as the probe reports them: its pointer and type, and the
`referenced` and `fillToFix` pointer sets, each sorted because the Kernel collects them in hash sets. -/
structure ObservedReferences where
  message : ObservedMessage
  referenced : List String
  fillToFix : List String
  deriving Repr, BEq, Inhabited

def ObservedReferences.render (observed : ObservedReferences) : String :=
  s!"{observed.message} referenced={observed.referenced} fillToFix={observed.fillToFix}"

private def sortedSet (pointers : List String) : List String :=
  pointers.eraseDups.mergeSort (compare · · != .gt)

private def observedReferences (model : FlatModel) (message : FlatRuleMessage)
    (references : ValidationMessageReferences) : ObservedReferences :=
  { message := observe model message
    referenced := sortedSet (references.referenced.map (renderPointer model))
    fillToFix := sortedSet (references.fillToFix.map (renderPointer model)) }

/-- Compare the projected channels with the Kernel's as sets, message by message. -/
private def compareReferences (lean kernel : List ObservedReferences) : RuleStatus :=
  let normalize (observed : List ObservedReferences) : List String :=
    (observed.map ObservedReferences.render).mergeSort (fun a b => compare a b != .gt)
  let kernel := kernel.map fun (observed : ObservedReferences) =>
    { observed with referenced := sortedSet observed.referenced, fillToFix := sortedSet observed.fillToFix }
  if normalize lean == normalize kernel then .matched
  else .divergedReferences (normalize lean) (normalize kernel)

/-- Display inputs that render nothing: the replay compares findings, not texts, and the one rendering
outcome that changes a finding, a fault, does not read them. -/
private def blankInputs : ValidationMessageInputs where
  fieldName := fun _ => { providerResult := none, modelLabel := none, debugDisplay := "" }
  fieldValue := fun _ => { displayValue := none, defaultDisplay := "" }
  fieldStoredToken := fun _ => none
  formPointer := fun _ _ => ""

/-- Each ordinary firing after the request locale's template renders at its row, so a rendering fault
reports as the Kernel reports it. A rule without a template in that locale, or with one this theory
refuses, keeps its firings, as does a firing whose rendering fails structurally. -/
def renderFirings (prepared : PreparedFlatStringContext model compilePattern) (language : Language)
    (locale : String) (document : CheckedDocument model) (definition : DmRule)
    (rule : CheckedResolvedValidationRule model) (fired : List (Env × FlatRuleMessage)) :
    List (Env × FlatRuleMessage) :=
  match (definition.messages.lookup locale).map
      (elaborateValidationMessageTemplate model language.messageKeywordProfile (.rule rule)) with
  | some (.ok template) =>
      let references := document.applyFullIndexPreliminary.toOption.bind (·.messageReferenceInputs.toOption)
      fired.map fun (environment, message) =>
        let context : ValidationMessageRowContext model compilePattern := {
          environment, document := document.source.toDocument, prepared, locale, references }
        match message.afterRendering (template.toRenderPlanAt context blankInputs) with
        | .ok rendered => (environment, rendered)
        | .error _ => (environment, message)
  | _ => fired

/-- Project every fired message's reference channels at the environment it fired at, with the
message-cache inputs of full validation for selected operands, and compare them as sets. -/
def replayReferences (model : FlatModel) (document : CheckedDocument model)
    (rule : CheckedResolvedValidationRule model) (fired : List (Env × FlatRuleMessage))
    (kernel : List ObservedReferences) : RuleStatus :=
  let repetitionAt := (rule.fullRowsAndRepetitionResults document).toOption.map
    fun (_, results) environment => results.find? (·.row == environment)
  let inputs := (document.applyFullIndexPreliminary.toOption.bind fun preliminary =>
    preliminary.messageReferenceInputs.toOption).map ({ · with repetitionAt })
  match fired.mapM fun (environment, message) =>
      (rule.condition.core.messageReferences message environment inputs).map
        (observedReferences model message) with
  | .error error => .refused { construct := "References", detail := (repr error).pretty }
  | .ok lean => compareReferences lean kernel

/-- The parallel counterpart: each fired row projects its reference channels at its own resolved join
row, so a duplicate side or an unmatched side is pointed at as the error pointer is. -/
def replayParallelReferences (model : FlatModel) (document : CheckedDocument model)
    (rule : CheckedParallelFieldRule model) (kernel : List ObservedReferences) : RuleStatus :=
  match runParallelRuleReferences document rule with
  | .error detail => .runFault detail
  | .ok fired =>
      match fired.mapM fun (message, references) => references.map (observedReferences model message) with
      | .error error => .refused { construct := "References", detail := (repr error).pretty }
      | .ok lean => compareReferences lean kernel

/-- Compare every authored and generated rule of `model` on one checked document against the
Kernel's messages, attributed by code and error field. With `rendering`, an ordinary rule's firings
first pass through `renderFirings` for that prepared context and locale. -/
def replayRules (model : DmModel) (language : Language) (world : World)
    (checked : CheckedDocument model.flat) (kernel : List ObservedMessage)
    (kernelReferences : List ObservedReferences := [])
    (rendering : Option (PreparedFlatStringContext model.flat builtinStringPatternCompiler × String) := none) :
    List RuleVerdict :=
  -- Rules read required-empty cells as formally unavailable (spec/03 §B.2), so they run on the
  -- document carrying full validation's generated `.required` findings.
  let validated := checked.fullValidationDocument
  let rules := validationRules model language
  rules.map fun rule =>
    let attributed (message : ObservedMessage) :=
      message.code == rule.errorCode && unindexedPointer message.pointer == errorFieldPath rule
    let expected := (kernel.filter attributed).mergeSort (compare · · != .gt)
    -- A message names its code and error field, so only two rules sharing both cannot be told apart.
    let shared := (rules.filter fun other =>
      other.errorCode == rule.errorCode && errorFieldPath other == errorFieldPath rule).length > 1
    let checkedRule := if shared then .error { construct := "ErrorCode", detail := s!"{rule.errorCode} is shared" }
      else checkValidationRule model language rule world
    match checkedRule, validated with
    | .error refusal, _ => { rule, status := .refused refusal }
    | .ok _, .error error => { rule, status := .runFault (repr error).pretty }
    | .ok checked', .ok document =>
        let run : Except String (List FlatRuleMessage × Option (List (Env × FlatRuleMessage))) :=
          match checked' with
          | .parallel _ => (runValidationRule world document checked').map (·, none)
          | .ordinary ordinary => (runRuleAt world document ordinary).map fun fired =>
              let fired := match rendering with
                | some (prepared, locale) => renderFirings prepared language locale document rule ordinary fired
                | none => fired
              (fired.map (·.2), some fired)
        match run with
        | .error detail => { rule, status := .runFault detail }
        | .ok (messages, fired) =>
            let actual := (messages.map (observe model.flat)).mergeSort (compare · · != .gt)
            if actual != expected then { rule, status := .diverged actual expected } else
            let references := match checked', fired with
              | .parallel parallel, _ => some (replayParallelReferences model.flat document parallel
                  (kernelReferences.filter (attributed ·.message)))
              | .ordinary ordinary, some fired => some (replayReferences model.flat document ordinary fired
                  (kernelReferences.filter (attributed ·.message)))
              | .ordinary _, none => none
            { rule, status := .matched, references }

end A12Kernel.Dm
