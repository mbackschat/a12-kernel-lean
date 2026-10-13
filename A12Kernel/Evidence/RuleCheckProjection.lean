import Lean.Data.Json
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Elaboration.DeclarationReport

/-! # Retained rule-check observations through the reader and the message checker

Every retained `rule check --message` batch is replayed row by row: the DM reader, the ordinary or
parallel condition check, and the error-text checker over each declared locale's text, composed as the
[declaration report](../Elaboration/DeclarationReport.lean) composes them. A row agrees when the Kernel
refuses wherever the condition is refused here, and otherwise when the classes and the Kernel's own
verdict both agree. Which class a refused condition draws is the condition producers' responsibility
and is not compared here. The Kernel's internal-error class is matched by an unclassed refusal, which
this project deliberately keeps without a class. A row with no Kernel verdict, which the instrument
stopped first, is skipped.

`deferred` names each row whose divergence another obligation owns. A deferred row that agrees fails,
so the list cannot outlive its cause.
-/

namespace A12Kernel.Evidence.RuleCheckProjection

open Lean A12Kernel A12Kernel.Dm

/-- Observation batch, its model and its request file, under the evidence root. -/
def captures : List (String × String × String) := [
  ("captures/comparison-entry-gates/observations.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/comparison-entry-gates/ops.json"),
  ("captures/comparison-entry-gates/observations2.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/comparison-entry-gates/ops2.json"),
  ("captures/comparison-entry-gates/observations3.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/comparison-entry-gates/ops3.json"),
  ("captures/computation-star-binding-gate/obs11.json", "captures/computation-star-binding-gate/StarBinding3_DM.json", "captures/computation-star-binding-gate/ops11.json"),
  ("captures/condition-class-projection-2026-10-01/obs-baseyear-review.json", "captures/condition-class-projection-2026-10-01/OrderBaseYear_DM.json", "captures/condition-class-projection-2026-10-01/ops-baseyear-review.json"),
  ("captures/condition-class-projection-2026-10-01/obs-baseyear.json", "captures/condition-class-projection-2026-10-01/OrderBaseYear_DM.json", "captures/condition-class-projection-2026-10-01/ops-baseyear.json"),
  ("captures/condition-class-projection-2026-10-01/obs-domain-baseyear.json", "captures/condition-class-projection-2026-10-01/OrderBaseYear_DM.json", "captures/condition-class-projection-2026-10-01/ops-domain.json"),
  ("captures/condition-class-projection-2026-10-01/obs-domain.json", "captures/condition-class-projection-2026-10-01/Order_DM.json", "captures/condition-class-projection-2026-10-01/ops-domain.json"),
  ("captures/condition-class-projection-2026-10-01/obs-pairs.json", "captures/condition-class-projection-2026-10-01/Order_DM.json", "captures/condition-class-projection-2026-10-01/ops-pairs.json"),
  ("captures/condition-class-projection-2026-10-01/obs-points.json", "captures/condition-class-projection-2026-10-01/Order_DM.json", "captures/condition-class-projection-2026-10-01/ops-points.json"),
  ("captures/condition-class-projection-2026-10-01/obs-range.json", "captures/condition-class-projection-2026-10-01/OrderBaseYear_DM.json", "captures/condition-class-projection-2026-10-01/ops-range.json"),
  ("captures/condition-class-projection-2026-10-01/obs.json", "captures/condition-class-projection-2026-10-01/Order_DM.json", "captures/condition-class-projection-2026-10-01/ops.json"),
  ("captures/field-value-read-carriers/observations-grid.json", "captures/field-value-read-carriers/Grid25g_DM.json", "captures/field-value-read-carriers/ops-grid.json"),
  ("captures/field-value-read-grid/observations-grid.json", "captures/field-value-read-grid/Grid25f_DM.json", "captures/field-value-read-grid/ops-grid.json"),
  ("captures/field-value-read-grid/observations-grid2.json", "captures/field-value-read-grid/Grid25f_DM.json", "captures/field-value-read-grid/ops-grid2.json"),
  ("captures/field-value-read-predictions/observations-grid2.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid2.json"),
  ("captures/field-value-read-predictions/observations-grid3.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid3.json"),
  ("captures/field-value-read-predictions/observations-grid7.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid7.json"),
  ("captures/field-value-read-predictions/observations-grid8.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid8.json"),
  ("captures/having-admission-order-2026-10-09/observations.json", "captures/having-filter-comparison-and-scope-classes/Probe_DM.json", "captures/having-admission-order-2026-10-09/ops.json"),
  ("captures/having-error-reference-2026-10-09/observations.json", "captures/having-error-reference-2026-10-09/Probe_DM.json", "captures/having-error-reference-2026-10-09/ops.json"),
  ("captures/having-first-field-2026-10-09/observations.json", "captures/having-reference-scope-2026-10-09/Probe_DM.json", "captures/having-first-field-2026-10-09/ops.json"),
  ("captures/having-iteration-guards-2026-10-09/observations.json", "captures/having-reference-scope-2026-10-09/Probe_DM.json", "captures/having-iteration-guards-2026-10-09/ops.json"),
  ("captures/having-number-leaf-grid-2026-10-02/obs-supplement.json", "captures/having-number-leaf-grid-2026-10-02/Hn_DM.json", "captures/having-number-leaf-grid-2026-10-02/ops-supplement.json"),
  ("captures/having-number-leaf-grid-2026-10-02/obs.json", "captures/having-number-leaf-grid-2026-10-02/Hn_DM.json", "captures/having-number-leaf-grid-2026-10-02/ops.json"),
  ("captures/having-reference-scope-2026-10-09/marked-group-observations.json", "captures/having-reference-scope-2026-10-09/Probe_DM.json", "captures/having-reference-scope-2026-10-09/marked-group-ops.json"),
  ("captures/having-reference-scope-2026-10-09/observations.json", "captures/having-reference-scope-2026-10-09/Probe_DM.json", "captures/having-reference-scope-2026-10-09/ops.json"),
  ("captures/message-category-gate-order/observations.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-category-gate-order/ops.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-flat-group.json", "captures/message-decoder-matrix-2026-10-01/ProbeFlat_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-group.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-flat-keyword.json", "captures/message-decoder-matrix-2026-10-01/ProbeFlat_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-keyword.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-flat-name-review.json", "captures/message-decoder-matrix-2026-10-01/ProbeFlat_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-name-review.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-flat-prediction.json", "captures/message-decoder-matrix-2026-10-01/ProbeFlat_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-prediction.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-flat-review.json", "captures/message-decoder-matrix-2026-10-01/ProbeFlat_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-review.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-flat.json", "captures/message-decoder-matrix-2026-10-01/ProbeFlat_DM.json", "captures/message-decoder-matrix-2026-10-01/ops.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-group.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-group.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-keyword.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-keyword.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-name-review.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-name-review.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-prediction.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-prediction.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs-review.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-decoder-matrix-2026-10-01/ops-review.json"),
  ("captures/message-decoder-matrix-2026-10-01/obs.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-decoder-matrix-2026-10-01/ops.json"),
  ("captures/message-index-field-terminal/ops-obs.json", "captures/message-index-field-terminal/Ix_DM.json", "captures/message-index-field-terminal/ops.json"),
  ("captures/message-index-german-suffix-2026-10-02/ops-de-locale-obs.json", "captures/message-index-german-suffix-2026-10-02/IxDeLoc_DM.json", "captures/message-index-german-suffix-2026-10-02/ops-de-locale.json"),
  ("captures/message-index-german-suffix-2026-10-02/ops-en-locale-obs.json", "captures/message-index-german-suffix-2026-10-02/IxEnLoc_DM.json", "captures/message-index-german-suffix-2026-10-02/ops-en-locale.json"),
  ("captures/message-index-german-suffix-2026-10-02/ops-obs.json", "captures/message-index-german-suffix-2026-10-02/IxDe_DM.json", "captures/message-index-german-suffix-2026-10-02/ops.json"),
  ("captures/message-index-terminal-classes/ops-obs.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-index-terminal-classes/ops.json"),
  ("captures/message-keyed-membership-2026-10-13/obs.json", "captures/message-keyed-membership-2026-10-13/Kp_DM.json", "captures/message-keyed-membership-2026-10-13/ops.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-keyed.json", "captures/message-keyed-membership-2026-10-13/Kq_DM.json", "captures/message-keyed-membership-2026-10-13/ops-keyed.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-spelling.json", "captures/message-keyed-membership-2026-10-13/Kq_DM.json", "captures/message-keyed-membership-2026-10-13/ops-spelling.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-group.json", "captures/message-keyed-membership-2026-10-13/Kq_DM.json", "captures/message-keyed-membership-2026-10-13/ops-group.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-extent.json", "captures/message-keyed-membership-2026-10-13/Kq_DM.json", "captures/message-keyed-membership-2026-10-13/ops-extent.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-order.json", "captures/message-keyed-membership-2026-10-13/Kz_DM.json", "captures/message-keyed-membership-2026-10-13/ops-order.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops2-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops2.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops3-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops3.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops4-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops4.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops5-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops5.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops6-obs.json", "captures/message-parameter-iteration-and-encoding-classes/Probe2_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops6.json"),
  ("captures/message-parameter-iteration-and-encoding-classes/ops7-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-parameter-iteration-and-encoding-classes/ops7.json"),
  ("captures/message-parameter-refusal-classes/ops-obs.json", "captures/message-parameter-refusal-classes/Probe_DM.json", "captures/message-parameter-refusal-classes/ops.json"),
  ("captures/message-repertoire-co-reporting/observations.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-repertoire-co-reporting/ops.json"),
  ("captures/message-repertoire-co-reporting/observations2.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/message-repertoire-co-reporting/ops2.json"),
  ("captures/nonrepeatable-index-field-gate/ops-obs.json", "captures/nonrepeatable-index-field-gate/Nrx_DM.json", "captures/nonrepeatable-index-field-gate/ops.json"),
  ("captures/parser-index-and-iteration-classes/obs4.json", "captures/parser-index-and-iteration-classes/IdxProbe_DM.json", "captures/parser-index-and-iteration-classes/ops4.json"),
  ("captures/parser-index-and-iteration-classes/obs5.json", "captures/parser-index-and-iteration-classes/IdxProbe_DM.json", "captures/parser-index-and-iteration-classes/ops5.json"),
  ("captures/parser-static-legality-sweep/ops-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/parser-static-legality-sweep/ops.json"),
  ("captures/parser-static-legality-sweep/ops2-obs.json", "captures/parser-static-legality-sweep/Probe_DM.json", "captures/parser-static-legality-sweep/ops2.json"),
  ("captures/parser-static-legality-sweep/ops3-obs.json", "captures/parser-static-legality-sweep/Probe3_DM.json", "captures/parser-static-legality-sweep/ops3.json"),
  ("captures/selected-typed-comparison-2026-10-09/observations.json", "captures/selected-typed-comparison-2026-10-09/Probe_DM.json", "captures/selected-typed-comparison-2026-10-09/ops.json"),
  ("captures/semantic-index-entry-2026-10-09/observations.json", "captures/selected-typed-comparison-2026-10-09/Probe_DM.json", "captures/semantic-index-entry-2026-10-09/ops.json"),
  ("captures/temporal-extractor-entry/observations.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/temporal-extractor-entry/ops.json"),
  ("captures/temporal-extractor-entry/observations2.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/temporal-extractor-entry/ops2.json"),
  ("captures/unraised-diagnostic-vocabulary/obs.json", "captures/parser-index-and-iteration-classes/IdxProbe_DM.json", "captures/unraised-diagnostic-vocabulary/ops.json")]

/-- Divergent rows and the obligation that owns each. -/
def deferred : List (String × String) := [
  ("comparison-entry-gates/observations.json#groupregex", "host pattern compiler, SG7"),
  ("comparison-entry-gates/observations2.json#violatedcontrol", "host pattern compiler, SG7"),
  ("parser-static-legality-sweep/ops2-obs.json#Q07", "host pattern compiler, SG7"),
  ("parser-static-legality-sweep/ops3-obs.json#R32", "parallel token comparison, K20")]

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

private def argsOf (args : List String) (flag : String) : List String :=
  match args with
  | name :: value :: rest => (if name == flag then [value] else []) ++ argsOf (value :: rest) flag
  | _ => []

private def segments (path : String) : List String := (path.splitOn "/").filter (· != "")

/-- The rule a `rule check` request authors: `--group` defaults to the field's group, and the error
field is addressed relative to it. -/
private def requestedRule (args : List String) : DmRule :=
  let field := segments ((argsOf args "--field").headD "")
  let group := match (argsOf args "--group").head? with
    | some path => segments path
    | none => field.dropLast
  let ups := group.length - (field.length - 1) + 1
  { group, name := "Probe", severity := "ERROR"
    errorEntityRelPath := String.intercalate "/" (List.replicate ups ".." ++ field.drop (field.length - 1))
    errorCode := (argsOf args "--code").headD ""
    condition := (argsOf args "--condition").headD "" }

/-- The written texts, and for each declared locale the request leaves out the instrument's own
parameter-free placeholder, which it supplies rather than leave the locale without a text. -/
private def messageEntries (locales : List String) (args : List String) : List (String × String) :=
  let written := (argsOf args "--message").map fun entry => match entry.splitOn "=" with
    | locale :: text => (locale, String.intercalate "=" text)
    | [] => ("", "")
  (locales.filter (fun locale => !written.any (·.1 == locale))).map (·, "placeholder") ++ written

/-- What this project reports for one admitted declaration: its classes in report order and the
number of refusals that carry no class. -/
private def reported (model : FlatModel) (profile : ValidationMessageKeywordProfile)
    (condition : ValidationMessageCondition model) (locales : List String)
    (entries : List (String × String)) : List String × Nat :=
  let refusals := fun text => validationMessageTemplateRefusals model profile condition text
  let verdicts : DeclarationVerdicts := {
    presence := messagePresence locales entries
    errorText := errorTextClasses locales entries fun text =>
      (refusals text).filterMap (·.namedRuleDiagnostic?) }
  -- The repertoire finding is codeless and stands beside the parameter refusals.
  let unclassed := (errorTextClasses locales entries fun text =>
      [(refusals text).countP (·.namedRuleDiagnostic?.isNone) +
        (firstUnsupportedMessageTemplateCharacter? text).toList.length]).sum
  (verdicts.report.map (·.kernelCode), unclassed)

inductive Outcome where
  | skipped
  | agrees
  | diverges (detail : String)

private def compare (dm : DmModel) (locales : List String) (request observation : Json) : Outcome :=
  match observation.getObjValAs? Bool "valid" with
  | .error _ => .skipped
  | .ok valid =>
  let args := ((request.getObjValAs? (Array String) "args").toOption.getD #[]).toList
  let kernel := ((observation.getObjValAs? (Array String) "codes").toOption.getD #[]).toList.filter
    (!·.startsWith "RK_")
  let language := if dm.conditionLanguage.startsWith "de" then Language.german else .english
  let profile := language.messageKeywordProfile
  let entries := messageEntries locales args
  let rule := requestedRule args
  let outcome := match checkValidationRule dm language rule with
    | .error refusal => if valid then some s!"refused {refusal.construct}" else none
    | .ok checked =>
        let (codes, unclassed) := match checked with
          | .ordinary checked => reported dm.flat profile (.rule checked) locales entries
          | .parallel checked => reported dm.flat profile (.parallel checked rule.group) locales entries
        let internal := (kernel.filter (· == "MVK_INTERNAL_ERROR")).length
        let named := kernel.filter (· != "MVK_INTERNAL_ERROR")
        let sorted := fun (list : List String) => list.mergeSort (· ≤ ·)
        if sorted codes != sorted named || unclassed < internal then some s!"{codes} against {kernel}"
        else if valid != (codes.isEmpty && unclassed == 0) then some s!"verdict {valid}, classes {codes}"
        else none
  match outcome with
  | some detail => .diverges detail
  | none => .agrees

/-- Replay every batch and return the agreeing and skipped row counts. -/
def checkArtifacts (root : System.FilePath) : IO (Nat × Nat) := do
  let mut agreeing := 0
  let mut skipped := 0
  let mut failures : Array String := #[]
  let mut deferredSeen : Array String := #[]
  for (observations, modelPath, requests) in captures do
    let modelJson ← readJson (root / modelPath)
    let some dm := (readModel modelJson).toOption
      | throw (IO.userError s!"{modelPath}: unreadable model")
    let locales := (((modelJson.getObjValD "header").getObjValAs? (Array Json) "locales").toOption.getD #[]).toList.filterMap
      fun locale => (locale.getObjValAs? String "code").toOption
    let batch := ((← readJson (root / observations)).getObjValAs? (Array Json) "observations").toOption.getD #[]
    for request in ((← readJson (root / requests)).getArr?).toOption.getD #[] do
      -- A batch may interleave other verbs; only a rule check is a rule's static verdict.
      if (request.getObjValAs? String "verb").toOption != some "rule" ||
          ((request.getObjValAs? (Array String) "args").toOption.bind (·[0]?)) != some "check" then continue
      let id := (request.getObjValAs? String "id").toOption.getD ""
      let some observation := batch.find? (fun row => (row.getObjValAs? String "id").toOption == some id)
        | continue
      let key := s!"{(observations.drop "captures/".length)}#{id}"
      match compare dm locales request observation, deferred.lookup key with
      | .skipped, _ => skipped := skipped + 1
      | .agrees, none => agreeing := agreeing + 1
      | .agrees, some owner => failures := failures.push s!"{key}: deferred to {owner} but agrees"
      | .diverges _, some _ => deferredSeen := deferredSeen.push key
      | .diverges detail, none => failures := failures.push s!"{key}: {detail}"
  for (key, owner) in deferred do
    if !deferredSeen.contains key then failures := failures.push s!"{key}: deferred to {owner} but not met"
  if !failures.isEmpty then
    throw (IO.userError s!"rule-check observations diverge:
{String.intercalate "
" failures.toList}")
  pure (agreeing, skipped)

end A12Kernel.Evidence.RuleCheckProjection
