import Lean.Data.Json
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Elaboration.DeclarationReport
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # Retained rule-check observations through the reader and the message checker

Every retained `rule check --message` batch is replayed row by row: the DM reader, the ordinary or
parallel condition check, and the error-text checker over each declared locale's text, composed as the
[declaration report](../Elaboration/DeclarationReport.lean) composes them. A refused condition agrees
when the Kernel refuses it with the class the refusal leads with; a refusal without a class agrees only
with a Kernel verdict naming none but the internal-error class, which this project deliberately keeps
without a class. An admitted condition agrees when the classes and the Kernel's own verdict both agree.
A row with no Kernel verdict, which the instrument stopped first, is skipped. A `computation add` row
is compared through [`checkComputation`](../Reference/Dm/ComputationCheck.lean) the same way, an
admitted computation's generated rule standing as its rule row.

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
  ("captures/computation-message-members-2026-10-13/obs.json", "captures/computation-message-members-2026-10-13/Kc_DM.json", "captures/computation-message-members-2026-10-13/ops.json"),
  ("captures/parallel-custom-condition-2026-10-14/obs.json", "captures/parallel-custom-condition-2026-10-14/Staffing_DM.json", "captures/parallel-custom-condition-2026-10-14/ops.json"),
  ("captures/parallel-instance-leaves-2026-10-14/obs-rule.json", "captures/parallel-instance-leaves-2026-10-14/GuardJoin_DM.json", "captures/parallel-instance-leaves-2026-10-14/ops-rule.json"),
  ("captures/joined-carrier-admission-2026-10-14/obs.json", "captures/joined-carrier-admission-2026-10-14/J_DM.json", "captures/joined-carrier-admission-2026-10-14/ops.json"),
  ("captures/joined-carrier-admission-2026-10-14/obs2.json", "captures/joined-carrier-admission-2026-10-14/J_DM.json", "captures/joined-carrier-admission-2026-10-14/ops2.json"),
  ("captures/joined-carrier-limits-2026-10-14/obs.json", "captures/joined-carrier-limits-2026-10-14/R1_DM.json", "captures/joined-carrier-limits-2026-10-14/ops.json"),
  ("captures/joined-carrier-limits-2026-10-14/obs2.json", "captures/joined-carrier-limits-2026-10-14/R1b_DM.json", "captures/joined-carrier-limits-2026-10-14/ops2.json"),
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
  ("captures/message-keyed-membership-2026-10-13/obs-review.json", "captures/message-keyed-membership-2026-10-13/Kv_DM.json", "captures/message-keyed-membership-2026-10-13/ops-review.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-roots.json", "captures/message-keyed-membership-2026-10-13/Kw_DM.json", "captures/message-keyed-membership-2026-10-13/ops-roots.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-controls-keyed.json", "captures/message-keyed-membership-2026-10-13/Kq_DM.json", "captures/message-keyed-membership-2026-10-13/ops-controls-keyed.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-controls-order.json", "captures/message-keyed-membership-2026-10-13/Kz_DM.json", "captures/message-keyed-membership-2026-10-13/ops-controls-order.json"),
  ("captures/message-keyed-membership-2026-10-13/obs-controls-roots.json", "captures/message-keyed-membership-2026-10-13/Kw_DM.json", "captures/message-keyed-membership-2026-10-13/ops-controls-roots.json"),
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
  ("captures/unraised-diagnostic-vocabulary/obs.json", "captures/parser-index-and-iteration-classes/IdxProbe_DM.json", "captures/unraised-diagnostic-vocabulary/ops.json"),
  ("captures/empty-enumeration-token-2026-10-14/obs.json", "captures/empty-enumeration-token-2026-10-14/EmptyTok_DM.json", "captures/empty-enumeration-token-2026-10-14/ops.json"),
  ("captures/predicate-operand-classes-2026-10-14/obs.json", "captures/predicate-operand-classes-2026-10-14/PredOp_DM.json", "captures/predicate-operand-classes-2026-10-14/ops.json"),
  ("captures/predicate-operand-classes-2026-10-14/obs2.json", "captures/predicate-operand-classes-2026-10-14/PredOp_DM.json", "captures/predicate-operand-classes-2026-10-14/ops2.json"),
  ("captures/having-ordinary-leaves-2026-10-14/obs.json", "captures/having-ordinary-leaves-2026-10-14/R3_DM.json", "captures/having-ordinary-leaves-2026-10-14/ops.json"),
  ("captures/having-ordinary-leaves-2026-10-14/obs2.json", "captures/having-ordinary-leaves-2026-10-14/R3_DM.json", "captures/having-ordinary-leaves-2026-10-14/ops2.json"),
  ("captures/having-ordinary-leaves-2026-10-14/obs3.json", "captures/having-ordinary-leaves-2026-10-14/R3_DM.json", "captures/having-ordinary-leaves-2026-10-14/ops3.json"),
  ("captures/having-ordinary-leaves-2026-10-14/obs4.json", "captures/having-ordinary-leaves-2026-10-14/R3_DM.json", "captures/having-ordinary-leaves-2026-10-14/ops4.json"),
  ("captures/semantic-index-reads-2026-10-14/obs.json", "captures/semantic-index-reads-2026-10-14/R4_DM.json", "captures/semantic-index-reads-2026-10-14/ops.json"),
  ("captures/semantic-index-reads-2026-10-14/obs-b.json", "captures/semantic-index-reads-2026-10-14/R4b_DM.json", "captures/semantic-index-reads-2026-10-14/ops-b.json"),
  ("captures/semantic-index-reads-2026-10-14/obs-d.json", "captures/semantic-index-reads-2026-10-14/R4b_DM.json", "captures/semantic-index-reads-2026-10-14/ops-d.json"),
  ("captures/message-references-2026-10-14/obs.json", "captures/message-references-2026-10-14/R5_DM.json", "captures/message-references-2026-10-14/ops.json"),
  ("captures/expanded-shift-amounts-2026-10-14/obs.json", "captures/expanded-shift-amounts-2026-10-14/R8_DM.json", "captures/expanded-shift-amounts-2026-10-14/ops.json"),
  ("captures/expanded-shift-amounts-2026-10-14/obs2.json", "captures/expanded-shift-amounts-2026-10-14/R8_DM.json", "captures/expanded-shift-amounts-2026-10-14/ops2.json"),
  ("captures/expanded-shift-amounts-2026-10-14/obs3.json", "captures/expanded-shift-amounts-2026-10-14/R8_DM.json", "captures/expanded-shift-amounts-2026-10-14/ops3.json"),
  ("captures/expanded-shift-amounts-2026-10-14/obs-filtered.json", "captures/expanded-shift-amounts-2026-10-14/R8F_DM.json", "captures/expanded-shift-amounts-2026-10-14/ops-filtered.json"),
  ("captures/expanded-shift-amounts-2026-10-14/obs-supplementary.json", "captures/expanded-shift-amounts-2026-10-14/R8S_DM.json", "captures/expanded-shift-amounts-2026-10-14/ops-supplementary.json"),
  ("captures/entity-list-group-gates-2026-10-14/obs.json", "captures/entity-list-group-gates-2026-10-14/R9_DM.json", "captures/entity-list-group-gates-2026-10-14/ops.json"),
  ("captures/filter-suppression-and-row-carriers-2026-10-14/obs.json", "captures/filter-suppression-and-row-carriers-2026-10-14/R11_DM.json", "captures/filter-suppression-and-row-carriers-2026-10-14/ops.json"),
  ("captures/filter-suppression-and-row-carriers-2026-10-14/obs-b.json", "captures/filter-suppression-and-row-carriers-2026-10-14/R11BS_DM.json", "captures/filter-suppression-and-row-carriers-2026-10-14/ops-b.json"),
  ("captures/filter-waiver-carriers-2026-10-14/obs.json", "captures/filter-waiver-carriers-2026-10-14/R11D_DM.json", "captures/filter-waiver-carriers-2026-10-14/ops.json")]

/-- Divergent rows and the obligation that owns each. -/
def deferred : List (String × String) := [
  ("comparison-entry-gates/observations.json#groupregex", "host pattern compiler, SG7"),
  ("comparison-entry-gates/observations2.json#violatedcontrol", "host pattern compiler, SG7"),
  ("parser-static-legality-sweep/ops2-obs.json#Q07", "host pattern compiler, SG7"),
  ("comparison-entry-gates/observations.json#regex", "host pattern compiler, SG7")]

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

/-- The values of `flag`, written either as a separate argument or joined by `=`; the instrument
reads both forms. -/
private def argsOf (args : List String) (flag : String) : List String :=
  match args with
  | name :: rest =>
      let joined := if name.startsWith (flag ++ "=") then [(name.drop (flag.length + 1)).toString] else []
      let separate := match rest with
        | value :: _ => if name == flag then [value] else []
        | [] => []
      joined ++ separate ++ argsOf rest flag
  | [] => []

private def segments (path : String) : List String := (path.splitOn "/").filter (· != "")

/-- The rule a `rule check` request authors: `--group` defaults to the field's group, and the error
field is addressed relative to it. -/
private def requestedRule (args : List String) : DmRule :=
  let field := segments ((argsOf args "--field").headD "")
  let group := match (argsOf args "--group").head? with
    | some path => segments path
    | none => field.dropLast
  -- The path climbs from the rule to the deepest group the declaring group shares with the field, then
  -- descends, so a field below the declaring group keeps its intermediate groups.
  let shared := ((group.zip field.dropLast).takeWhile fun (a, b) => a == b).length
  let ups := group.length - shared + 1
  { group, name := "Probe", severity := "ERROR"
    errorEntityRelPath := String.intercalate "/" (List.replicate ups ".." ++ field.drop shared)
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

/-- The computation a `computation add` spec authors, placed in its `group` or else its computed
field's group, the target addressed from the computation element one level below that group. -/
private def requestedComputation (spec : Json) : DmComputation :=
  let field := segments ((spec.getObjValAs? String "computedField").toOption.getD "")
  let group := match (spec.getObjValAs? String "group").toOption with
    | some path => segments path
    | none => field.dropLast
  -- The path climbs and descends as `requestedRule`'s does, so a target below the declaring group
  -- keeps its intermediate groups.
  let shared := ((group.zip field.dropLast).takeWhile fun (a, b) => a == b).length
  let ups := group.length - shared + 1
  let alternatives := ((spec.getObjValAs? (Array Json) "alternatives").toOption.getD #[]).toList.map
    fun alternative => {
      precondition := (alternative.getObjValAs? String "precondition").toOption
      operation := (alternative.getObjValAs? String "operation").toOption.getD ""
      toleranceRangeOp := (alternative.getObjValAs? String "toleranceRangeOp").toOption }
  { group, name := "Probe", alternatives, errorCodesToSuppress := []
    targetRelPath := String.intercalate "/" (List.replicate ups ".." ++ field.drop shared)
    commonPrecondition := (spec.getObjValAs? String "commonPrecondition").toOption }

/-- A computation spec's written texts, with the instrument's placeholder for each omitted locale. -/
private def specEntries (locales : List String) (spec : Json) : List (String × String) :=
  let written := ((spec.getObjValAs? (Array Json) "messages").toOption.getD #[]).toList.map fun entry =>
    ((entry.getObjValAs? String "locale").toOption.getD "", (entry.getObjValAs? String "text").toOption.getD "")
  (locales.filter (fun locale => !written.any (·.1 == locale))).map (·, "placeholder") ++ written

/-- How one refusal meets the Kernel's verdict and codes, `none` when they agree. -/
private def refusedAgainst (refusal : Refusal) (valid : Bool) (kernel : List String) : Option String :=
  let named := kernel.filter (· != "MVK_INTERNAL_ERROR")
  if valid then some s!"refused {refusal.construct}"
  else match refusal.kernelClass? with
    | some code => if named.contains code then none else some s!"class {code} against {kernel}"
    | none => if named.isEmpty then none else some s!"unclassed {refusal.construct} ({refusal.detail}) against {kernel}"

inductive Outcome where
  | skipped
  | agrees
  | diverges (detail : String)

/-- The Kernel's codes on one row, without the instrument's own `RK_` refusals. -/
private def kernelCodes (observation : Json) : List String :=
  ((observation.getObjValAs? (Array String) "codes").toOption.getD #[]).toList.filter (!·.startsWith "RK_")

/-- The Kernel's verdict on one row, `none` when the instrument stopped before the Kernel answered.
A row's `valid` decides; a computation preview reports only `ok` for an admitted spec, and a failed
preview carrying no Kernel code was refused by the instrument. -/
private def kernelVerdict? (observation : Json) (preview : Bool) : Option Bool :=
  match (observation.getObjValAs? Bool "valid").toOption with
  | some valid => some valid
  | none =>
      if !preview then none else
      match (observation.getObjValAs? Bool "ok").toOption with
      | some true => some true
      | some false => if (kernelCodes observation).isEmpty then none else some false
      | none => none

/-- Compare one declaration with its Kernel verdict: a `rule check` row's own rule, or the rule a
`computation add` row's computation generates, whose message is the computation's. -/
private def compare (dm : DmModel) (locales : List String) (rule : DmRule)
    (entries : List (String × String)) (observation : Json) (preview : Bool) : Outcome :=
  match kernelVerdict? observation preview with
  | none => .skipped
  | some valid =>
  let kernel := kernelCodes observation
  let language := if dm.conditionLanguage.startsWith "de" then Language.german else .english
  let profile := language.messageKeywordProfile
  let outcome := match checkValidationRule dm language rule with
    | .error refusal => refusedAgainst refusal valid kernel
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

/-- Compare one `computation add` row: the computation's own admission first, then the rule it
generates, whose message is the computation's. -/
private def compareComputation (dm : DmModel) (locales : List String) (computation : DmComputation)
    (entries : List (String × String)) (observation : Json) : Outcome :=
  match kernelVerdict? observation true with
  | none => .skipped
  | some valid =>
  let kernel := kernelCodes observation
  let language := if dm.conditionLanguage.startsWith "de" then Language.german else .english
  match checkComputation dm language computation with
  | .error refusal => match refusedAgainst refusal valid kernel with
    | some detail => .diverges detail
    | none => .agrees
  | .ok _ => match computation.generatedRule? language with
    | some rule => compare dm locales rule entries observation true
    | none => .diverges "admitted computation without a generated rule"

/-- Replay every batch and return the agreeing and skipped row counts. -/
def checkArtifacts (root : System.FilePath) : IO (Nat × Nat) := do
  let mut agreeing := 0
  let mut skipped := 0
  let mut failures : Array String := #[]
  let mut deferredSeen : Array String := #[]
  for (observations, modelPath, requests) in captures do
    let modelJson ← match parseModelJson (← IO.FS.readFile (root / modelPath)) with
      | .ok json => pure json
      | .error message => throw (IO.userError s!"{modelPath}: {message}")
    let some dm := (readModel modelJson).toOption
      | throw (IO.userError s!"{modelPath}: unreadable model")
    let locales := (((modelJson.getObjValD "header").getObjValAs? (Array Json) "locales").toOption.getD #[]).toList.filterMap
      fun locale => (locale.getObjValAs? String "code").toOption
    let batch := ((← readJson (root / observations)).getObjValAs? (Array Json) "observations").toOption.getD #[]
    for request in ((← readJson (root / requests)).getArr?).toOption.getD #[] do
      let args := ((request.getObjValAs? (Array String) "args").toOption.getD #[]).toList
      -- A batch may interleave other verbs. A rule check is its rule's static verdict, a computation
      -- preview its computation's.
      let declaration ← match (request.getObjValAs? String "verb").toOption, args with
        | some "rule", "check" :: _ => pure (some (Sum.inl (requestedRule args), messageEntries locales args))
        | some "computation", "add" :: file :: _ => do
            let spec ← readJson ((root / requests).parent.getD root / file)
            pure (some (Sum.inr (requestedComputation spec), specEntries locales spec))
        | _, _ => pure none
      let some (declaration, entries) := declaration | continue
      let id := (request.getObjValAs? String "id").toOption.getD ""
      let some observation := batch.find? (fun row => (row.getObjValAs? String "id").toOption == some id)
        | continue
      let key := s!"{(observations.drop "captures/".length)}#{id}"
      let outcome := match declaration with
        | .inl rule => compare dm locales rule entries observation false
        | .inr computation => compareComputation dm locales computation entries observation
      match outcome, deferred.lookup key with
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
