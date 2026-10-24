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
  ("captures/field-value-read-predictions/observations-grid.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid.json"),
  ("captures/field-value-read-predictions/observations-grid6.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid6.json"),
  ("captures/parser-index-and-iteration-classes/obs.json", "captures/parser-index-and-iteration-classes/IdxProbe0_DM.json", "captures/parser-index-and-iteration-classes/ops.json"),
  ("captures/parser-index-and-iteration-classes/obs2.json", "captures/parser-index-and-iteration-classes/IdxProbe0_DM.json", "captures/parser-index-and-iteration-classes/ops2.json"),
  ("captures/parser-index-and-iteration-classes/obs3.json", "captures/parser-index-and-iteration-classes/IdxProbe0_DM.json", "captures/parser-index-and-iteration-classes/ops3.json"),
  ("captures/parser-index-and-iteration-classes/obs-spell.json", "captures/parser-index-and-iteration-classes/IdxProbe0_DM.json", "captures/parser-index-and-iteration-classes/ops-spell.json"),
  ("captures/selected-parent-binding/observations.json", "captures/selected-parent-binding/model.json", "captures/selected-parent-binding/ops.json"),
  ("captures/message-group-availability-2026-09-30/obs-1.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-availability-2026-09-30/obs-1.json"),
  ("captures/message-group-availability-2026-09-30/obs-2.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-availability-2026-09-30/obs-2.json"),
  ("captures/message-group-availability-2026-09-30/obs-3.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-availability-2026-09-30/obs-3.json"),
  ("captures/message-group-argument-events-2026-10-01/obs.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-argument-events-2026-10-01/obs.json"),
  ("captures/message-group-argument-events-2026-10-01/obs-2.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-argument-events-2026-10-01/obs-2.json"),
  ("captures/message-group-walk-and-dotted-2026-10-01/obs.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-walk-and-dotted-2026-10-01/obs.json"),
  ("captures/message-group-walk-and-dotted-2026-10-01/obs-2.json", "captures/message-group-availability-2026-09-30/GroupAvail_DM.json", "captures/message-group-walk-and-dotted-2026-10-01/obs-2.json"),
  ("captures/message-name-position-carriers-2026-10-01/obs.json", "captures/message-group-availability-2026-09-30/GroupAvailTwin_DM.json", "captures/message-name-position-carriers-2026-10-01/obs.json"),
  ("captures/message-name-position-carriers-2026-10-01/obs-2.json", "captures/message-group-availability-2026-09-30/GroupAvailTwin_DM.json", "captures/message-name-position-carriers-2026-10-01/obs-2.json"),
  ("captures/message-name-position-carriers-2026-10-01/obs-3.json", "captures/message-group-availability-2026-09-30/GroupAvailTwin_DM.json", "captures/message-name-position-carriers-2026-10-01/obs-3.json"),
  ("captures/message-name-position-refusals-2026-10-01/obs.json", "captures/message-group-availability-2026-09-30/GroupAvailTwin_DM.json", "captures/message-name-position-refusals-2026-10-01/obs.json"),
  ("captures/selected-range-compositions-2026-10-13/static/observations.json", "captures/selected-range-compositions-2026-10-13/static/base-model.json", "captures/selected-range-compositions-2026-10-13/static/observations.json"),
  ("captures/rulegroup-field-fill-2026-10-24/obs.json", "captures/rulegroup-field-fill-2026-10-24/K22rg_DM.json", "captures/rulegroup-field-fill-2026-10-24/ops.json"),
  ("captures/k22-static-classes-2026-10-24/obs.json", "captures/k22-static-classes-2026-10-24/K22s_DM.json", "captures/k22-static-classes-2026-10-24/ops.json"),
  ("captures/k22-join-count-membership-2026-10-24/obs.json", "captures/k22-join-count-membership-2026-10-24/K22r_DM.json", "captures/k22-join-count-membership-2026-10-24/ops.json"),
  ("captures/k22-static-s2-2026-10-24/obs.json", "captures/k22-static-s2-2026-10-24/K22t_DM.json", "captures/k22-static-s2-2026-10-24/ops.json"),
  ("captures/k22-static-s3-2026-10-24/obs.json", "captures/k22-static-s3-2026-10-24/K22t_DM.json", "captures/k22-static-s3-2026-10-24/ops.json"),
  ("captures/k22-static-s4-2026-10-24/obs.json", "captures/k22-static-s4-2026-10-24/K22u_DM.json", "captures/k22-static-s4-2026-10-24/ops.json"),
  ("captures/k22-static-s4-2026-10-24/custom-first-filled/obs.json", "captures/k22-static-s4-2026-10-24/custom-first-filled/K22v_DM.json", "captures/k22-static-s4-2026-10-24/custom-first-filled/ops.json"),
  ("captures/k22-static-s4-2026-10-24/raw-members/obs.json", "captures/k22-static-s4-2026-10-24/custom-first-filled/K22v_DM.json", "captures/k22-static-s4-2026-10-24/raw-members/ops.json"),
  ("captures/k22-static-s5-2026-10-24/obs.json", "captures/k22-static-s4-2026-10-24/K22u_DM.json", "captures/k22-static-s5-2026-10-24/ops.json"),
  ("captures/k22-static-s5-2026-10-24/slots/obs.json", "captures/k22-static-s4-2026-10-24/K22u_DM.json", "captures/k22-static-s5-2026-10-24/slots/ops.json"),
  ("captures/field-value-read-remaining-sites/observations-grid.json", "captures/field-value-read-remaining-sites/Grid25h_DM.json", "captures/field-value-read-remaining-sites/ops-grid.json"),
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
  ("captures/filter-waiver-carriers-2026-10-14/obs.json", "captures/filter-waiver-carriers-2026-10-14/R11D_DM.json", "captures/filter-waiver-carriers-2026-10-14/ops.json"),
  ("captures/handback-rows-2026-10-23/obs-claim-typed-raw.json", "captures/handback-rows-2026-10-23/claim-typed-raw_DM.json", "captures/handback-rows-2026-10-23/ops-claim-typed-raw.json"),
  ("captures/handback-rows-2026-10-23/obs-customer-items.json", "captures/handback-rows-2026-10-23/customer-items_DM.json", "captures/handback-rows-2026-10-23/ops-customer-items.json"),
  ("captures/handback-rows-2026-10-23/obs-customer-marked-items.json", "captures/handback-rows-2026-10-23/customer-marked-items_DM.json", "captures/handback-rows-2026-10-23/ops-customer-marked-items.json"),
  ("captures/handback-rows-2026-10-23/obs-order-group-target.json", "captures/handback-rows-2026-10-23/order-group-target_DM.json", "captures/handback-rows-2026-10-23/ops-order-group-target.json"),
  ("captures/handback-rows-2026-10-23/obs-order-k04-bows.json", "captures/handback-rows-2026-10-23/order-k04-bows_DM.json", "captures/handback-rows-2026-10-23/ops-order-k04-bows.json"),
  ("captures/handback-rows-2026-10-23/obs-order-k04-tags.json", "captures/handback-rows-2026-10-23/order-k04-tags_DM.json", "captures/handback-rows-2026-10-23/ops-order-k04-tags.json"),
  ("captures/handback-rows-2026-10-23/obs-order-k04.json", "captures/handback-rows-2026-10-23/order-k04_DM.json", "captures/handback-rows-2026-10-23/ops-order-k04.json"),
  ("captures/handback-rows-2026-10-23/obs-order-keyed-gates.json", "captures/handback-rows-2026-10-23/order-keyed-gates_DM.json", "captures/handback-rows-2026-10-23/ops-order-keyed-gates.json"),
  ("captures/handback-rows-2026-10-23/obs-order-slots.json", "captures/handback-rows-2026-10-23/order-slots_DM.json", "captures/handback-rows-2026-10-23/ops-order-slots.json"),
  ("captures/handback-rows-2026-10-23/obs-shop-marked-residue.json", "captures/handback-rows-2026-10-23/shop-marked-residue_DM.json", "captures/handback-rows-2026-10-23/ops-shop-marked-residue.json"),
  ("captures/handback-rows-2026-10-23/obs-shop-nested-keys.json", "captures/handback-rows-2026-10-23/shop-nested-keys_DM.json", "captures/handback-rows-2026-10-23/ops-shop-nested-keys.json"),
  ("captures/handback-rows-2026-10-23/obs-shop-shifted-dates.json", "captures/handback-rows-2026-10-23/shop-shifted-dates_DM.json", "captures/handback-rows-2026-10-23/ops-shop-shifted-dates.json"),
  ("captures/handback-rows-2026-10-23/obs-shop-typed-keys.json", "captures/handback-rows-2026-10-23/shop-typed-keys_DM.json", "captures/handback-rows-2026-10-23/ops-shop-typed-keys.json"),
  ("captures/handback-rows-2026-10-23/obs-sup-customer-marked-items.json", "captures/handback-rows-2026-10-23/customer-marked-items_DM.json", "captures/handback-rows-2026-10-23/ops-sup-customer-marked-items.json"),
  ("captures/handback-rows-2026-10-23/obs-binding.json", "captures/handback-rows-2026-10-23/customer-marked-items_DM.json", "captures/handback-rows-2026-10-23/ops-binding.json"),
  ("captures/handback-rows-2026-10-23/obs-rv-customer-marked-items.json", "captures/handback-rows-2026-10-23/customer-marked-items_DM.json", "captures/handback-rows-2026-10-23/ops-rv-customer-marked-items.json"),
  ("captures/handback-rows-2026-10-23/obs-rv-order-k04-tags.json", "captures/handback-rows-2026-10-23/order-k04-tags_DM.json", "captures/handback-rows-2026-10-23/ops-rv-order-k04-tags.json"),
  ("captures/handback-rows-2026-10-23/obs-rv-order-k04-bows.json", "captures/handback-rows-2026-10-23/order-k04-bows_DM.json", "captures/handback-rows-2026-10-23/ops-rv-order-k04-bows.json"),
  ("captures/consumer-readiness-k21-2026-10-23/obs-k21-static.json", "captures/consumer-readiness-k21-2026-10-23/K21_DM.json", "captures/consumer-readiness-k21-2026-10-23/ops-k21-static.json"),
  ("captures/handback-rows-2026-10-23/obs-sup-order-k04-bows.json", "captures/handback-rows-2026-10-23/order-k04-bows_DM.json", "captures/handback-rows-2026-10-23/ops-sup-order-k04-bows.json"),
  ("captures/handback-rows-2026-10-23/obs-sup-order-k04-tags.json", "captures/handback-rows-2026-10-23/order-k04-tags_DM.json", "captures/handback-rows-2026-10-23/ops-sup-order-k04-tags.json"),
  ("captures/handback-rows-2026-10-23/obs-sup-order-keyed-gates.json", "captures/handback-rows-2026-10-23/order-keyed-gates_DM.json", "captures/handback-rows-2026-10-23/ops-sup-order-keyed-gates.json"),
  ("captures/handback-rows-2026-10-23/obs-sup-shop-shifted-dates.json", "captures/handback-rows-2026-10-23/shop-shifted-dates_DM.json", "captures/handback-rows-2026-10-23/ops-sup-shop-shifted-dates.json"),
  ("captures/handback-rows-2026-10-23/obs-sup2-shop-shifted-dates.json", "captures/handback-rows-2026-10-23/shop-shifted-dates_DM.json", "captures/handback-rows-2026-10-23/ops-sup2-shop-shifted-dates.json"),
  ("captures/handback-rows-2026-10-23/dry-run-codes.json", "captures/handback-rows-2026-10-23/order-group-target_DM.json", "captures/handback-rows-2026-10-23/dry-ops-order-group-target.json"),
  ("captures/handback-rows-2026-10-23/dry-run-codes.json", "captures/handback-rows-2026-10-23/order-k04-tags_DM.json", "captures/handback-rows-2026-10-23/dry-ops-order-k04-tags.json"),
  ("captures/handback-rows-2026-10-23/dry-run-codes.json", "captures/handback-rows-2026-10-23/order-k04_DM.json", "captures/handback-rows-2026-10-23/dry-ops-order-k04.json"),
  ("captures/consumer-readiness-k21-2026-10-23/dry-run-codes.json", "captures/consumer-readiness-k21-2026-10-23/K21_DM.json", "captures/consumer-readiness-k21-2026-10-23/dry-ops-k21.json"),
  ("captures/joined-filled-count-2026-10-24/dry-run-codes.json", "captures/handback-rows-2026-10-23/K0607f_DM.json", "captures/joined-filled-count-2026-10-24/dry-ops.json"),
  ("captures/keyed-group-beside-join-2026-10-24/dry-run-codes-keyed.json", "captures/keyed-group-beside-join-2026-10-24/K22k_DM.json", "captures/keyed-group-beside-join-2026-10-24/dry-ops.json"),
  ("captures/keyed-group-beside-join-2026-10-24/dry-run-codes-unkeyed.json", "captures/keyed-group-beside-join-2026-10-24/K22u_DM.json", "captures/keyed-group-beside-join-2026-10-24/dry-ops.json"),
  ("captures/ancestor-starred-group-count-computation/obs-admission.json", "captures/ancestor-starred-group-count-computation/GroupCountAdmission_DM.json", "captures/ancestor-starred-group-count-computation/ops-admission.json"),
  ("captures/ancestor-starred-group-count-separators/obs-admission.json", "captures/ancestor-starred-group-count-separators/GroupCountSeparatorsAdmission_DM.json", "captures/ancestor-starred-group-count-separators/ops-admission.json"),
  ("captures/below-star-group-runtime/obs-admission.json", "captures/starred-group-value-count-classes/ProbeN_DM.json", "captures/below-star-group-runtime/ops-admission.json"),
  ("captures/computation-star-binding-gate/obs.json", "captures/computation-star-binding-gate/StarBinding_DM.json", "captures/computation-star-binding-gate/ops.json"),
  ("captures/computation-star-binding-gate/obs10.json", "captures/computation-star-binding-gate/StarBinding3_DM.json", "captures/computation-star-binding-gate/ops10.json"),
  ("captures/computation-star-binding-gate/obs12-StarBinding3_DM.json", "captures/computation-star-binding-gate/StarBinding3_DM.json", "captures/computation-star-binding-gate/obs12-StarBinding3_DM.json"),
  ("captures/computation-star-binding-gate/obs12-StarBinding4_DM.json", "captures/computation-star-binding-gate/StarBinding4_DM.json", "captures/computation-star-binding-gate/obs12-StarBinding4_DM.json"),
  ("captures/computation-star-binding-gate/obs2.json", "captures/computation-star-binding-gate/StarBinding2_DM.json", "captures/computation-star-binding-gate/ops2.json"),
  ("captures/computation-star-binding-gate/obs3.json", "captures/computation-star-binding-gate/StarBinding2_DM.json", "captures/computation-star-binding-gate/ops3.json"),
  ("captures/computation-star-binding-gate/obs4.json", "captures/computation-star-binding-gate/StarBinding3_DM.json", "captures/computation-star-binding-gate/ops4.json"),
  ("captures/computation-star-binding-gate/obs5.json", "captures/computation-star-binding-gate/StarBinding3_DM.json", "captures/computation-star-binding-gate/ops5.json"),
  ("captures/computation-star-binding-gate/obs6.json", "captures/computation-star-binding-gate/StarBinding3_DM.json", "captures/computation-star-binding-gate/ops6.json"),
  ("captures/computation-star-binding-gate/obs7.json", "captures/computation-star-binding-gate/StarBinding4_DM.json", "captures/computation-star-binding-gate/ops7.json"),
  ("captures/computation-star-binding-gate/obs8-StarBinding4_DM.json", "captures/computation-star-binding-gate/StarBinding4_DM.json", "captures/computation-star-binding-gate/obs8-StarBinding4_DM.json"),
  ("captures/computation-star-binding-gate/obs8-StarBinding5_DM.json", "captures/computation-star-binding-gate/StarBinding5_DM.json", "captures/computation-star-binding-gate/obs8-StarBinding5_DM.json"),
  ("captures/computation-star-binding-gate/obs9.json", "captures/group-count-list-extent/CompGate_DM.json", "captures/computation-star-binding-gate/ops9.json"),
  ("captures/cross-kind-format-runtime-parser/obs-reverse.json", "captures/cross-kind-format-runtime-parser/Rev_DM.json", "captures/cross-kind-format-runtime-parser/ops-reverse.json"),
  ("captures/cross-kind-format-runtime-parser/obs.json", "captures/cross-kind-format-runtime-parser/Kind_DM.json", "captures/cross-kind-format-runtime-parser/ops.json"),
  ("captures/distinct-count-component-omitting-fold/obs.json", "captures/distinct-count-component-omitting-fold/Omit_DM.json", "captures/distinct-count-component-omitting-fold/ops.json"),
  ("captures/distinct-count-group-expansion-fold/obs.json", "captures/distinct-count-group-expansion-fold/Grp_DM.json", "captures/distinct-count-group-expansion-fold/ops.json"),
  ("captures/distinct-count-temporal-identity/obs-admission.json", "captures/distinct-count-temporal-identity/Dist_DM.json", "captures/distinct-count-temporal-identity/ops-admission.json"),
  ("captures/distinct-count-time-bearing-fold/obs.json", "captures/distinct-count-time-bearing-fold/Clock_DM.json", "captures/distinct-count-time-bearing-fold/ops.json"),
  ("captures/distinct-count-yearless-and-supplemented-fold/obs-baseyear.json", "captures/distinct-count-yearless-and-supplemented-fold/BaseYear_DM.json", "captures/distinct-count-yearless-and-supplemented-fold/ops-baseyear.json"),
  ("captures/distinct-count-yearless-and-supplemented-fold/obs.json", "captures/distinct-count-yearless-and-supplemented-fold/NoBase_DM.json", "captures/distinct-count-yearless-and-supplemented-fold/ops.json"),
  ("captures/entity-list-gate-denominator-closure/obs.json", "captures/entity-list-gate-denominator-closure/XFmt3_DM.json", "captures/entity-list-gate-denominator-closure/ops.json"),
  ("captures/entity-list-kind-empty-and-root-carriers/obs-star-gate.json", "captures/entity-list-kind-empty-and-root-carriers/ProbeE_DM.json", "captures/entity-list-kind-empty-and-root-carriers/ops-star-gate.json"),
  ("captures/entity-list-kind-empty-and-root-carriers/obs.json", "captures/entity-list-kind-empty-and-root-carriers/ProbeE_DM.json", "captures/entity-list-kind-empty-and-root-carriers/ops.json"),
  ("captures/equal-set-spelling-families-carrier-split/obs-baseyear.json", "captures/equal-set-spelling-families-carrier-split/XFmt2_BaseYear_DM.json", "captures/equal-set-spelling-families-carrier-split/ops-baseyear.json"),
  ("captures/equal-set-spelling-families-carrier-split/obs.json", "captures/equal-set-spelling-families-carrier-split/XFmt2_DM.json", "captures/equal-set-spelling-families-carrier-split/ops.json"),
  ("captures/extrema-component-omitting-fold/obs.json", "captures/extrema-component-omitting-fold/Ext_DM.json", "captures/extrema-component-omitting-fold/ops.json"),
  ("captures/extrema-operand-kind-grid/obs-grid.json", "captures/extrema-operand-kind-grid/Rng_DM.json", "captures/extrema-operand-kind-grid/obs-grid.json"),
  ("captures/field-value-read-predictions/observations-grid4.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid4.json"),
  ("captures/field-value-read-predictions/observations-grid5.json", "captures/field-value-read-predictions/Grid25i_DM.json", "captures/field-value-read-predictions/ops-grid5.json"),
  ("captures/filter-reference-two-levels-above/obs-field-positions.json", "captures/filter-reference-two-levels-above/Rep_DM.json", "captures/filter-reference-two-levels-above/ops-field-positions.json"),
  ("captures/filter-reference-two-levels-above/obs-group-leaf-and-arms.json", "captures/filter-reference-two-levels-above/Rep_DM2.json", "captures/filter-reference-two-levels-above/ops-group-leaf-and-arms.json"),
  ("captures/filter-suppression-and-row-carriers-2026-10-14/obs-c.json", "captures/filter-suppression-and-row-carriers-2026-10-14/R11C_DM.json", "captures/filter-suppression-and-row-carriers-2026-10-14/ops-c.json"),
  ("captures/filter-suppression-and-row-carriers-2026-10-14/obs-k.json", "captures/filter-suppression-and-row-carriers-2026-10-14/R11_DM.json", "captures/filter-suppression-and-row-carriers-2026-10-14/ops-k.json"),
  ("captures/filter-waiver-carriers-2026-10-14/obs-x.json", "captures/filter-waiver-carriers-2026-10-14/R11C_DM.json", "captures/filter-waiver-carriers-2026-10-14/ops-x.json"),
  ("captures/filtered-star-leading-kind/obs.json", "captures/filtered-star-leading-kind/FiltLead_DM.json", "captures/filtered-star-leading-kind/ops.json"),
  ("captures/filtered-star-leading-kind/obs2.json", "captures/filtered-star-leading-kind/FiltLead_DM.json", "captures/filtered-star-leading-kind/ops2.json"),
  ("captures/filtered-star-leading-kind/obs3.json", "captures/filtered-star-leading-kind/FiltLead_DM.json", "captures/filtered-star-leading-kind/ops3.json"),
  ("captures/first-filled-reads-the-format-string/obs.json", "captures/first-filled-reads-the-format-string/XFmt_DM.json", "captures/first-filled-reads-the-format-string/ops.json"),
  ("captures/group-operand-and-short-name-classes/obs-computation.json", "captures/group-operand-and-short-name-classes/ProbeJ_DM.json", "captures/group-operand-and-short-name-classes/ops-computation.json"),
  ("captures/group-operand-and-short-name-classes/obs.json", "captures/group-operand-and-short-name-classes/ProbeJ_DM.json", "captures/group-operand-and-short-name-classes/ops.json"),
  ("captures/iteration-binding-2026-10-23/obs-order-review.json", "captures/iteration-binding-2026-10-23/Order22c_DM.json", "captures/iteration-binding-2026-10-23/ops-order-review.json"),
  ("captures/iteration-binding-2026-10-23/obs-order-review2.json", "captures/iteration-binding-2026-10-23/Order22c_DM.json", "captures/iteration-binding-2026-10-23/ops-order-review2.json"),
  ("captures/iteration-binding-2026-10-23/obs-order.json", "captures/iteration-binding-2026-10-23/Order22c_DM.json", "captures/iteration-binding-2026-10-23/ops-order.json"),
  ("captures/iteration-binding-2026-10-23/obs-plan.json", "captures/iteration-binding-2026-10-23/Plan22c_DM.json", "captures/iteration-binding-2026-10-23/ops-plan.json"),
  ("captures/iteration-binding-2026-10-23/obs-rota-review.json", "captures/iteration-binding-2026-10-23/Rota22c_DM.json", "captures/iteration-binding-2026-10-23/ops-rota-review.json"),
  ("captures/iteration-binding-2026-10-23/obs-rota.json", "captures/iteration-binding-2026-10-23/Rota22c_DM.json", "captures/iteration-binding-2026-10-23/ops-rota.json"),
  ("captures/cross-root-reads-2026-10-24/static-codes.json", "captures/cross-root-reads-2026-10-24/XR_DM.json", "captures/cross-root-reads-2026-10-24/ops.json"),
  ("captures/cross-root-reads-2026-10-24/static-codes2.json", "captures/cross-root-reads-2026-10-24/XR2_DM.json", "captures/cross-root-reads-2026-10-24/ops2.json"),
  ("captures/cross-root-reads-2026-10-24/static-codes3.json", "captures/cross-root-reads-2026-10-24/XR2_DM.json", "captures/cross-root-reads-2026-10-24/ops3.json"),
  ("captures/parallel-custom-condition-reach-2026-10-24/static-codes.json", "captures/parallel-custom-condition-reach-2026-10-24/K22c_DM.json", "captures/parallel-custom-condition-reach-2026-10-24/ops-shapes.json"),
  ("captures/iteration-guard-2026-10-22/obs.json", "captures/iteration-guard-2026-10-22/IterGuard_DM.json", "captures/iteration-guard-2026-10-22/ops.json"),
  ("captures/parallel-instance-leaves-2026-10-14/obs-guard.json", "captures/parallel-instance-leaves-2026-10-14/GuardJoin_DM.json", "captures/parallel-instance-leaves-2026-10-14/ops-guard.json"),
  ("captures/parser-index-and-iteration-classes/obsc.json", "captures/parser-index-and-iteration-classes/IdxProbe_DM.json", "captures/parser-index-and-iteration-classes/opsc.json"),
  ("captures/pattern-and-key-resolver-classes/obs-glfield.json", "captures/pattern-and-key-resolver-classes/ProbeL_DM.json", "captures/pattern-and-key-resolver-classes/ops-glfield.json"),
  ("captures/pattern-and-key-resolver-classes/obs-locus.json", "captures/pattern-and-key-resolver-classes/ProbeL_DM.json", "captures/pattern-and-key-resolver-classes/ops-locus.json"),
  ("captures/pattern-and-key-resolver-classes/obs-review.json", "captures/pattern-and-key-resolver-classes/ProbeL_DM.json", "captures/pattern-and-key-resolver-classes/ops-review.json"),
  ("captures/pattern-and-key-resolver-classes/obs-rnu.json", "captures/pattern-and-key-resolver-classes/ProbeL_DM.json", "captures/pattern-and-key-resolver-classes/ops-rnu.json"),
  ("captures/pattern-and-key-resolver-classes/obs.json", "captures/pattern-and-key-resolver-classes/ProbeL_DM.json", "captures/pattern-and-key-resolver-classes/ops.json"),
  ("captures/resolver-failure-classes-every-carrier/obs-segments.json", "captures/resolver-failure-classes-every-carrier/ProbeE_DM.json", "captures/resolver-failure-classes-every-carrier/ops-segments.json"),
  ("captures/resolver-failure-classes-every-carrier/obs.json", "captures/resolver-failure-classes-every-carrier/ProbeE_DM.json", "captures/resolver-failure-classes-every-carrier/ops.json"),
  ("captures/rounding-argument/observations.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/rounding-argument/ops.json"),
  ("captures/rounding-argument/observations2.json", "captures/arithmetic-shape-gates/Calc_DM.json", "captures/rounding-argument/ops2.json"),
  ("captures/selected-overlap-streams-2026-10-09/observations.json", "captures/selected-overlap-streams-2026-10-09/Probe_DM.json", "captures/selected-overlap-streams-2026-10-09/ops.json"),
  ("captures/selected-typed-comparison-2026-10-09/operand-syntax/observations.json", "captures/selected-typed-comparison-2026-10-09/operand-syntax/Probe_DM.json", "captures/selected-typed-comparison-2026-10-09/operand-syntax/ops.json"),
  ("captures/starred-group-value-count-classes/obs-below.json", "captures/starred-group-value-count-classes/ProbeM_DM.json", "captures/starred-group-value-count-classes/ops-below.json"),
  ("captures/starred-group-value-count-classes/obs-quant.json", "captures/starred-group-value-count-classes/ProbeM_DM.json", "captures/starred-group-value-count-classes/ops-quant.json"),
  ("captures/starred-group-value-count-classes/obs-value-below.json", "captures/starred-group-value-count-classes/ProbeN_DM.json", "captures/starred-group-value-count-classes/ops-value-below.json"),
  ("captures/starred-group-value-count-classes/obs.json", "captures/starred-group-value-count-classes/ProbeM_DM.json", "captures/starred-group-value-count-classes/ops.json"),
  ("captures/starred-path-segment-order/obs.json", "captures/starred-path-segment-order/ProbeI_DM.json", "captures/starred-path-segment-order/ops.json"),
  ("captures/typedef-resolves-to-base-kind/obs.json", "captures/typedef-resolves-to-base-kind/TdBase_DM.json", "captures/typedef-resolves-to-base-kind/ops.json"),
  ("captures/value-list-base-type-cross-pairs/observations-basetype.json", "captures/pattern-comparison-left-kind-gate/Probe4_DM.json", "captures/value-list-base-type-cross-pairs/ops-basetype.json")]

/-- Divergent rows and the obligation that owns each. -/
def deferred : List (String × String) := [
  ("comparison-entry-gates/observations.json#groupregex", "host pattern compiler, SG7"),
  ("comparison-entry-gates/observations2.json#violatedcontrol", "host pattern compiler, SG7"),
  ("parser-static-legality-sweep/ops2-obs.json#Q07", "host pattern compiler, SG7"),
  ("comparison-entry-gates/observations.json#regex", "host pattern compiler, SG7"),
  ("field-value-read-remaining-sites/observations-grid.json#p5", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs.json#pm-ctl", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs.json#pm-ctlrel", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs.json#pm-unique", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs.json#pv-ctl", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs-locus.json#pm-rowlocus", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs-locus.json#pm-rowlocus-abs", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs-review.json#pv-unique", "host pattern compiler, SG7"),
  ("pattern-and-key-resolver-classes/obs-review.json#pv-rowlocus", "host pattern compiler, SG7")]

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

/-- A rule at `group` reporting on the entity at absolute `field`, whose group defaults to the entity's
own group, addressed relative to it. -/
private def ruleAt (field : List String) (group? : Option String) (errorCode condition : String) : DmRule :=
  let group := match group? with
    | some path => segments path
    | none => field.dropLast
  -- The path climbs from the rule to the deepest group the declaring group shares with the field, then
  -- descends, so a field below the declaring group keeps its intermediate groups.
  let shared := ((group.zip field.dropLast).takeWhile fun (a, b) => a == b).length
  let ups := group.length - shared + 1
  { group, name := "Probe", severity := "ERROR", errorCode, condition
    errorEntityRelPath := String.intercalate "/" (List.replicate ups ".." ++ field.drop shared) }

/-- The rule a `rule check` request authors. -/
private def requestedRule (args : List String) : DmRule :=
  ruleAt (segments ((argsOf args "--field").headD "")) (argsOf args "--group").head?
    ((argsOf args "--code").headD "") ((argsOf args "--condition").headD "")

/-- The rule a `rule add --dry-run` spec authors; its `field` may name a group. -/
private def specRule (spec : Json) : DmRule :=
  ruleAt (segments ((spec.getObjValAs? String "field").toOption.getD "")) (spec.getObjValAs? String "group").toOption
    ((spec.getObjValAs? String "code").toOption.getD "") ((spec.getObjValAs? String "condition").toOption.getD "")

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
    -- This project names the internal-error class where it models the Kernel's defect (rounding
    -- overflow, a raw String's length bound), so that one class agrees with itself.
    | some code => if named.contains code || (code == "MVK_INTERNAL_ERROR" && kernel.contains code) then none
        else some s!"class {code} against {kernel}"
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

/-- A self-contained row is its own `rule check`, its one message in the model's first locale. -/
private def selfContained (locales : List String) (request : Json) :
    Option (Sum DmRule DmComputation × List (String × String)) := do
  let condition ← (request.getObjValAs? String "condition").toOption
  let field := (request.getObjValAs? String "field").toOption.getD ""
  let id := (request.getObjValAs? String "id").toOption.getD ""
  let text := (request.getObjValAs? String "message").toOption.getD ""
  let rule := ruleAt (segments field) (request.getObjValAs? String "group").toOption id condition
  pure (Sum.inl rule, messageEntries locales [s!"--message={locales.headD ""}={text}"])

/-- The root-group element a structured `apply` operation adds, `none` for any other operation. Only
a DateRange field is built: its operation writes its whole type, while a field of another kind takes
instrument defaults the captures do not retain. -/
private def addedElement? (op : Json) : Option (String × Json) := do
  guard ((op.getObjValAs? String "target").toOption == some "field")
  guard ((op.getObjValAs? String "kind").toOption == some "DATERANGE")
  let group ← (op.getObjValAs? String "group").toOption
  let name ← (op.getObjValAs? String "name").toOption
  let range := op.getObjValD "dateRange"
  let format ← (range.getObjValAs? String "format").toOption
  let separator ← (range.getObjValAs? String "separator").toOption
  pure (group, Json.mkObj [("type", "Field"), ("id", Json.str s!"{group}/{name}"), ("name", Json.str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "DateRangeType"),
      ("DateRangeType", Json.mkObj [("format", Json.str format), ("rangeSeparator", Json.str separator)])])])])

/-- `model` with `element` appended to the root group `group`. -/
private def appendToRootGroup (model : Json) (group : String) (element : Json) : Json :=
  let roots := ((model.getObjValD "content").getObjValD "modelRoot").getObjValD "rootGroups"
  let roots := (roots.getArr?.toOption.getD #[]).map fun root =>
    if (root.getObjValAs? String "id").toOption != some group then root else
    let body := root.getObjValD "Group"
    root.setObjVal! "Group" (body.setObjVal! "elements"
      (Json.arr (((body.getObjValAs? (Array Json) "elements").toOption.getD #[]).push element)))
  let modelRoot := ((model.getObjValD "content").getObjValD "modelRoot").setObjVal! "rootGroups" (Json.arr roots)
  model.setObjVal! "content" ((model.getObjValD "content").setObjVal! "modelRoot" modelRoot)

/-- A model and the locales its header declares, after the elements `added` places in root groups. -/
private def loadModel (path : System.FilePath) (added : List (String × Json) := []) :
    IO (DmModel × List String) := do
  let modelJson ← match parseModelJson (← IO.FS.readFile path) with
    | .ok json => pure (added.foldl (fun model (group, element) => appendToRootGroup model group element) json)
    | .error message => throw (IO.userError s!"{path}: {message}")
  let some dm := (readModel modelJson).toOption
    | throw (IO.userError s!"{path}: unreadable model")
  pure (dm, (((modelJson.getObjValD "header").getObjValAs? (Array Json) "locales").toOption.getD #[]).toList.filterMap
    fun locale => (locale.getObjValAs? String "code").toOption)

/-- Replay every batch and return the agreeing and skipped row counts. -/
def checkArtifacts (root : System.FilePath) : IO (Nat × Nat) := do
  let mut agreeing := 0
  let mut skipped := 0
  let mut failures : Array String := #[]
  let mut deferredSeen : Array String := #[]
  for (observations, modelPath, requests) in captures do
    let (batchModel, batchLocales) ← loadModel (root / modelPath)
    -- A dry-run batch retains only each row's verdict and Kernel codes, keyed by row id, since the
    -- instrument's envelope renders the Kernel's messages.
    let retained ← readJson (root / observations)
    let batch := match retained.getObjValAs? (Array Json) "observations", retained.getObjVal? "rows" with
      | .ok rows, _ => rows
      | .error _, .ok (.obj rows) => rows.foldl (init := #[]) fun batch (id : String) (row : Json) => batch.push (Json.mkObj
          [("id", Json.str id), ("valid", row.getObjValD "admitted"), ("codes", row.getObjValD "codes")])
      -- A structured `apply` packet retains one row per case.
      | .error _, _ => (retained.getArr?.toOption.getD #[]).map fun (row : Json) => Json.mkObj
          [("id", row.getObjValD "case"), ("valid", row.getObjValD "admitted"), ("codes", row.getObjValD "codes")]
    let requestRows := match (← readJson (root / requests)) with
      | .arr rows => rows
      | json => (json.getObjValAs? (Array Json) "observations").toOption.getD #[]
    for request in requestRows do
      let args := ((request.getObjValAs? (Array String) "args").toOption.getD #[]).toList
      -- A structured `apply` case is its `<case>-spec.json`: field additions, then the computation.
      let applyOps ← match (request.getObjValAs? String "case").toOption with
        | some case => do
            let spec ← readJson ((root / requests).parent.getD root / s!"{case}-spec.json")
            pure (some (spec.getArr?.toOption.getD #[]).toList)
        | none => pure none
      let fieldAdds := (applyOps.getD []).filter fun op => (op.getObjValAs? String "target").toOption == some "field"
      let added := fieldAdds.filterMap addedElement?
      if added.length != fieldAdds.length then continue
      -- A row may name its own model, with the instrument's `-m` or a self-contained row's `model`:
      -- a file beside the request file, or else beside the batch's model.
      let (dm, locales) ← match argsOf args "-m" ++ (request.getObjValAs? String "model").toOption.toList with
        | file :: _ =>
            let beside := (root / requests).parent.getD root / file
            loadModel (if ← beside.pathExists then beside else (root / modelPath).parent.getD root / file)
        | [] => if added.isEmpty then pure (batchModel, batchLocales) else loadModel (root / modelPath) added
      -- A batch may interleave other verbs. A rule check is its rule's static verdict, a computation
      -- preview its computation's.
      let declaration ← match (request.getObjValAs? String "verb").toOption, args with
        | some "rule", "check" :: _ => pure (some (Sum.inl (requestedRule args), messageEntries locales args))
        | some "rule", "add" :: "--dry-run" :: file :: _ => do
            let spec ← readJson ((root / requests).parent.getD root / file)
            pure (some (Sum.inl (specRule spec), specEntries locales spec))
        | some "computation", "add" :: "--dry-run" :: file :: _ | some "computation", "add" :: file :: _ => do
            let spec ← readJson ((root / requests).parent.getD root / file)
            pure (some (Sum.inr (requestedComputation spec), specEntries locales spec))
        | none, [] =>
          if let some ops := applyOps then
            pure ((ops.find? fun op => (op.getObjValAs? String "target").toOption == some "computation").map
              fun op => (Sum.inr (requestedComputation op), specEntries locales op))
          else pure (selfContained locales request)
        | _, _ => pure none
      let some (declaration, entries) := declaration | continue
      let id := ((request.getObjValAs? String "id").toOption <|> (request.getObjValAs? String "case").toOption).getD ""
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
