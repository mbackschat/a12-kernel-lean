import Lean.Data.Json
import A12Kernel.Reference.Dm.SampleAcceptanceCapture

/-! # The accepted-sample controls (Q2-P6) and the severity channel against retained Kernel rows

Each lock compares every row of a retained 31.3.1 capture with the Kernel's acceptance through
[`SampleAcceptanceCapture`](SampleAcceptanceCapture.lean).

The [controls](../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/MANIFEST.sha256) are
three models over one Boolean field `B` carrying the ERROR rules `FieldNotFilled(B)` and `[B] == True`;
`QUnsat_DM.json` adds `[B] == False` as ERROR, `QWarn_DM.json` as WARNING, and `QSat_DM.json` omits it.
Their six documents are exhaustive for these models: `B` is the only field, so a verdict depends only on
`B`'s cell, absent (two spellings), empty, not check-relevant, `true` or `false` (spec/02 §A.3 and §B.2).

The [severity channel](../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/MANIFEST.sha256)
separates a rule's own severity from a built-in finding's: one condition authored as ERROR, WARNING and
INFO, and formal and `mandatoryField` findings on fields whose only rule is INFO or WARNING. -/

namespace A12Kernel.Dm.AcceptedSampleControlLocks

open SampleAcceptanceCapture

/-- `QUnsat_DM.json` accepts no document under either relation. -/
example : agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/QUnsat_DM.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/request-unsat.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/artifact-unsat.json") =
    some (List.replicate 6 (false, false)) := by native_decide

/-- `QSat_DM.json` accepts exactly the `false` document. -/
example : agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/QSat_DM.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/request-sat.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/artifact-sat.json") =
    some [(false, false), (false, false), (false, false), (false, false), (true, true), (false, false)] := by
  native_decide

/-- `QWarn_DM.json` accepts the `false` document error-free only. -/
example : agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/QWarn_DM.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/request-warn.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/artifact-warn.json") =
    some [(false, false), (false, false), (false, false), (false, false), (false, true), (false, false)] := by
  native_decide

/-- On `Sev_DM.json` a WARNING-only row and an INFO-only row are error-free, and the formal row is not. -/
example : agreed (include_str "../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/Sev_DM.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/request.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/artifact.json") =
    some [(true, true), (false, true), (false, false), (false, false), (false, true)] := by native_decide

/-- On `Sev2_DM.json` the ERROR twin rejects, and a formal or `mandatoryField` finding rejects on a field
whose only rule is INFO or WARNING. -/
example : agreed (include_str "../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/Sev2_DM.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/request-isolation.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/artifact-isolation.json") =
    some [(true, true), (false, false), (false, false), (false, false), (false, false)] := by native_decide

end A12Kernel.Dm.AcceptedSampleControlLocks
