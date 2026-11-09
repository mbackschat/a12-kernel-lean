import Lean.Data.Json
import A12Kernel.Reference.Dm.SampleAcceptance
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # The accepted-sample controls (Q2-P6) and the severity channel against retained Kernel rows

Each lock reads a retained 31.3.1 capture's model, request and artifact bytes, computes every row's
[`sampleAcceptance`](SampleAcceptance.lean), and compares it with the acceptance the Kernel's messages
imply: message-free when a row has none, error-free when none reports ERROR. The model and documents are
therefore the captured ones, not transcriptions, and the artifact's severities are the oracle.

The [controls](../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/MANIFEST.sha256) are
three models over one Boolean field `B` carrying the ERROR rules `FieldNotFilled(B)` and `[B] == True`;
`QUnsat_DM.json` adds `[B] == False` as ERROR, `QWarn_DM.json` as WARNING, and `QSat_DM.json` omits it.
Their six documents are exhaustive for these models: `B` is the only field, so a verdict depends only on
`B`'s cell, absent (two spellings), empty, not check-relevant, `true` or `false` (spec/02 §A.3 and §B.2).

The [severity channel](../../../evidence/kernel-31.3.1/captures/severity-channel-2026-11-08/MANIFEST.sha256)
separates a rule's own severity from a built-in finding's: one condition authored as ERROR, WARNING and
INFO, and formal and `mandatoryField` findings on fields whose only rule is INFO or WARNING. -/

namespace A12Kernel.Dm.AcceptedSampleControlLocks

open Lean

private def world : World := { now := { epochMillis := 0 } }

/-- The acceptance the Kernel's messages imply for one artifact row, `none` when the engines disagree. -/
private def kernelAcceptance (row : Json) : Option SampleAcceptance := do
  if (row.getObjValAs? Bool "enginesAgree").toOption != some true then none
  let engines ← (row.getObjValAs? (Array Json) "engines").toOption
  let engine ← engines[0]?
  let messages ← (engine.getObjValAs? (Array Json) "messages").toOption
  let severities := messages.toList.map fun message => (message.getObjValAs? String "severity").toOption
  pure { messageFree := messages.isEmpty, errorFree := severities.all (· != some "ERROR") }

/-- Each request row's Lean and Kernel acceptance, in request order. -/
private def rows (modelText requestText artifactText : String) :
    Option (List (Option SampleAcceptance × Option SampleAcceptance)) := do
  let dm ← ((parseModelJson modelText).bind (readModel ·)).toOption
  let request ← (Json.parse requestText).toOption
  let artifact ← (Json.parse artifactText).toOption
  let locale := (request.getObjValAs? String "locale").toOption.getD "en_US"
  let requested ← (request.getObjValAs? (Array Json) "rows").toOption
  let observed ← (artifact.getObjValAs? (Array Json) "rows").toOption
  requested.toList.mapM fun row => do
    let name ← (row.getObjValAs? String "name").toOption
    let document ← (row.getObjVal? "documentInline").toOption
    let kernel := (observed.find? fun o => (o.getObjValAs? String "name").toOption == some name).bind
      kernelAcceptance
    pure (sampleAcceptance world dm document locale, kernel)

/-- `(message-free, error-free)` per row when every row is decided on both sides and Lean agrees with the
Kernel; `none` otherwise. -/
private def agreed (modelText requestText artifactText : String) : Option (List (Bool × Bool)) := do
  let rows ← rows modelText requestText artifactText
  rows.mapM fun (lean, kernel) => do
    let lean ← lean
    let kernel ← kernel
    if lean != kernel then none
    pure (lean.messageFree, lean.errorFree)

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
