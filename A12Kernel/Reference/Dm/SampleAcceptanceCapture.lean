import Lean.Data.Json
import A12Kernel.Reference.Dm.SampleAcceptance
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # Sample acceptance against a retained Kernel capture

A retained `:adapter:kernelProbe` capture holds a model, a request whose rows carry inline documents, and an
artifact with each row's messages per engine. These readers compare each row's
[`sampleAcceptance`](SampleAcceptance.lean) with the acceptance the Kernel's messages imply: message-free
when a row has none, error-free when none reports ERROR. The model and documents are the captured bytes,
not transcriptions, and the artifact's severities are the oracle. -/

namespace A12Kernel.Dm.SampleAcceptanceCapture

open Lean

private def world : World := { now := { epochMillis := 0 } }

/-- The acceptance the Kernel's messages imply for one artifact row, `none` when the engines disagree. -/
def kernelAcceptance (row : Json) : Option SampleAcceptance := do
  if (row.getObjValAs? Bool "enginesAgree").toOption != some true then none
  let engines ← (row.getObjValAs? (Array Json) "engines").toOption
  let engine ← engines[0]?
  let messages ← (engine.getObjValAs? (Array Json) "messages").toOption
  let severities := messages.toList.map fun message => (message.getObjValAs? String "severity").toOption
  pure { messageFree := messages.isEmpty, errorFree := severities.all (· != some "ERROR") }

/-- The inline documents of a request's rows, in request order. -/
def requestDocuments (requestText : String) : Option (List Json) := do
  let request ← (Json.parse requestText).toOption
  let requested ← (request.getObjValAs? (Array Json) "rows").toOption
  requested.toList.mapM fun row => (row.getObjVal? "documentInline").toOption

/-- Each request row's Lean and Kernel acceptance, in request order. -/
def rows (modelText requestText artifactText : String) :
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
def agreed (modelText requestText artifactText : String) : Option (List (Bool × Bool)) := do
  let rows ← rows modelText requestText artifactText
  rows.mapM fun (lean, kernel) => do
    let lean ← lean
    let kernel ← kernel
    if lean != kernel then none
    pure (lean.messageFree, lean.errorFree)

end A12Kernel.Dm.SampleAcceptanceCapture
