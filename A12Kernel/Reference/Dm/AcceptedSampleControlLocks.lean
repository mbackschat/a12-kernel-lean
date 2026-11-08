import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Replay

/-! # The accepted-sample controls (Q2-P6)

The [retained capture](../../../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/MANIFEST.sha256)
holds three DM 29.8.0 models over one root `Probe` with one Boolean field `B`. Each carries the ERROR
rules `FieldNotFilled(B)` and `[B] == True`; `QUnsat_DM` adds `[B] == False` as ERROR, `QWarn_DM` as
WARNING, and `QSat_DM` omits it. Under spec/10 §2's relations `QUnsat_DM` accepts no document,
`QSat_DM` accepts the document holding `false`, and `QWarn_DM` accepts that document only error-free.

The six documents are exhaustive for these models. `B` is the only field, so a document's verdicts
depend only on `B`'s cell, which is absent, empty, not check-relevant, `true` or `false` (spec/02 §A.3
and §B.2); the root missing and the root present without `B` are the two absent spellings, and
`FieldNotFilled` fires on a blank root (spec/03 §A.4). Kernel 31.3.1 gave every row's messages at
a12-dmkits `505683610`, which the replay matches. -/

namespace A12Kernel.Dm.AcceptedSampleControlLocks

open Lean

private def model : FlatModel :=
  { fields := [{ id := 1, name := "B", groupPath := ["Probe"], policy.kind := .boolean }] }

private def world : World := { now := { epochMillis := 0 } }

/-- The capture's documents, in its row order: no root, an empty root, then `B` present-empty, `true`,
`false` and the refused token `maybe`. -/
private def documents : List Json :=
  [Json.mkObj [], Json.mkObj [("Probe", Json.mkObj [])]] ++
    ["", "true", "false", "maybe"].map fun text => Json.mkObj [("Probe", Json.mkObj [("B", .str text)])]

/-- `(message-free, error-free)` for a model whose third rule, `[B] == False`, has severity `third`, or
is absent. A built-in finding is ERROR (spec/10 §2). -/
private def acceptance (third : Option String) (doc : Json) : Option (Bool × Bool) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm doc).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let findings ← (validated.read { field := 1, path := [] }).toOption.map (·.findings.length)
  let rules := [("QNone", "FieldNotFilled(B)", "ERROR"), ("QTrue", "[B] == True", "ERROR")] ++
    (third.map fun severity => ("QFalse", "[B] == False", severity)).toList
  let fired ← rules.mapM fun (code, condition, severity) => do
    let rule : DmRule :=
      { group := ["Probe"], name := code, errorCode := code, errorEntityRelPath := "../B", condition
        severity }
    let checkedRule ← (checkValidationRule dm .english rule world).toOption
    let messages ← (runValidationRule world validated checkedRule).toOption
    pure (messages.map fun _ => severity)
  pure (findings == 0 && fired.flatten.isEmpty, findings == 0 && !fired.flatten.contains "ERROR")

/-- `QUnsat_DM` accepts no document under either relation. -/
example : documents.map (acceptance (some "ERROR")) = List.replicate 6 (some (false, false)) := by
  native_decide

/-- `QSat_DM` accepts exactly the `false` document. -/
example : documents.map (acceptance none) =
    [some (false, false), some (false, false), some (false, false), some (false, false), some (true, true),
      some (false, false)] := by native_decide

/-- `QWarn_DM` accepts the `false` document error-free only. -/
example : documents.map (acceptance (some "WARNING")) =
    [some (false, false), some (false, false), some (false, false), some (false, false), some (false, true),
      some (false, false)] := by native_decide

end A12Kernel.Dm.AcceptedSampleControlLocks
