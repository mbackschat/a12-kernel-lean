import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LocalizedTextBinding

/-! # Message-free and error-free acceptance of a document

[spec/10 §2](../../../spec/10-validation-and-polarity.md#2-severity-is-metadata) defines both relations
over full validation's message set: every rule of the model, run on the checked document that carries its
generated mandatory findings, plus the built-in findings. Every built-in finding reports ERROR there, so a
cell with any finding rejects the document under both relations, while a rule's message counts against
error-free acceptance only when its own severity is ERROR.

The cell findings stand for the built-in messages; spec/10 §2 grounds that substitution in the fact that
every producer of a not-check-relevant cell reports a built-in finding. The relations are `none` when the
document does not read, a declaration or rule is refused, or the condition language is unknown, so a
caller cannot mistake an unrepresented model for an accepting one. -/

namespace A12Kernel.Dm

/-- A document's standing under spec/10 §2's two acceptance relations. -/
structure SampleAcceptance where
  messageFree : Bool
  errorFree : Bool
  deriving Repr, BEq, DecidableEq

/-- Both acceptance relations of `doc` under `dm` in full validation, rendering messages for `locale`. -/
def sampleAcceptance (world : World) (dm : DmModel) (doc : Lean.Json) (locale : String := "en_US") :
    Option SampleAcceptance := do
  if !dm.refusals.isEmpty then none
  let language ← Language.ofCode? dm.conditionLanguage
  let input ← (readDocument dm doc).toOption
  if !input.refusals.isEmpty then none
  let locale ← (localeKey locale).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared locale input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let builtin := validated.checkedCells.any (!·.cell.findings.isEmpty)
  let messages ← dm.rules.flatMapM fun rule => do
    let checkedRule ← (checkValidationRule dm language rule world).toOption
    (runValidationRule world validated checkedRule).toOption
  pure { messageFree := !builtin && messages.isEmpty
         errorFree := !builtin && messages.all (·.severity != .error) }

end A12Kernel.Dm
