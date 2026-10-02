import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParserLocks
import A12Kernel.Elaboration.StringContext

/-! # A12Kernel.ReplayMain — replay retained `kernelProbe` requests through Lean

Each argument is a `kernelProbe` request file. The process reads its model, parses every rule
condition and computation text in it, reads every document row, and prints one tab-separated line per
row: the request, the row, the reader's outcome and the share of the model's texts that parsed.
Evaluation and comparison against the retained Kernel artifact follow as the replay grows.
-/

namespace A12Kernel.Replay

open Lean A12Kernel.Dm

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

private def replayRequest (requestPath : System.FilePath) : IO Unit := do
  let request ← readJson requestPath
  let directory := requestPath.parent.getD "."
  let some modelName := (request.getObjValAs? String "model").toOption
    | IO.println s!"{requestPath}\t-\tbad-request\tno model"
  let model ← match readModel (← readJson (directory / modelName)) with
    | .ok model => pure model
    | .error reason => do IO.println s!"{requestPath}\t-\tmodel-error\t{reason}"; return
  let locale := (request.getObjValAs? String "locale").toOption.getD "en_US"
  let texts := model.rules.map (·.condition) ++ model.computations.flatMap fun computation =>
    computation.commonPrecondition.toList ++ computation.alternatives.flatMap fun alternative =>
      alternative.precondition.toList ++ [alternative.operation]
  let parsed := match Language.ofCode? model.conditionLanguage with
    | some language => (texts.filter fun text => (parseText language text).toOption.isSome).length
    | none => 0
  let parseColumn := s!"parsed={parsed}/{texts.length}"
  let world : World := { now := { epochMillis := 0 } }
  let rows := (request.getObjValAs? (Array Json) "rows").toOption.getD #[]
  for row in rows do
    let name := (row.getObjValAs? String "name").toOption.getD "?"
    let document ← match row.getObjVal? "documentInline", row.getObjValAs? String "document" with
      | .ok inline, _ => pure inline
      | _, .ok file => readJson (directory / file)
      | _, _ => do IO.println s!"{requestPath}\t{name}\tbad-row\tno document"; continue
    match readDocument model document with
    | .error reason => IO.println s!"{requestPath}\t{name}\tdocument-error\t{reason}"
    | .ok read =>
        let refused := model.refusals.length + read.refusals.length
        match prepareFlatStringContext world builtinStringPatternCompiler model.flat with
        | .error error => IO.println s!"{requestPath}\t{name}\tprepare-error\t{repr error}"
        | .ok prepared =>
            match checkDocument prepared locale read.data with
            | .ok _ =>
                let reasons := ((model.refusals ++ read.refusals).map (·.2)).eraseDups
                IO.println s!"{requestPath}\t{name}\tchecked\t{parseColumn}\trefusals={refused}\t{"; ".intercalate reasons}"
            | .error error => IO.println s!"{requestPath}\t{name}\tcheck-error\t{(repr error).pretty 200}"

end A12Kernel.Replay

def main (arguments : List String) : IO UInt32 := do
  for argument in arguments do
    try A12Kernel.Replay.replayRequest argument
    catch error => IO.println s!"{argument}\t-\tio-error\t{error}"
  pure 0
