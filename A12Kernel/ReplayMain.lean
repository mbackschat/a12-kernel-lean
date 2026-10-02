import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.ParserLocks
import A12Kernel.Reference.Dm.ReaderLocks
import A12Kernel.Elaboration.StringContext

/-! # A12Kernel.ReplayMain — replay retained `kernelProbe` requests through Lean

Each argument is a `kernelProbe` request file. The process reads its model and its Kernel artifact
(`artifact<suffix>.json` beside `req<suffix>.json` or `request<suffix>.json`, the suffix led by `-` or `.`), then for every document
row replays every rule and prints one tab-separated line per rule:

`request  row  rule  code  tier  construct  detail`

where `tier` is `match`, `tier1` (Lean fires a different message set), `tier2` (Lean cannot
represent the rule or the document), or `fault` (a structural failure inside Lean). A row whose
document or model cannot be read prints one line with the rule column `-`. The Kernel's first engine
is the reference; a row whose engines disagree is reported as such and not compared.
-/

namespace A12Kernel.Replay

open Lean A12Kernel.Dm

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

/-- `2026-10-02T00:00:00Z` as epoch milliseconds; any other spelling is not a clock. -/
private def clockMillis? (text : String) : Option Int := do
  let [date, time] := text.splitOn "T" | none
  let [year, month, day] := date.splitOn "-" | none
  let [hour, minute, second] := (time.dropRightWhile (· == 'Z')).splitOn ":" | none
  let (y, m, d) := (← year.toInt?, ← month.toInt?, ← day.toInt?)
  -- Days from the civil date by the proleptic Gregorian era formula.
  let y' := if m ≤ 2 then y - 1 else y
  let era := (if y' ≥ 0 then y' else y' - 399) / 400
  let yoe := y' - era * 400
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  let days := era * 146097 + doe - 719468
  pure ((days * 86400 + (← hour.toInt?) * 3600 + (← minute.toInt?) * 60 + (← second.toInt?)) * 1000)

/-- The artifact a request produced: its name with `req` or `request` replaced by `artifact`, the
suffix after the first `-` or `.` kept. -/
private def artifactPath (requestPath : System.FilePath) : System.FilePath :=
  let stem := requestPath.fileStem.getD ""
  let suffix := (stem.dropWhile Char.isAlpha).toString
  (requestPath.parent.getD ".") / s!"artifact{suffix}.json"

private def kernelMessages (row : Json) : Option (Bool × List ObservedMessage) := do
  let engines ← (row.getObjValAs? (Array Json) "engines").toOption
  let first ← engines[0]?
  let messages ← (first.getObjValAs? (Array Json) "messages").toOption
  let agree := (row.getObjValAs? Bool "enginesAgree").toOption.getD true
  pure (agree, messages.toList.filterMap fun message => do
    pure { code := ← (message.getObjValAs? String "code").toOption
           pointer := ← (message.getObjValAs? String "field").toOption
           messageType := ← (message.getObjValAs? String "type").toOption })

private def kernelComputations (row : Json) : Option (List ComputedOutcome) := do
  let engines ← (row.getObjValAs? (Array Json) "engines").toOption
  let first ← engines[0]?
  let computations ← (first.getObjVal? "computations").toOption
  let outcomes ← (computations.getObjValAs? (Array Json) "outcomes").toOption
  pure (outcomes.toList.filterMap fun outcome => do
    let pointer ← (outcome.getObjValAs? String "field").toOption
    let value := (outcome.getObjValAs? String "value").toOption.getD ""
    let text := if (outcome.getObjValAs? Bool "cleared").toOption == some true then "cleared"
      else if (outcome.getObjValAs? Bool "errored").toOption == some true then s!"errored {value}"
      else s!"value {value}"
    pure { pointer, outcome := text })

/-- A pointer without its row indices, the target path it addresses. -/
private def unindexed (pointer : String) : String :=
  "/".intercalate ((pointer.splitOn "/").map fun segment => (segment.splitOn "[").head!)

private def sorted (outcomes : List ComputedOutcome) : List ComputedOutcome :=
  outcomes.mergeSort (compare · · != .gt)

/-- Compare every computation of `model` on one checked document against the Kernel's outcomes,
printing one line per computation through `line`. -/
private def replayComputations (line : String → String → String → String → IO Unit)
    (model : DmModel) (language : Language) (world : World)
    (prepared : PreparedFlatStringContext model.flat compilePattern)
    (checked : CheckedDocument model.flat) (kernel : List ComputedOutcome) : IO Unit := do
  let attempts := model.computations.map fun computation =>
    (computation, lowerComputation model.flat language computation)
  for (computation, attempt) in attempts do
    if let .error refusal := attempt then
      line computation.name "compute" "tier2" s!"{refusal.construct}\t{oneLine refusal.detail}"
  let admitted := attempts.filterMap fun (computation, attempt) =>
    attempt.toOption.map fun (target, lowered) => (computation, target, lowered)
  if admitted.isEmpty then return
  let partial_ := admitted.length != attempts.length
  match runComputations world prepared checked (admitted.map (·.2.2)) with
  | .error refusal =>
      for (computation, _, _) in admitted do
        line computation.name "compute" "tier2" s!"{refusal.construct}\t{oneLine refusal.detail}"
  | .ok outcomes =>
      for (computation, target, _) in admitted do
        let path := "/".intercalate target.path
        let lean := sorted (outcomes.filter (unindexed ·.pointer == path))
        let expected := sorted (kernel.filter (unindexed ·.pointer == path))
        if lean == expected then line computation.name "compute" "match" ""
        else
          -- Beside a refused computation a target may read a stored value the Kernel computed, so the
          -- divergence is not attributable to this computation.
          let tier := if partial_ then "unattributed" else "tier1"
          line computation.name "compute" tier s!"Divergence\tlean={lean} kernel={expected}"

private def replayRequest (requestPath : System.FilePath) : IO Unit := do
  let line (row rule code tier rest : String) :=
    IO.println s!"{requestPath}\t{row}\t{rule}\t{code}\t{tier}\t{rest.replace "\n" " "}"
  let request ← readJson requestPath
  let directory := requestPath.parent.getD "."
  let some modelName := (request.getObjValAs? String "model").toOption
    | line "-" "-" "-" "tier2" "Request\tno model"
  let model ← match readModel (← readJson (directory / modelName)) with
    | .ok model => pure model
    | .error reason => do line "-" "-" "-" "tier2" s!"Model\t{reason}"; return
  let some language := Language.ofCode? model.conditionLanguage
    | line "-" "-" "-" "tier2" s!"Language\t{model.conditionLanguage}"
  let locale := (request.getObjValAs? String "locale").toOption.getD "en_US"
  let clock := ((request.getObjValAs? String "clock").toOption.bind clockMillis?).getD 0
  let world : World := { now := { epochMillis := clock } }
  let artifact ← try pure (some (← readJson (artifactPath requestPath))) catch _ => pure none
  let artifactRows := (artifact.bind fun json => (json.getObjValAs? (Array Json) "rows").toOption).getD #[]
  let prepared ← match prepareFlatStringContext world builtinStringPatternCompiler model.flat with
    | .ok prepared => pure prepared
    | .error error => do line "-" "-" "-" "tier2" s!"Prepare\t{repr error}"; return
  for row in (request.getObjValAs? (Array Json) "rows").toOption.getD #[] do
    let name := (row.getObjValAs? String "name").toOption.getD "?"
    let observedRow := artifactRows.find? fun observed =>
      (observed.getObjValAs? String "name").toOption == some name
    let some (agree, kernel) := observedRow.bind kernelMessages
      | line name "-" "-" "absent" "Artifact\tno retained observation"
    if !agree then line name "-" "-" "fault" "Engines\tthe Kernel's engines disagree"; continue
    let document ← match row.getObjVal? "documentInline", row.getObjValAs? String "document" with
      | .ok inline, _ => pure inline
      | _, .ok file => readJson (directory / file)
      | _, _ => do line name "-" "-" "tier2" "Request\tno document"; continue
    match readDocument model document with
    | .error reason => line name "-" "-" "tier2" s!"Document\t{reason}"
    | .ok read =>
        if let some (path, reason) := read.refusals.head? then
          line name "-" "-" "tier2" s!"Document\t{"/".intercalate path}: {reason}"
          continue
        match checkDocument prepared locale read.data with
        | .error error => line name "-" "-" "tier2" s!"Document\t{(repr error).pretty 200}"
        | .ok checked =>
            for verdict in replayRules model language world checked kernel do
              line name verdict.rule.name verdict.rule.errorCode verdict.status.tier
                verdict.status.detail
            if let some computed := observedRow.bind kernelComputations then
              replayComputations (line name) model language world prepared checked computed

end A12Kernel.Replay

def main (arguments : List String) : IO UInt32 := do
  for argument in arguments do
    try A12Kernel.Replay.replayRequest argument
    catch error => IO.println s!"{argument}\t-\t-\t-\ttier2\tIO\t{(toString error).replace "\n" " "}"
  pure 0
