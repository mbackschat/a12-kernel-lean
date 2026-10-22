import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # Retained Number formal observations through the reader

Every row of the retained runtime Number captures is read by the DM reader, and each filled Number
cell's surfaced formal code is recomputed by the one formal cascade from the input the reader
selected: the decimal it converted, or the verbatim text it kept. A row agrees when the codes the
Kernel reports at Number fields are exactly these. A row whose validation faulted in the Kernel agrees
only where the reader refuses its cells as outside the conversion profile, which refuses the scale
that faults rather than answering it.
-/

namespace A12Kernel.Evidence.NumberFormalProjection

open Lean A12Kernel A12Kernel.Dm

/-- A request file and its artifact, under the evidence root. -/
def captures : List (String × String) := [
  ("captures/runtime-formal-number-cascade/request.json", "captures/runtime-formal-number-cascade/artifact.json"),
  ("captures/runtime-formal-number-cascade/request2.json", "captures/runtime-formal-number-cascade/artifact2.json"),
  ("captures/number-ingress-2026-10-13/request.json", "captures/number-ingress-2026-10-13/artifact.json"),
  ("captures/number-ingress-2026-10-13/request-de.json", "captures/number-ingress-2026-10-13/artifact-de.json"),
  ("captures/number-ingress-2026-10-13/request-e.json", "captures/number-ingress-2026-10-13/artifact-e.json"),
  ("captures/number-ingress-2026-10-13/request-f.json", "captures/number-ingress-2026-10-13/artifact-f.json"),
  ("captures/number-ingress-2026-10-13/request-g.json", "captures/number-ingress-2026-10-13/artifact-g.json"),
  ("captures/number-declaration-bounds-2026-10-13/request.json", "captures/number-declaration-bounds-2026-10-13/artifact.json")]

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

/-- Every code the Number cascade can surface, so a Kernel message is attributed to it by code. -/
private def numberCodes : List String :=
  [NumericFormalReadError.leadingPlus, .malformed, .totalDigitsTooLong, .signedZero,
    .negativeNotAllowed, .decimalSeparatorForbidden, .decimalSeparatorRequired,
    .fractionalDigitsOutOfRange, .integerDigitsTooLong, .zeroNotAllowed, .leadingZerosNotAllowed,
    .textTooShort, .textTooLong, .belowMinimum, .aboveMaximum].map (·.errorCode)

/-- The code a filled nonrepeatable Number cell draws from its reader-selected input, keyed by the
pointer the Kernel reports it at. -/
private def leanCodes (model : FlatModel) (cells : List ClassifiedCellInput) : List String :=
  cells.filterMap fun cell => do
    let declaration ← model.fields.find? (·.id == cell.address.field)
    let .number info := declaration.policy.kind | none
    if cell.stored.isEmpty || !cell.address.path.isEmpty then none
    let input := (cell.numericDecimal.map NumericStoredInput.decimal).getD (.text cell.stored)
    match declaration.numericTargetConstraints.checkFormalRead info input with
    | .error error => some s!"{"/".intercalate (declaration.groupPath ++ [declaration.name])}:{error.errorCode}"
    | .ok _ => none

private def kernelCodes (engine : Json) : List String :=
  ((engine.getObjValAs? (Array Json) "messages").toOption.getD #[]).toList.filterMap fun message => do
    let code ← (message.getObjValAs? String "code").toOption
    if !numberCodes.contains code then none
    pure s!"{← (message.getObjValAs? String "field").toOption}:{code}"

/-- The reader's refusal of a scale the Kernel converts and then faults on. -/
private def profileRefusal : String := "exceeds the represented decimal conversion profile"

/-- Replay every row against each engine's observation and return the agreeing observation count and
the number of field codes they compared, faulted observations contributing none. -/
def checkArtifacts (root : System.FilePath) : IO (Nat × Nat) := do
  let mut agreeing := 0
  let mut compared := 0
  let mut failures : Array String := #[]
  for (requestPath, artifactPath) in captures do
    let request ← readJson (root / requestPath)
    let directory := (root / requestPath).parent.getD root
    let some modelName := (request.getObjValAs? String "model").toOption
      | throw (IO.userError s!"{requestPath}: no model")
    let some model := ((parseModelJson (← IO.FS.readFile (directory / modelName))).bind (readModel ·)).toOption
      | throw (IO.userError s!"{requestPath}: unreadable model")
    let observed := ((← readJson (root / artifactPath)).getObjValAs? (Array Json) "rows").toOption.getD #[]
    let rows := (request.getObjValAs? (Array Json) "rows").toOption.getD #[]
    if rows.isEmpty then failures := failures.push s!"{requestPath}: no rows"
    for row in rows do
      let name := (row.getObjValAs? String "name").toOption.getD "?"
      let key := s!"{requestPath.drop "captures/".length}#{name}"
      let engines := ((observed.find? fun candidate =>
          (candidate.getObjValAs? String "name").toOption == some name).bind fun candidate =>
          (candidate.getObjValAs? (Array Json) "engines").toOption).getD #[]
      if engines.isEmpty then
        failures := failures.push s!"{key}: no observation"
        continue
      let document ← match row.getObjVal? "documentInline", row.getObjValAs? String "document" with
        | .ok inline, _ => pure (Except.ok inline)
        | _, .ok file => pure (parseDocumentJson (← IO.FS.readFile (directory / file)))
        | _, _ => pure (.error "no document")
      let read := document.bind (readDocument model)
      for engine in engines do
        let faulted := (engine.getObjVal? "fault").isOk
        let outcome : Option String := match read with
          | .error reason => some s!"unreadable document: {reason}"
          | .ok read =>
              if faulted then
                if !read.refusals.isEmpty && read.refusals.all (·.2.endsWith profileRefusal) then none
              else some s!"the Kernel faulted where the reader gives {read.refusals}"
              else if !read.refusals.isEmpty then some s!"refused {read.refusals}"
              else
                let sorted := fun (list : List String) => list.mergeSort (· ≤ ·)
                let lean := sorted (leanCodes model.flat read.data.cells)
                let kernel := sorted (kernelCodes engine)
                if lean == kernel then none else some s!"{lean} against {kernel}"
        match outcome with
        | some detail => failures := failures.push s!"{key}: {detail}"
        | none =>
            agreeing := agreeing + 1
            compared := compared + (kernelCodes engine).length
  if !failures.isEmpty then
    throw (IO.userError s!"Number formal observations diverge:\n{"\n".intercalate failures.toList}")
  pure (agreeing, compared)

end A12Kernel.Evidence.NumberFormalProjection
