import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.NumericComputation.Target
import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.FullDateComputation

/-! # A field copied into a field of another kind: the generated comparison's classes

One fixture mirrors the measured model: eleven declarations over all nine kinds, each with a twin that
serves as the target, so the diagonal is the admitted same-kind control. Every expected class below
is that model's measured row, a root computation copying one field into another
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)).
Each carrier is asked both ways: a source of another kind into its own target kind, and its own
kind copied into a target of another kind. -/

namespace A12Kernel.Conformance.FieldCopyComparison

open A12Kernel

private def labelled (first second : String) : List EnumerationDisplayFact :=
  [{ locale := "en_US", stored := "OPEN", display := first },
   { locale := "en_US", stored := "CLOSED", display := second }]

private def decl (id : FieldId) (name : String) (kind : FieldKind)
    (enumeration : Option EnumerationDeclaration := none) : FlatFieldDecl :=
  { id, groupPath := ["Order"], name, policy := { kind }, enumeration
    temporalTargetPolicy := match kind with
      | .temporal .date _ => some { format := "dd.MM.yyyy", partialMode := .full }
      | _ => none
    dateRangePolicy := match kind with
      | .dateRange => some { format := "dd.MM.yyyy", separator := "-" }
      | _ => none }

private def openClosed : EnumerationDeclaration := { storedTokens := ["OPEN", "CLOSED"] }

/-- The eleven source declarations, keyed by name; `20 + id` is each one's target twin. -/
private def kinds : List (String × FieldKind × Option EnumerationDeclaration) :=
  [("Note", .string, none),
   ("Qty", .number { scale := 0, signed := true }, none),
   ("Amount", .number { scale := 2, signed := true }, none),
   ("Due", .temporal .date TemporalComponents.fullDate, none),
   ("At", .temporal .time TemporalComponents.time, none),
   ("Stamp", .temporal .dateTime TemporalComponents.now, none),
   ("Window", .dateRange, none),
   ("Flag", .boolean, none),
   ("Signed", .confirm, none),
   ("Plain", .enumeration, some openClosed),
   ("Labelled", .enumeration, some { openClosed with displayFacts := labelled "Open" "Closed" })]

private def declarations : List FlatFieldDecl :=
  (kinds.zipIdx 1).flatMap fun ((name, kind, enumeration), id) =>
    [decl id name kind enumeration, decl (20 + id) (name ++ "2") kind enumeration]

/-- A labelled Enumeration whose labels conflict with `Labelled`'s, and an unlabelled one declaring
    a value the others do not. -/
private def swapped :=
  decl 40 "Swapped" .enumeration (some { openClosed with displayFacts := labelled "Closed" "Open" })
private def wide :=
  decl 41 "Wide" .enumeration (some { storedTokens := ["OPEN", "CLOSED", "PENDING"] })

private def model : FlatModel := { fields := declarations ++ [swapped, wide] }

private def idOf (name : String) : FieldId :=
  (model.fields.find? (·.name == name)).map (·.id) |>.getD 0

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

/-- `admitted`, the class a refusal projects, or `refused` for a refusal claiming none. -/
private def verdict (result : Except ε α) (project : ε → Option String) : String :=
  match result with
  | .ok _ => "admitted"
  | .error error => (project error).getD "refused"

private def stringCopy (target source : String) : String :=
  verdict (elaborateStringComputationOperation model ["Order"] (idOf target) (.field (bare source)))
    fun error => error.targetDiagnostic?.map (·.kernelCode)

private def numberCopy (target source : String) : String :=
  verdict (elaborateCompleteNumericTargetComputationOperation model ["Order"] (idOf target)
      (.atom (.numeric (.field (bare source)))))
    fun error => error.targetDiagnostic?.map (·.kernelCode)

private def enumerationCopy (target source : String) : String :=
  verdict (elaborateEnumerationComputation model ["Order"] (idOf target) (.field (.direct (bare source))))
    fun error => (error.diagnostic?.map (·.kernelCode)).orElse
      fun _ => error.calculationRefusal?.map (·.catalogKey)

private def fullDateCopy (target source : String) : String :=
  verdict (elaborateFullDateFieldComputation model (idOf source) (idOf target))
    fun error => error.diagnostic?.map (·.kernelCode)

private def text := "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"
private def date := "MVK_INVALID_COMPARE_TO_DATE"
private def range := "MVK_INVALID_COMPARE_TO_DATE_RANGE"
private def yesNo := "MVK_INVALID_COMPARE_TO_YESNO"
private def yes := "MVK_INVALID_COMPARE_TO_YES"
private def display := "MVK_INVALID_COMPARE_ENUM_TO_STRING"

/-- The kind arms against the measured grid: each arm claims its kind on either side, in the walk's
    order, so a Confirm outranks a Boolean, both outrank a temporal field, and a temporal field
    outranks a DateRange. Temporal pairs are `none` because the date arm reads formats. -/
example :
    [(.string, .number, some text), (.number, .string, some text), (.enumeration, .number, some text),
     (.number, .enumeration, some text), (.string, .temporal .date, some date),
     (.temporal .time, .number, some date), (.dateRange, .temporal .dateTime, some date),
     (.temporal .date, .dateRange, some date), (.string, .dateRange, some range),
     (.dateRange, .enumeration, some range), (.boolean, .temporal .date, some yesNo),
     (.dateRange, .boolean, some yesNo), (.confirm, .boolean, some yes), (.boolean, .confirm, some yes),
     (.temporal .date, .temporal .time, none), (.string, .enumeration, none), (.number, .number, none),
     (.confirm, .confirm, none), (.boolean, .boolean, none), (.dateRange, .dateRange, none)].all
      (fun ((target : SurfaceScalarKind), (source : SurfaceScalarKind), expected) =>
        (copyComparisonKindArm? target source).map (·.diagnostic.kernelCode) == expected) := by
  native_decide

/- A String target: every other kind draws its arm's class, a labelled Enumeration the display class.
   An unlabelled Enumeration is admitted by the Kernel, and this carrier, which has no Enumeration
   leaf, still refuses it without claiming a class. -/
example :
    ["Note", "Qty", "Amount", "Due", "At", "Stamp", "Window", "Flag", "Signed", "Labelled", "Plain"].map
        (stringCopy "Note2") =
      ["admitted", text, text, date, date, date, range, yesNo, yes, display, "refused"] := by
  native_decide

/- A String copied into each other kind. An unlabelled Enumeration target draws the calculation's
   own class, which belongs to the Enumeration carrier, so this one claims none. -/
example :
    ["Qty2", "Amount2", "Due2", "At2", "Stamp2", "Window2", "Flag2", "Signed2", "Labelled2", "Plain2"].map
        (stringCopy · "Note") =
      [text, text, date, date, date, range, yesNo, yes, display, "refused"] := by
  native_decide

/- A Number target, the scale rule deciding between two Numbers. -/
example :
    ["Qty", "Amount", "Note", "Due", "At", "Stamp", "Window", "Flag", "Signed", "Plain", "Labelled"].map
        (numberCopy "Qty2") =
      ["admitted", "MVK_INVALID_COMPARE_DEC_PLACES", text, date, date, date, range, yesNo, yes, text,
       text] := by
  native_decide

/- A Number copied into each other kind. -/
example :
    ["Note2", "Due2", "At2", "Stamp2", "Window2", "Flag2", "Signed2", "Plain2", "Labelled2"].map
        (numberCopy · "Qty") =
      [text, date, date, date, range, yesNo, yes, text, text] := by
  native_decide

/- An Enumeration target. The comparison answers first; only a copy it admits reaches the
   calculation's domain class, which a String into an unlabelled target and a wider unlabelled
   Enumeration draw. Where the display and the domain both fail, the display class answers. -/
example :
    ["Plain", "Note", "Qty", "Amount", "Due", "At", "Stamp", "Window", "Flag", "Signed", "Labelled",
        "Wide"].map (enumerationCopy "Plain2") =
      ["admitted", "MVK_ERROR_INVALID_ENUM_CALCULATION", text, text, date, date, date, range, yesNo,
       yes, display, "MVK_ERROR_INVALID_ENUM_CALCULATION"] ∧
    ["Labelled", "Note", "Plain", "Swapped", "Wide"].map (enumerationCopy "Labelled2") =
      ["admitted", display, display, "MVK_INVALID_COMPARE_ENUM_TO_ENUM", display] ∧
    enumerationCopy "Wide" "Plain" = "admitted" := by
  native_decide

/- An Enumeration copied into each other kind. An unlabelled one into a String is admitted by the
   Kernel and still refused here without a class, as on the String carrier. -/
example :
    ["Note2", "Qty2", "Due2", "At2", "Stamp2", "Window2", "Flag2", "Signed2"].map
        (enumerationCopy · "Labelled") =
      [display, text, date, date, date, range, yesNo, yes] ∧
    enumerationCopy "Note2" "Plain" = "refused" := by
  native_decide

/- A full-Date target. A temporal source is judged by its declared format, so a clock and an
   instant draw the date class through that gate, and every other kind through its arm. -/
example :
    ["Due", "Note", "Qty", "Amount", "Plain", "Labelled", "Window", "Flag", "Signed", "At", "Stamp"].map
        (fullDateCopy "Due2") =
      ["admitted", date, date, date, date, date, date, yesNo, yes, date, date] := by
  native_decide


end A12Kernel.Conformance.FieldCopyComparison
