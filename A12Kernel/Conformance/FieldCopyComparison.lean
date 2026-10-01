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

/-- The measured eleven-kind model, shared with the [condition-class locks](ConditionDiagnostic.lean). -/
def model : FlatModel := { fields := declarations ++ [swapped, wide] }

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
private def ok := "admitted"
private def places := "MVK_INVALID_COMPARE_DEC_PLACES"
private def enumEnum := "MVK_INVALID_COMPARE_ENUM_TO_ENUM"
private def enumCalc := "MVK_ERROR_INVALID_ENUM_CALCULATION"

/-- Every retained row copying one field into another, as (target, source, measured verdict), in the
    capture's order ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)). -/
private def grid : List (String × String × String) :=
  [("Note2", "Note", ok), ("Note2", "Qty", text), ("Note2", "Amount", text),
    ("Note2", "Due", date), ("Note2", "At", date), ("Note2", "Window", range),
    ("Note2", "Flag", yesNo), ("Note2", "Signed", yes), ("Note2", "Plain", ok),
    ("Note2", "Labelled", display), ("Qty2", "Note", text), ("Qty2", "Qty", ok),
    ("Qty2", "Amount", places), ("Qty2", "Due", date), ("Qty2", "At", date),
    ("Qty2", "Window", range), ("Qty2", "Flag", yesNo), ("Qty2", "Signed", yes),
    ("Qty2", "Plain", text), ("Qty2", "Labelled", text), ("Amount2", "Note", text),
    ("Amount2", "Qty", places), ("Amount2", "Amount", ok), ("Amount2", "Due", date),
    ("Amount2", "At", date), ("Amount2", "Window", range), ("Amount2", "Flag", yesNo),
    ("Amount2", "Signed", yes), ("Amount2", "Plain", text), ("Amount2", "Labelled", text),
    ("Due2", "Note", date), ("Due2", "Qty", date), ("Due2", "Amount", date),
    ("Due2", "Due", ok), ("Due2", "At", date), ("Due2", "Window", date),
    ("Due2", "Flag", yesNo), ("Due2", "Signed", yes), ("Due2", "Plain", date),
    ("Due2", "Labelled", date), ("At2", "Note", date), ("At2", "Qty", date),
    ("At2", "Amount", date), ("At2", "Due", date), ("At2", "At", ok),
    ("At2", "Window", date), ("At2", "Flag", yesNo), ("At2", "Signed", yes),
    ("At2", "Plain", date), ("At2", "Labelled", date), ("Window2", "Note", range),
    ("Window2", "Qty", range), ("Window2", "Amount", range), ("Window2", "Due", date),
    ("Window2", "At", date), ("Window2", "Window", ok), ("Window2", "Flag", yesNo),
    ("Window2", "Signed", yes), ("Window2", "Plain", range), ("Window2", "Labelled", range),
    ("Flag2", "Note", yesNo), ("Flag2", "Qty", yesNo), ("Flag2", "Amount", yesNo),
    ("Flag2", "Due", yesNo), ("Flag2", "At", yesNo), ("Flag2", "Window", yesNo),
    ("Flag2", "Flag", ok), ("Flag2", "Signed", yes), ("Flag2", "Plain", yesNo),
    ("Flag2", "Labelled", yesNo), ("Signed2", "Note", yes), ("Signed2", "Qty", yes),
    ("Signed2", "Amount", yes), ("Signed2", "Due", yes), ("Signed2", "At", yes),
    ("Signed2", "Window", yes), ("Signed2", "Flag", yes), ("Signed2", "Signed", ok),
    ("Signed2", "Plain", yes), ("Signed2", "Labelled", yes), ("Plain2", "Note", enumCalc),
    ("Plain2", "Qty", text), ("Plain2", "Amount", text), ("Plain2", "Due", date),
    ("Plain2", "At", date), ("Plain2", "Window", range), ("Plain2", "Flag", yesNo),
    ("Plain2", "Signed", yes), ("Plain2", "Plain", ok), ("Plain2", "Labelled", display),
    ("Labelled2", "Note", display), ("Labelled2", "Qty", text), ("Labelled2", "Amount", text),
    ("Labelled2", "Due", date), ("Labelled2", "At", date), ("Labelled2", "Window", range),
    ("Labelled2", "Flag", yesNo), ("Labelled2", "Signed", yes), ("Labelled2", "Plain", display),
    ("Labelled2", "Labelled", ok), ("Stamp2", "Note", date), ("Stamp2", "Qty", date),
    ("Stamp2", "Amount", date), ("Stamp2", "Due", date), ("Stamp2", "At", date),
    ("Stamp2", "Window", date), ("Stamp2", "Flag", yesNo), ("Stamp2", "Signed", yes),
    ("Stamp2", "Plain", date), ("Stamp2", "Labelled", date), ("Stamp2", "Stamp", ok),
    ("Note2", "Stamp", date), ("Qty2", "Stamp", date), ("Amount2", "Stamp", date),
    ("Due2", "Stamp", date), ("At2", "Stamp", date), ("Window2", "Stamp", date),
    ("Flag2", "Stamp", yesNo), ("Signed2", "Stamp", yes), ("Plain2", "Stamp", date),
    ("Labelled2", "Stamp", date), ("Labelled2", "Swapped", enumEnum), ("Plain2", "Wide", enumCalc),
    ("Labelled2", "Wide", display), ("Wide", "Plain", ok), ("Note2", "Swapped", display)]


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

private def kindOf (name : String) : SurfaceScalarKind :=
  ((model.fields.find? (·.name == name)).map (·.policy.kind.surfaceKind)).getD .string

/-- A row neither side of which is of the carrier's kind, whose two kinds meet no kind arm, and which
    the display arm does not refuse: two fields of one other family, which the scale rule, the format
    question or the Enumeration calculation decides on that family's own carrier. Every carrier reads a
    copy through the shared comparison, so each answers the display arm's refusals too. -/
private def outside (own : SurfaceScalarKind) (row : String × String × String) : Bool :=
  kindOf row.1 != own && kindOf row.2.1 != own &&
    (copyComparisonKindArm? (kindOf row.1) (kindOf row.2.1)).isNone &&
    row.2.2 != display && row.2.2 != enumEnum

private def refuses (carrier : String → String → String) (row : String × String × String) : Bool :=
  carrier row.1 row.2.1 == "refused"

/- Every carrier answers every retained row with its measured verdict or claims no class, so no
   carrier ever claims a wrong one. -/
example :
    [stringCopy, numberCopy, enumerationCopy, fullDateCopy].all fun carrier =>
      grid.all fun row => carrier row.1 row.2.1 == row.2.2 || refuses carrier row := by
  native_decide

/- Where each carrier claims no class, exactly. The String, Number and Enumeration carriers answer
   every row one side of which is their kind, and every row whose kinds meet an arm; the rest are
   another family's. The exceptions are named: an unlabelled Enumeration into a String is admitted by
   the Kernel and refused here without a class, since neither the String carrier nor the Enumeration
   one has a leaf reading it as text; a String into an unlabelled Enumeration draws the calculation's
   class, which the Enumeration carrier owns. The full-Date carrier answers only a full-Date target, a
   clock or instant source through its format gate. -/
example :
    let unlabelledIntoText := ("Note2", "Plain")
    let textIntoUnlabelled := ("Plain2", "Note")
    grid.all (fun row => refuses stringCopy row ==
      (outside .string row || [unlabelledIntoText, textIntoUnlabelled].contains (row.1, row.2.1))) ∧
    grid.all (fun row => refuses numberCopy row == outside .number row) ∧
    grid.all (fun row => refuses enumerationCopy row ==
      (outside .enumeration row || (row.1, row.2.1) == unlabelledIntoText)) ∧
    grid.all (fun row => refuses fullDateCopy row == (row.1 != "Due2")) := by
  native_decide

end A12Kernel.Conformance.FieldCopyComparison
