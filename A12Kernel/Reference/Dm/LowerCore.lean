import A12Kernel.Reference.Dm.Syntax
import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.RoundingArgument
import A12Kernel.Elaboration.DeclarationAdmission

/-! # Lowering parse trees: the shared vocabulary

The pieces every lowering of a parsed text needs: the refusal it reports, paths and literals in the
elaborators' surface form, and the comparison operators. Lowering retains grammar-position and
static operand restrictions before dispatching to the existing checked carriers; evaluation stays
in those carriers. Refusals name the construct and shape the replay ledger clusters on.
-/

namespace A12Kernel.Dm

def datePart? : String → Option DateNumericPart
  | "YearFromDate" => some .year
  | "MonthFromDate" => some .month
  | "DayFromDate" => some .day
  | "QuarterFromDate" => some .quarter
  | _ => none

def timePart? : String → Option TimeNumericPart
  | "HoursFromTime" => some .hour
  | "MinutesFromTime" => some .minute
  | "SecondsFromTime" => some .second
  | _ => none


def Expr.patternConstant? : Expr → Option String
  | .string source => some source
  | .braces body => body.patternConstant?
  | _ => none


/-- Why a parsed text did not reach a checked carrier. `construct` is the catalog id or shape the
ledger clusters on, `detail` the elaborator's own error when one answered. -/
structure Refusal where
  construct : String
  detail : String := ""
  declarationFailure? : Option DeclarationAdmissionFailure := none
  deriving Repr, BEq, Inhabited

abbrev Lowering := Except Refusal

def refuse (construct : String) (detail : String := "") : Lowering α :=
  .error { construct, detail }

def admitDeclarations (declarations : List ExecutableDeclaration) : Lowering Unit :=
  (ExecutableDeclaration.admitAll declarations).mapError fun failure =>
    { construct := "DeclarationAdmission", detail := toString (repr failure),
      declarationFailure? := some failure }

/-- A detail on one physical line, so a replay row stays one row. -/
def oneLine (text : String) : String :=
  String.ofList (text.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c)

/-- The Kernel class a reader refusal reports for an elaboration error. An error type the reader has no
settled projection for reports none; `RefusalClass` supplies the projections. -/
class StaticClassified (ε : Type) where
  diagnostic? : ε → Option KernelStaticDiagnostic

instance (priority := low) noStaticClass : StaticClassified ε := ⟨fun _ => none⟩

/-- A refusal's detail: the Kernel class first, where the error carries one, then the cause, so a
comparison reads the class off the first word and a lock the whole cause. -/
def classifiedDetail [Repr ε] [StaticClassified ε] (error : ε) : String :=
  let cause := oneLine ((repr error).pretty 100000)
  match StaticClassified.diagnostic? error with
  | some diagnostic => s!"{diagnostic.kernelCode} {cause}"
  | none => cause

/-- The Kernel class a refusal detail leads with, if any. -/
def Refusal.kernelClass? (refusal : Refusal) : Option String :=
  (refusal.detail.splitOn " ").head?.filter (·.startsWith "MVK_")

/-- A refusal detail without its leading Kernel class: the structural cause alone, or the class when
the detail is nothing else. -/
def Refusal.cause (refusal : Refusal) : String :=
  match refusal.kernelClass? with
  | some code => if refusal.detail.length ≤ code.length then refusal.detail
      else (refusal.detail.drop (code.length + 1)).toString
  | none => refusal.detail

/-- Lift an elaborator's result, naming the construct it was asked for. -/
def elaborated [Repr ε] [StaticClassified ε] (construct : String) : Except ε α → Lowering α
  | .ok value => .ok value
  | .error error => .error { construct, detail := classifiedDetail error }

def Path.base : Path → PathBase
  | path => if path.absolute then .absolute else .relative path.ups

def Path.isPlain (path : Path) : Bool :=
  !path.correlated && path.segments.all (!·.star)

/-- A field path with no star, no correlation and at least one segment. -/
def Path.toFieldPath? (path : Path) : Option SurfaceFieldPath := do
  if !path.isPlain then none
  let field ← path.segments.getLast?
  pure { base := path.base, turningPoint := path.turningPoint
         groups := path.segments.dropLast.map (·.name), field := field.name }

def Path.toGroupPath? (path : Path) : Option SurfaceGroupPath := do
  if !path.isPlain then none
  pure { base := path.base, turningPoint := path.turningPoint, groups := path.segments.map (·.name) }

def Path.starGroups (path : Path) : List SurfaceStarGroupSegment :=
  path.segments.map fun segment => { name := segment.name, starred := segment.star }

/-- A path whose last segment is a field and whose groups may carry stars. -/
def Path.toStarFieldPath? (path : Path) : Option SurfaceStarFieldPath := do
  if path.correlated then none
  let field ← path.segments.getLast?
  if field.star then none
  pure { base := path.base, turningPoint := path.turningPoint
         groups := path.starGroups.dropLast, field := field.name }

/-- A plain entity in a field slot: a bare path with neither index nor category. -/
def Expr.fieldEntity? : Expr → Option SurfaceFieldPath
  | .entity { path, index := none, category := none, filter := none } => path.toFieldPath?
  | _ => none

/-- A bracketed read of a plain field. -/
def Expr.fieldValue? : Expr → Option SurfaceFieldPath
  | .value { path, index := none, category := none, filter := none } => path.toFieldPath?
  | _ => none

/-- A bracketed stored or category field read, shared by validation and computation membership. -/
def Expr.textFieldValue? : Expr → Option SurfaceTextFieldOperand
  | .value { path, index := none, category, filter := none } => do
      let field ← path.toFieldPath?
      pure (match category with | none => .direct field | some name => .category field name)
  | _ => none

/-- A group in a group slot: a bare path, or `RuleGroup`. -/
def Expr.groupReference? : Expr → Option SurfaceGroupReference
  | .constant "RuleGroup" => some (.ruleGroup false)
  | .entity { path, index := none, category := none, filter := none } => (path.toGroupPath?).map .path
  | _ => none

/-- A number literal as authored: its value and the scale its digits spell (spec §12.2). -/
def decodeNumber? (text : String) : Option DecodedNumericLiteral := do
  let negative := text.startsWith "-"
  let digits := if negative then (text.drop 1).toString else text
  let (integer, fraction) := match digits.splitOn "." with
    | [integer] => (integer, "")
    | [integer, fraction] => (integer, fraction)
    | _ => ("", "")
  if integer.isEmpty || !(integer ++ fraction).all Char.isDigit then none
  let unscaled ← (integer ++ fraction).toNat?
  let magnitude : Rat := (unscaled : Rat) / ((10 : Rat) ^ fraction.length)
  pure { value := if negative then -magnitude else magnitude, authoredScale := fraction.length }

private def twoDigits? (text : String) : Option Nat :=
  if text.length == 2 && text.all Char.isDigit then text.toNat? else none

private def dateConstantParts? (text : String) : Option (Nat × Nat × Nat) := do
  let [day, month, year] := text.splitOn "." | none
  let day ← twoDigits? day
  let month ← twoDigits? month
  if year.length != 4 || !year.all Char.isDigit then none
  pure (← year.toNat?, month, day)

/-- The calendar date a `DD.MM.YYYY` literal names; any other text is not a date (spec §12.2: zero
padding and a real calendar date are part of the shape). -/
def civilDateConstant? (text : String) : Option CivilDate := do
  let (year, month, day) ← dateConstantParts? text
  CivilDate.ofYmd? year month day

/-- The clock an exact `HH:mm:ss` literal names, a real one only ([`spec/05`](../../../spec/05-dates-and-time.md)
§1, the literal typing note). -/
def timeConstant? (text : String) : Option TimeOfDay := do
  let [hour, minute, second] := text.splitOn ":" | none
  TimeOfDay.ofHms? (← twoDigits? hour) (← twoDigits? minute) (← twoDigits? second)

/-- The wall label a date literal joined by `T` to a clock literal names. -/
def dateTimeConstant? (text : String) : Option LocalDateTime := do
  let [date, clock] := text.splitOn "T" | none
  let (year, month, day) ← dateConstantParts? date
  let time ← timeConstant? clock
  LocalDateTime.ofYmdHms? year month day time.hour time.minute time.second

/-- The month and day an omitted-year `DD.MM.` literal names, a real date in a common year only,
whatever the Base Year ([`spec/05`](../../../spec/05-dates-and-time.md) §1): `"30.04."` names one,
`"31.04."` and `"29.02."` are strings. -/
def yearlessDateConstant? (text : String) : Option (Nat × Nat) := do
  let [day, month, ""] := text.splitOn "." | none
  let day ← twoDigits? day
  let month ← twoDigits? month
  -- 2023 stands for every common year, whose month lengths are all the check reads.
  let _ ← CivilDate.ofYmd? 2023 month day
  pure (month, day)

/-- Preserve a date literal's written year presence for arithmetic and assignment alike. -/
def authoredDateLiteral? (text : String) : Option AuthoredDateLiteral :=
  match civilDateConstant? text, yearlessDateConstant? text with
  | some date, _ => some { year := some date.parts.year, month := date.parts.month, day := date.parts.day }
  | _, some (month, day) => some { year := none, month, day }
  | _, _ => none

def baseYearDateSource? : Expr → Option BaseYearDateSource
  | .constant "BaseYear" => some .direct
  | .call bound [.mk (.constant "BaseYear") none] none none =>
      match bound with
      | "StartOfDateRange" => some (.range .start)
      | "EndOfDateRange" => some (.range .finish)
      | _ => none
  | _ => none

def dateDifferenceOperandWith? (field : Expr → Option Field) : Expr → Option (SurfaceDateDifferenceOperand Field)
  | .string text => authoredDateLiteral? text |>.map .literal
  | .constant "Now" => some .now
  | .constant "Today" => some .today
  | expr => match baseYearDateSource? expr with
      | some source => some (.baseYear source)
      | none => field expr |>.map .field

/-- Whether a quoted literal is typed as a temporal constant rather than a string, by its content
alone: a date with or without its year, a clock, or a date and a clock joined by `T`. The typing
precedes every operand walk, so a site reading the literal as text must refuse it instead
([`spec/05`](../../../spec/05-dates-and-time.md) §1, [`spec/12`](../../../spec/12-concrete-syntax.md) §2). -/
def isTemporalConstant (text : String) : Bool :=
  (civilDateConstant? text).isSome || (yearlessDateConstant? text).isSome ||
    (timeConstant? text).isSome || (dateTimeConstant? text).isSome

/-- Preserve authored year presence while resolving Date literals in the model zone (spec/05 §1). -/
def dateConstant? (model : FlatModel) (text : String) : Option SurfaceLiteral := do
  let literal ← authoredDateLiteral? text
  let instant ← literal.comparisonInstant? model
  pure (.date literal.components instant)

def CompareOp.toSurface? : CompareOp → Option SurfaceComparisonOp
  | .eq => some .equal
  | .ne => some .notEqual
  | .lt => some .less
  | .le => some .lessEqual
  | .gt => some .greater
  | .ge => some .greaterEqual
  | _ => none

/-- The same comparison read from the other side, for a literal written on the left. -/
def mirrorComparison : SurfaceComparisonOp → SurfaceComparisonOp
  | .less => .greater
  | .lessEqual => .greaterEqual
  | .greater => .less
  | .greaterEqual => .lessEqual
  | op => op

def CompareOp.toNumeric? : CompareOp → Option NumericValidationOp
  | .eq => some (.ordinary .equal)
  | .ne => some (.ordinary .notEqual)
  | .lt => some (.ordinary .less)
  | .le => some (.ordinary .lessEqual)
  | .gt => some (.ordinary .greater)
  | .ge => some (.ordinary .greaterEqual)
  | .tolerance 1 => some (.tolerance .range1)
  | .tolerance 2 => some (.tolerance .range2)
  | .tolerance 5 => some (.tolerance .range5)
  | .tolerance 10 => some (.tolerance .range10)
  | _ => none

/-- The decimal places a rounding call names: an integer literal in `0..14`, or `0` when omitted
(spec §4). -/
def roundingPlaces? : List Argument → Option RoundingPlaces
  | [] => some omittedRoundingPlaces
  | [.mk (.number text) none] => text.toNat?.bind RoundingPlaces.ofNat?
  | _ => none

def roundingMode? : String → Option DecimalRoundingMode
  | "RoundDown" => some .floor
  | "RoundUp" => some .ceiling
  | "RoundAccounting" => some .halfUp
  | _ => none

/-- GrammarOnly entity slots admit digit-only field names, distinct from numeric literal operands. -/
def numericFieldFormReference (source : Expr) : Lowering Reference :=
  match source with
    | .entity reference => pure reference
    | .number text =>
        if !text.isEmpty && text.toList.all Char.isDigit then
          pure ({ path := { segments := [{ name := text, star := false }] } } : Reference)
        else refuse "NumericFieldForm" KernelStaticDiagnostic.unexpectedToken.kernelCode
    | _ => refuse "NumericFieldForm" KernelStaticDiagnostic.unexpectedToken.kernelCode

/-- Field forms share the checked Number read and arithmetic but retain their source slot
until KF393/KF395's group, star, category and kind gates have answered. -/
def lowerNumericFieldAtom (model : FlatModel) (group : GroupPath)
    (atom : Expr → Lowering Atom) (source : Expr) : Lowering Atom := do
  let reference ← numericFieldFormReference source
  if reference.filter.isSome then refuse "NumericFieldForm" "filtered reference"
  let unstarred : Path := { reference.path with segments := reference.path.segments.map fun (segment : Segment) => { segment with star := false } }
  let some field := unstarred.toFieldPath? | refuse "NumericFieldForm" "correlated source"
  if (model.groupNamedBy? group field).isSome then
    refuse "NumericFieldForm" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if reference.path.segments.any (·.star) then
    refuse "NumericFieldForm" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  let declaration ← elaborated "NumericFieldForm" (model.resolveFieldDeclarationUnchecked group field)
  if reference.category.isSome then
    refuse "NumericFieldForm" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  match declaration.policy.kind with
  | .number _ => atom (.value reference)
  | _ => refuse "NumericFieldForm" KernelStaticDiagnostic.noNumber.kernelCode

private inductive NumericFieldForm where
  | absolute
  | rounded (mode : DecimalRoundingMode)

private def numericFieldForm? : String → Option NumericFieldForm
  | "AbsValue" => some .absolute
  | "RoundDownValue" => some (.rounded .floor)
  | "RoundUpValue" => some (.rounded .ceiling)
  | "RoundAccountingValue" => some (.rounded .halfUp)
  | _ => none

/-- Syntax routing shares the field-form vocabulary without running its operand gates. -/
def isNumericFieldForm (name : String) : Bool := (numericFieldForm? name).isSome

/-- The grammar admits only an optional unsigned digit token (GrammarOnly rundenOp).
Semantic precision bounds are checked separately, after the field (KF393/KF448). -/
private def fieldRoundingArgument (arguments : List Argument) : Lowering (Option Nat) :=
  match arguments with
    | [] => pure none
    | [.mk (.number text) none] => match text.toNat? with
        | some value => pure (some value)
        | none => refuse "NumericFieldForm" KernelStaticDiagnostic.unexpectedToken.kernelCode
    | _ => refuse "NumericFieldForm" KernelStaticDiagnostic.unexpectedToken.kernelCode

private def numericReadRefusal [MonadExceptOf Refusal m] (construct : String)
    (detail : String := "") : m α := throw { construct, detail }

/-- Read numeric syntax in source order, exposing each completed operation to its admission
owner before proceeding to a sibling. Rounding operand gates precede precision gates
(CheckRundenOpImpl; CheckRundenOperOpImpl). -/
partial def lowerNumericExprWith [Monad m] [MonadExceptOf Refusal m]
    [Nonempty (m (AuthoredNumericExpr Atom))]
    (atom fieldAtom : Expr → m Atom)
    (beforeRounding : Expr → AuthoredNumericExpr Atom → m Unit)
    (complete : Expr → AuthoredNumericExpr Atom → m Unit)
    (expression : Expr) : m (AuthoredNumericExpr Atom) := do
  let recurse := lowerNumericExprWith atom fieldAtom beforeRounding complete
  let argument (arguments : List Argument) : m (Option Nat) :=
    match fieldRoundingArgument arguments with
    | .ok value => pure value
    | .error error => throw error
  let rounding (id : String) (argument : Option Nat) : m RoundingPlaces := do
    match checkRoundingArgument argument with
    | .ok places => pure places
    | .error error => numericReadRefusal id error.kernelCode
  let tree ← match expression with
    | .number text => match decodeNumber? text with
        | some literal => pure (.literal literal)
        | none => numericReadRefusal "NumberLiteral" text
    | .braces body => (.group ·) <$> recurse body
    | .arith .pow base exponent => do
        pure (.power (← recurse base) (← recurse exponent))
    | .arith op left right => do
        let op : NumericScaleBinaryOp := match op with
          | .add => .add | .sub => .subtract | .mul => .multiply | _ => .divide
        pure (.binary op (← recurse left) (← recurse right))
    | .call "Abs" [.mk body none] none none => (.abs ·) <$> recurse body
    | .call id (.mk first none :: rest) none none =>
        if let some form := numericFieldForm? id then do
          match form with
          | .absolute =>
              if !rest.isEmpty then numericReadRefusal id KernelStaticDiagnostic.unexpectedToken.kernelCode
              else pure (.abs (.atom (← fieldAtom first)))
          | .rounded mode =>
              let places ← argument rest
              let source ← fieldAtom first
              pure (.round mode (← rounding id places) (.atom source))
        else if id == "Min" || id == "Max" then do
          let op : NumericExtremumOp := if id == "Min" then .minimum else .maximum
          let operands ← (first :: rest.filterMap fun | .mk e none => some e | _ => none).mapM recurse
          if operands.length != rest.length + 1 then numericReadRefusal id "filtered operand"
          match operands with
          | head :: tail => pure (.extremumCall op (tail.foldl (.extremum op) head))
          | [] => numericReadRefusal id
        else if let some mode := roundingMode? id then do
          let places ← argument rest
          let body ← recurse first
          beforeRounding first body
          pure (.round mode (← rounding id places) body)
        else (.atom ·) <$> atom expression
    | .call id [] none none =>
        if (numericFieldForm? id).isSome then numericReadRefusal id KernelStaticDiagnostic.unexpectedToken.kernelCode
        else (.atom ·) <$> atom expression
    | other => (.atom ·) <$> atom other
  complete expression tree
  pure tree

/-- Retain authored grouping, call boundaries and operand order for later typed admission;
rounding at each node makes reassociation observable (spec §4). -/
partial def lowerNumericExpr (atom fieldAtom : Expr → Lowering Atom) :
    Expr → Lowering (AuthoredNumericExpr Atom) :=
  lowerNumericExprWith atom fieldAtom (fun _ _ => pure ()) (fun _ _ => pure ())

/-- The first operator call in a tree, left to right: what a comparison is about when its sides are
operations, and so the cluster key a refused comparison is filed under. -/
partial def Expr.leadingCall? : Expr → Option String
  | .call id _ _ _ => some id
  | .arith _ left right | .compare _ left right => left.leadingCall?.orElse fun _ => right.leadingCall?
  | .braces body | .parens body => body.leadingCall?
  | _ => none

/-- The catalog id a parse tree's head stands for, the ledger's cluster key. -/
def Expr.construct : Expr → String
  | .number _ => "NumberLiteral"
  | .string _ => "StringLiteral"
  | .value _ => "FieldValue"
  | .entity _ => "Entity"
  | .constant id => id
  | .call id _ _ _ => id
  | .custom _ _ => "CustomCondition"
  | .arith _ _ _ => "Arithmetic"
  | .braces _ => "Braces"
  | .compare .patternMatched _ _ => "PatternMatched"
  | .compare .patternViolated _ _ => "PatternViolated"
  | .compare (.tolerance _) _ _ => "DiffersWithTolerance"
  | .compare _ _ _ => "Comparison"
  | .logic .and _ => "And"
  | .logic .or _ => "Or"
  | .parens _ => "Parens"

def calendarUnit? : String → Option DateDifferenceUnit
  | "DifferenceInMonths" => some .months
  | "DifferenceInYears" => some .years
  | _ => none

def subdayUnit? : String → Option DateTimeSubdayUnit
  | "DifferenceInHours" => some .hours
  | "DifferenceInMinutes" => some .minutes
  | "DifferenceInSeconds" => some .seconds
  | _ => none

def aggregateOp? : String → Option NumericAggregateOp
  | "Sum" => some .sum
  | "MinValue" => some .minimum
  | "MaxValue" => some .maximum
  | "NumberOfDifferentValues" => some .distinctCount
  | _ => none

end A12Kernel.Dm
