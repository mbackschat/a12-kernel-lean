import A12Kernel.Elaboration.DateRangeTargetPresentation
import A12Kernel.Elaboration.Flat.Model

namespace A12Kernel

/-- Equality of shared runtime format classes within the admitted declaration profiles.
Interpreted formats share by direction and additional-check flag, not spelling (spec/05 §8,
`CodeGenDateRangeTypeImpl` and `MetaGemeinsameFormate`). -/
def DateRangeDeclarationPolicy.sharesRuntimeFormat
    (left right : DateRangeDeclarationPolicy) : Bool :=
  left.youngerThan1900Check == right.youngerThan1900Check &&
    match left.interpretationOfYear, right.interpretationOfYear with
    | some a, some b => a == b
    | none, none => left.format == right.format && left.separator == right.separator
    | _, _ => false

/-- The first model declaration in the field's shared format class supplies runtime policy.
The original declaration remains the owner of static admission and document conversion. -/
def FlatModel.dateRangeRuntimePolicy (model : FlatModel)
    (declared : DateRangeDeclarationPolicy) : DateRangeDeclarationPolicy :=
  ((model.fields.filterMap (·.toDateRangeDeclarationPolicy?)).find?
    (·.sharesRuntimeFormat declared)).getD declared

/-- Convert document input using its own declaration, then expose the shared runtime spelling.
Failed conversion retains the raw String for runtime formal checking, as the document
deserializer does; it is not itself a formal verdict (spec/05 §8). -/
def FlatModel.dateRangeRuntimeText (model : FlatModel)
    (declared : DateRangeDeclarationPolicy) (text : String) :
    Except DateRangeInputError String := do
  let input ← match DateRangeInputFormat.ofPolicy? declared with
    | some format => pure format
    | none => throw (.unsupportedPolicy declared.format declared.separator)
  let effective := model.dateRangeRuntimePolicy declared
  let output ← match DateRangeInputFormat.ofPolicy? effective with
    | some format => pure format
    | none => throw (.unsupportedPolicy effective.format effective.separator)
  if text.isEmpty then return text
  match input.parseBasicEndpoints declared (model.baseYear.getD 2000) text with
  | .error _ => pure text
  | .ok (start, finish) => pure (output.renderParts start finish).text

/-- Classify runtime text, which has already passed declared conversion when read from JSON.
Day/month interpretation supplies adjacent years; month-only formal checking does not apply
that adjustment. Numeric endpoint reads still complete an admitted month range positionally. -/
def FlatModel.classifyRuntimeDateRange (model : FlatModel)
    (declared : DateRangeDeclarationPolicy) (text : String) :
    Except DateRangeInputError RawCell := do
  let effective := model.dateRangeRuntimePolicy declared
  let format ← match DateRangeInputFormat.ofPolicy? effective with
    | some format => pure format
    | none => throw (.unsupportedPolicy effective.format effective.separator)
  let runtimeYear := if effective.interpretationOfYear.isSome then
      some (model.baseYear.getD 2000) else model.baseYear
  let checkingPolicy := match format with
    | .yearlessMonth | .yearlessMonthConcatenated =>
        { effective with interpretationOfYear := none }
    | _ => effective
  let raw ← classifyStoredDateRangeForModel model.timeZoneId runtimeYear checkingPolicy text
  match format, raw with
  -- KF276 and DateUtil.completeDateAndFormat: month-only formal parsing does
  -- not take the year subsequently supplied to an endpoint consumer.
  | .yearlessMonth, _ | .yearlessMonthConcatenated, _ => pure raw
  | _, .parsed (.dateRange (.exact range)) =>
      if effective.youngerThan1900Check && range.start.parts.year < 1900 then
        pure (.rejected .dateRangeTooEarly)
      else pure raw
  | _, _ => pure raw

/-- Complete an unconfigured label range for a computation's Date endpoints. Its source has
already been observed; this positional completion is distinct from document conversion's
day-1 defaults (spec/05 §8). Invalid month labels remain invalid after rendering. -/
private def computationParts (year : Int) : DateRangeCellValue → DateParts × DateParts
  | .exact range => (range.start.parts, range.finish.parts)
  | .yearlessMonth start finish =>
      ({ year, month := start, day := 1 },
        { year, month := finish, day := (DateParts.daysInMonth? year finish).getD 1 })
  | .yearlessMonthDay start finish =>
      ({ year, month := start.month, day := start.day },
        { year, month := finish.month, day := finish.day })

/-- Render a computation through the target's shared policy, then check that runtime text.
The crossed-interpretation probe in spec/05 §8 distinguishes a valid source from an invalid
target attempt and its dependent poison. Declared source/target admission remains separate. -/
def FlatModel.evaluateDateRangeTarget (model : FlatModel) (target : FieldId)
    (result : DateRangeComputationResult) :
    Except DateRangeTargetEvaluationFault DateRangeTargetOutcome := do
  match result with
  | .noValue => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value value =>
      let some declaration := (model.lookupUniqueId target).toOption
        | throw (.targetUnavailable target)
      let some declared := declaration.toDateRangeDeclarationPolicy?
        | throw (.targetUnavailable target)
      let policy := model.dateRangeRuntimePolicy declared
      let some format := DateRangeInputFormat.ofPolicy? policy
        | throw (.input (.unsupportedPolicy policy.format policy.separator))
      let (start, finish) := computationParts (model.baseYear.getD 2000) value
      let attempted := format.renderParts start finish
      let raw ← (model.classifyRuntimeDateRange declared attempted.text).mapError .input
      match raw with
      | .rejected .dateRangeInvalid => pure (.errored attempted .inverted)
      | .rejected cause => pure (.errored attempted (.renderingRejected cause))
      | _ => pure (.accepted attempted)

end A12Kernel
