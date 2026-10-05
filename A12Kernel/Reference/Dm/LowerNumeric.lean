import A12Kernel.Reference.Dm.LowerEntity
import A12Kernel.Elaboration.NumericComputation.Atom

/-! # Lowering numeric operands

One lowering serves both arms' numeric operands, parameterized by what an aggregate ranges over:
a validation comparison's scalar atom aggregates direct field lists only, while a computation's
aggregates entity lists with stars, groups and filters. The atom forms themselves, field reads,
extractors, date differences, `Length`, `RangeAsNumber`, `FieldValueAsNumber`, `CurrentRepetition`
and `BaseYear`, mean the same on both arms and are lowered once.
-/

namespace A12Kernel.Dm

def aggregateOp? : String → Option NumericAggregateOp
  | "Sum" => some .sum
  | "MinValue" => some .minimum
  | "MaxValue" => some .maximum
  | "NumberOfDifferentValues" => some .distinctCount
  | _ => none

private def calendarUnit? : String → Option DateDifferenceUnit
  | "DifferenceInMonths" => some .months
  | "DifferenceInYears" => some .years
  | _ => none

def entityTextOperand? : Expr → Option SurfaceTextFieldOperand
  | .entity { path, index := none, category := none } => (path.toFieldPath?).map .direct
  | .entity { path, index := none, category := some name } => (path.toFieldPath?).map (.category · name)
  | _ => none

private def dateDifferenceOperand? : Expr → Option SurfaceDateDifferenceOperand
  | .string text => (authoredDateLiteral? text).map .literal
  | .constant "Now" => some .now
  | .constant "Today" => some .today
  | .constant "BaseYear" => some (.baseYear .direct)
  | expr => (expr.fieldEntity?).map .field

/-- One numeric atom. `aggregate` lowers an aggregate call's operands and `groups` a filled-group
count's, the two places the arms differ. -/
def lowerNumericAtomWith
    (aggregate : NumericAggregateOp → List Argument → Lowering Aggregate)
    (groups : List Argument → Lowering (List SurfaceGroupCountOperand)) :
    Expr → Lowering (SurfaceNumericAtom Aggregate)
  | .value { path, index := none, category := none } => match path.toFieldPath? with
      | some field => pure (.field field)
      | none => refuse "StarredValue"
  | .value _ => refuse "IndexedValue"
  | .constant "BaseYear" => pure .baseYear
  | .call "CurrentRepetition" [.mk group none none] none none => match group.groupReference? with
      | some (.path path) => pure (.currentRepetition path)
      | _ => refuse "CurrentRepetition"
  | .call "NumberOfFilledGroups" arguments none none => (.filledGroupCount ·) <$> groups arguments
  | .call "RangeAsNumber" [.mk field none none, .mk (.number start) none none,
      .mk (.number finish) none none] none none =>
      match field.fieldEntity?, start.toNat?, finish.toNat? with
      | some path, some start, some finish => pure (.stringRange path start finish)
      | _, _, _ => refuse "RangeAsNumber" "operand"
  | .call id [.mk left none none, .mk right none none] none none =>
      match id, calendarUnit? id, subdayUnit? id, dateDifferenceOperand? left,
          dateDifferenceOperand? right, aggregateOp? id with
      | "DifferenceInDays", _, _, some left, some right, _ => pure (.dayDifference left right)
      | _, some unit, _, some left, some right, _ => pure (.dateDifference unit left right)
      | _, _, some unit, some left, some right, _ => pure (.dateTimeDifference unit left right)
      | _, _, _, _, _, some op => (.aggregate op ·) <$> aggregate op [.mk left none none, .mk right none none]
      | _, _, _, _, _, none => refuse id "operand"
  | .call id [.mk operand none none] none none =>
      match datePart? id, timePart? id, aggregateOp? id, operand with
      | some part, _, _, .call bound [.mk range none none] none none =>
          match bound, range.fieldEntity? with
          | "StartOfDateRange", some path => pure (.dateRangeBoundPart path .start part)
          | "EndOfDateRange", some path => pure (.dateRangeBoundPart path .finish part)
          | _, _ => refuse id "operand"
      | some part, _, _, _ => match operand.fieldEntity? with
          | some path => pure (.temporalFieldPart path (.date part))
          | none => refuse id "operand"
      | _, some part, _, _ => match operand.fieldEntity? with
          | some path => pure (.temporalFieldPart path (.time part))
          | none => refuse id "operand"
      | _, _, some op, _ => (.aggregate op ·) <$> aggregate op [.mk operand none none]
      | none, none, none, _ =>
          match id, operand.fieldEntity?, entityTextOperand? operand with
          | "Length", some path, _ => pure (.stringLength path)
          | "FieldValueAsNumber", _, some source => pure (.fieldValueAsNumber source)
          | _, _, _ => refuse id "numeric operand"
  | .call id arguments none none => match aggregateOp? id with
      | some op => (.aggregate op ·) <$> aggregate op arguments
      | none => refuse id "numeric operand"
  | other => refuse other.construct "numeric operand"

/-- A validation comparison's scalar atom: aggregates over two or more direct fields, fixed group
counts. Starred and filtered operands belong to the ordered carrier. -/
def lowerValidationNumericAtom : Expr → Lowering SurfaceNumericAtom :=
  lowerNumericAtomWith
    (fun op arguments =>
      match arguments.mapM fun | .mk expr none none => expr.fieldEntity? | _ => none with
      | some (first :: rest) => pure { first, rest }
      | _ => refuse (match op with
          | .sum => "Sum" | .minimum => "MinValue" | .maximum => "MaxValue"
          | .distinctCount => "NumberOfDifferentValues") "entity operand")
    (fun arguments =>
      match arguments.mapM fun | .mk expr none none => expr.groupReference? | _ => none with
      | some groups => pure (groups.map .fixed)
      | none => refuse "NumberOfFilledGroups" "starred operand")

/-- A computation operation's atom, whose aggregates, counts and `FirstFilledValue` range over
entity lists. -/
def lowerComputationNumericAtom (model : FlatModel) (group : GroupPath) :
    Expr → Lowering SurfaceNumericComputationAtom
  | .call "NumberOfFilledFields" arguments none none =>
      (.filledFieldCount ·) <$> lowerEntitySource model group arguments
  | .call "FirstFilledValue" arguments none none =>
      (.firstFilled ·) <$> lowerEntitySource model group arguments
  | .call "SumOfProducts" arguments none none => (.sumOfProducts ·) <$> lowerProductAggregate arguments
  | .call "NumberOfValueInFields" [.mk expected none none] (some listed) none =>
      match expected with
      | .number text => match decodeNumber? text with
          | some literal => (.valueCount literal.value ·) <$> lowerEntitySource model group listed
          | none => refuse "NumberOfValueInFields" "expected value"
      | .constant "True" => (.booleanValueCount true ·) <$> lowerEntitySource model group listed
      | .constant "False" => (.booleanValueCount false ·) <$> lowerEntitySource model group listed
      | .string text => (.tokenEntityValueCount text ·) <$> lowerEntitySource model group listed
      | _ => refuse "NumberOfValueInFields" "expected value"
  | other => (.numeric ·) <$> lowerNumericAtomWith
      (fun _ arguments => lowerEntitySource model group arguments)
      (·.mapM lowerGroupCountOperand) other

end A12Kernel.Dm
