import A12Kernel.Elaboration.Flat

/-! # Partial-Date and Number-field `Time(...)`

This capsule checks the ordinary nonrepeatable Number-field form of each supplied
`Time(...)` component. The declaration must guarantee an integral nonnegative value and
either the two-character stored bound or the exact maximum for its position.

String fields remain excluded because the flat declaration does not retain the kernel
checker's extensible-enumeration distinction. Extractors and mixed component forms remain
separate.
-/

namespace A12Kernel

/-- The declaration gate selected by a field's authored `Time(...)` position. -/
inductive TimeNumberFieldPosition where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

namespace TimeNumberFieldPosition

/-- Inclusive maximum accepted as the position-specific alternative to stored length 2. -/
def maximum : TimeNumberFieldPosition → Rat
  | .hour => 23
  | .minute | .second => 59

end TimeNumberFieldPosition

private def hasNonnegativeNumberDomain
    (declaration : FlatFieldDecl) (source : FlatNumberField) : Bool :=
  if source.info.signed then
    match declaration.numericTargetConstraints.minimum with
    | some minimum => decide (0 ≤ minimum)
    | none => false
  else
    true

/-- Exact Number declaration gate used by one `Time(...)` component position. The
    two-character alternative is the declaration's complete stored-length bound, not its
    integer-digit cap. -/
def FlatModel.admitsTimeNumberField (model : FlatModel)
    (position : TimeNumberFieldPosition) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      let constraints := declaration.numericTargetConstraints
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some source &&
        source.info.scale == 0 &&
        constraints.minFractionalDigits == 0 &&
        (constraints.maxStoredLength == some 2 ||
          constraints.maximum == some position.maximum) &&
        hasNonnegativeNumberDomain declaration source

/-- One ordinary Number field whose declaration carries the exact component certificate. -/
structure CheckedTimeNumberField (model : FlatModel) where
  position : TimeNumberFieldPosition
  source : FlatNumberField
  admitted : model.admitsTimeNumberField position source = true

/-- The grammar-valid one-to-three-field prefix forms. Omitted trailing components are
    absent from this type and therefore cannot be read. -/
inductive SurfaceTimeNumberFields where
  | hour (hour : FieldId)
  | minute (hour minute : FieldId)
  | second (hour minute second : FieldId)
  deriving Repr, DecidableEq

/-- A checked one-to-three-field prefix retaining each field's authored position. -/
inductive CheckedTimeNumberFields (model : FlatModel) where
  | hour (hour : CheckedTimeNumberField model)
  | minute (hour minute : CheckedTimeNumberField model)
  | second (hour minute second : CheckedTimeNumberField model)

/-- Static rejection before any `Time(...)` component field is read. -/
inductive TimeNumberFieldsElabError where
  | field (position : TimeNumberFieldPosition) (error : ResolveError)
  | notNumber (position : TimeNumberFieldPosition) (field : FieldId)
  | declarationNotAdmitted (position : TimeNumberFieldPosition) (field : FieldId)
  deriving Repr, DecidableEq

private def elaborateTimeNumberField (model : FlatModel)
    (position : TimeNumberFieldPosition) (field : FieldId) :
    Except TimeNumberFieldsElabError (CheckedTimeNumberField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.notNumber position field)
  if admitted : model.admitsTimeNumberField position source = true then
    pure { position, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

/-- Check every supplied field from Hour through Second and preserve that prefix order. -/
def elaborateTimeNumberFields (model : FlatModel) :
    SurfaceTimeNumberFields →
      Except TimeNumberFieldsElabError (CheckedTimeNumberFields model)
  | .hour hour => do
      pure (.hour (← elaborateTimeNumberField model .hour hour))
  | .minute hour minute => do
      pure (.minute
        (← elaborateTimeNumberField model .hour hour)
        (← elaborateTimeNumberField model .minute minute))
  | .second hour minute second => do
      pure (.second
        (← elaborateTimeNumberField model .hour hour)
        (← elaborateTimeNumberField model .minute minute)
        (← elaborateTimeNumberField model .second second))

end A12Kernel
