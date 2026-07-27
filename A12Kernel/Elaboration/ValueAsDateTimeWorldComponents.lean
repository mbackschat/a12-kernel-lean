import A12Kernel.Elaboration.ValueAsDateTimeComponents

/-! # World-dependent checked `Time(...)` components

This capsule adds the dynamic `Now` companion to the document-only component owner. It
reuses the same prefix shape, checked numeric amount, exact-instant shift, model-zone
projection, and component result. The carrier states which branch needs `World`, so the
existing static API remains world-free and no second Time-prefix representation appears.
-/

namespace A12Kernel

/-- One matching component extractor over the shared dynamic `Now` shift. -/
structure CheckedNowShiftedTimeExtractor (model : FlatModel) where
  position : TimeComponentPosition
  part : TimeNumericPart
  source : CheckedShiftedNowDateTimeSource model
  positionMatches : position.extractor = part

/-- A component that declares whether it is document-only or needs the explicit world. -/
inductive CheckedWorldTimeComponent (model : FlatModel) where
  | static (checked : CheckedTimeComponent model)
  | shiftedNowExtractor (checked : CheckedNowShiftedTimeExtractor model)

/-- A checked prefix whose components state their world dependency explicitly. -/
abbrev CheckedWorldTimeComponents (model : FlatModel) :=
  TimeComponentPrefix (CheckedWorldTimeComponent model)

/-- Check one matching component extractor over the shared dynamic `Now` shift. -/
def elaborateNowShiftedTimeExtractor
    (model : FlatModel) (position : TimeComponentPosition)
    (part : TimeNumericPart) (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model) :
    Except TimeComponentsElabError (CheckedWorldTimeComponent model) := do
  if hPosition : position.extractor = part then
    let source ←
      elaborateShiftedNowDateTimeSource model unit amount
        |>.mapError .shifted
    pure (.shiftedNowExtractor {
      position
      part
      source
      positionMatches := hPosition
    })
  else
    throw (.extractorMismatch position part)

/-- Check a matching component extractor over one literal shift of dynamic `Now`. -/
def elaborateNowShiftedTimeExtractorLiteral
    (model : FlatModel) (position : TimeComponentPosition)
    (part : TimeNumericPart) (unit : DateTimeSubdayUnit)
    (amount : Rat) :
    Except TimeComponentsElabError (CheckedWorldTimeComponent model) :=
  elaborateNowShiftedTimeExtractor model position part unit (.literal amount)

/-- Check a matching component extractor over dynamic `Now` shifted by one checked direct-Number expression. -/
def elaborateNowShiftedTimeExtractorExpression
    (model : FlatModel) (rowGroup : GroupPath)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (unit : DateTimeSubdayUnit)
    (amount : AuthoredNumericExpr SurfaceNumericAtom) :
    Except TimeComponentsElabError (CheckedWorldTimeComponent model) := do
  let checkedAmount ←
    elaborateValueAsDateTimeExpressionShiftAmount model rowGroup amount
      |>.mapError .shifted
  elaborateNowShiftedTimeExtractor model position part unit checkedAmount

namespace CheckedNowShiftedTimeExtractor

/-- Execute the shared dynamic shift before applying the exact component projection. -/
def read (checked : CheckedNowShiftedTimeExtractor model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent := do
  let time ←
    checked.source.readTime phase world input |>.mapError .shifted
  pure (ValueAsDateTimeTimeOperand.extractComponent time checked.part)

end CheckedNowShiftedTimeExtractor

namespace CheckedWorldTimeComponent

/-- Read a static component without consulting `World`, or the dynamic component with it. -/
def read (checked : CheckedWorldTimeComponent model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match checked with
  | .static component => component.read phase input
  | .shiftedNowExtractor source => source.read phase world input

end CheckedWorldTimeComponent

namespace CheckedWorldTimeComponents

/-- Evaluate one checked prefix against the immutable document and explicit world. -/
def evaluate (checked : CheckedWorldTimeComponents model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionResult :=
  checked.evaluateWith fun component => component.read phase world input

end CheckedWorldTimeComponents

namespace CheckedValueAsDateTime

/-- Check the partial-Date source before executing a world-dependent Time prefix. -/
def evaluateWorldComponentsRaw (checked : CheckedValueAsDateTime model)
    (time : CheckedWorldTimeComponents model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (raw : RawCell String) :
    Except TimeComponentsFault ValueAsDateTimeResult :=
  checked.evaluateTimeOperandRaw phase raw fun _ => do
    let timeResult ← time.evaluate phase world input
    pure timeResult.asDateTimeOperand

end CheckedValueAsDateTime

end A12Kernel
