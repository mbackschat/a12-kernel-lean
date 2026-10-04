import A12Kernel.Elaboration.TemporalTargetPolicy

namespace A12Kernel

/-- The two renderable Date target shapes, dispatched on the declared format exactly as the Kernel
does. They share one outcome domain because they differ only in which components the store keeps. -/
inductive CheckedDateConstantTarget (model : FlatModel) (sourceCarriesYear : Bool := true) where
  | complete (target : CheckedDateFormatTarget model)
      (yearAgreement : (sourceCarriesYear || model.hasBaseYear) = true)
  | omittedComponent (target : CheckedOmittedComponentDateTarget model sourceCarriesYear)

namespace CheckedDateConstantTarget

def field : CheckedDateConstantTarget model sourceCarriesYear → FieldId
  | .complete target _ => target.checked.target.id
  | .omittedComponent target => target.checked.target.id

/-- The year presence of the stored format, independent of the source literal's completion. -/
def carriesYear : CheckedDateConstantTarget model sourceCarriesYear → Bool
  | .complete _ _ => true
  | .omittedComponent target => target.format.carriesYear

/-- The exact stored text this target gives one literal date, before its own gates judge it. -/
def renderCivil (target : CheckedDateConstantTarget model sourceCarriesYear)
    (date : CivilDate) : StoredDate :=
  match target with
  | .complete target _ => target.format.renderCivil date
  | .omittedComponent target => target.format.renderCivil date

/-- All Date renderers consume calendar parts before applying declaration-owned storage gates. -/
def evaluateParts (target : CheckedDateConstantTarget model sourceCarriesYear)
    (parts : DateParts) : FullDateTargetOutcome :=
  match target with
  | .complete target _ => target.evaluateParts parts
  | .omittedComponent target => target.evaluateParts parts

/-- Render and check one literal date against whichever shape the declaration selected. -/
def evaluateCivil (target : CheckedDateConstantTarget model sourceCarriesYear)
    (date : CivilDate) : FullDateTargetOutcome :=
  match target with
  | .complete target _ => target.evaluateCivil date
  | .omittedComponent target => target.evaluateCivil date

end CheckedDateConstantTarget

inductive DateConstantTargetElabError where
  | yearDisagreement
  | notRenderable (complete : FullDateTargetElabError) (omitting : OmittedComponentDateTargetElabError)
  deriving Repr, DecidableEq

/-- Select the declaration-owned renderer, preserving authored year presence separately from the
    civil date used at runtime. The Base Year admission rule is symmetric over the pair. -/
def elaborateDateConstantTargetIn (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) (sourceCarriesYear : Bool := true) :
    Except DateConstantTargetElabError (CheckedDateConstantTarget model sourceCarriesYear) := do
  match elaborateDateFormatTargetIn model scope targetField with
  | .ok target =>
      if h : (sourceCarriesYear || model.hasBaseYear) = true then
        pure (.complete target h)
      else throw .yearDisagreement
  | .error complete =>
      match elaborateOmittedComponentDateTargetIn model scope targetField sourceCarriesYear with
      | .ok target => pure (.omittedComponent target)
      | .error omitting => throw (.notRenderable complete omitting)

end A12Kernel
