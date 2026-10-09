import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.TemporalNumericInput

namespace A12Kernel

/-- Precision is checked before format and Base Year (spec/05 §3, KF529). -/
def FlatFieldDecl.admitsTemporalPartPrecision (declaration : FlatFieldDecl)
    (part : TemporalNumericPart) : Bool :=
  !(declaration.toTemporalTargetPolicy?.any fun policy => !(match part with
    | .date part => part.admittedPartialMode policy.partialMode
    | .time _ => policy.partialMode == .full))

/-- Only partial declarations need a stored-component decoder. -/
def FlatModel.temporalNumericPartialFormat (model : FlatModel) (field : FieldId) :
    Option FullDateTargetFormat := do
  let declaration ← (model.lookupUniqueId field).toOption
  let policy ← declaration.toTemporalTargetPolicy?
  if policy.partialMode == .full then none else FullDateTargetFormat.ofSource? policy.format

/-- Certify source identity, precision, format and the exact model-owned partial decoder.
An unsupported partial spelling cannot be certified by omitting its decoder. -/
def FlatModel.admitsTemporalNumericPart (model : FlatModel) (field : FlatTemporalField)
    (part : TemporalNumericPart) (format : Option FullDateTargetFormat) : Bool :=
  (model.lookupUniqueId field.id).toOption.any fun declaration =>
    declaration.toTemporalField? == some field &&
      declaration.admitsTemporalPartPrecision part && part.admittedBy field model.hasBaseYear &&
      format == model.temporalNumericPartialFormat field.id &&
      !(declaration.toTemporalTargetPolicy?.any fun policy =>
        policy.partialMode != .full && format.isNone)

end A12Kernel
