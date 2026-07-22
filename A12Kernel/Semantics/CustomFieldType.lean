import A12Kernel.Document
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.CustomFieldType — checked registered validator observation

This capsule checks that a declaration's named pure validator exists in the explicit `World`, derives the kernel's effective context, and samples it only for a relevant nonempty parsed value. The returned ordinary `CheckedCell` is the single reusable observation for message, suppression, validation, and computation consumers.
-/

namespace A12Kernel

/-- The raw model declaration preserves whether either validator hint was authored. -/
structure CustomFieldTypeDeclaration where
  name : String
  minLength : Option Nat := none
  maxLength : Option Nat := none
  deriving Repr, DecidableEq

inductive CustomFieldTypeElabError where
  | missingValidator (name : String)
  deriving Repr, DecidableEq

/-- A checked declaration owns the exact validator resolved from the construction world. -/
structure CheckedCustomFieldType where
  declaration : CustomFieldTypeDeclaration
  validator : RegisteredCustomFieldValidator

def CustomFieldTypeDeclaration.validationContext
    (declaration : CustomFieldTypeDeclaration) (locale : String) :
    CustomFieldValidationContext where
  locale := locale
  minLength := declaration.minLength.getD 1
  maxLength := declaration.maxLength.getD 999
  isDisplayValue := false

/-- Reject an unregistered name during checked construction rather than failing during evaluation or inventing a generic rejection. -/
def elaborateCustomFieldType (world : World)
    (declaration : CustomFieldTypeDeclaration) :
    Except CustomFieldTypeElabError CheckedCustomFieldType :=
  match world.resolveCustomFieldValidator? declaration.name with
  | none => .error (.missingValidator declaration.name)
  | some validator => .ok { declaration, validator }

/-- Sample the checked validator for one relevant concrete stored value. Nonrelevance returns no observation; physical/semantic emptiness and preceding parser rejection bypass the validator. A nonempty parsed value produces one ordinary checked cell that every later consumer can share. -/
def CheckedCustomFieldType.checkRelevantRaw (checked : CheckedCustomFieldType)
    (locale : String) (relevant : Bool) (raw : RawCell String) :
    Option (CheckedCell String) :=
  if relevant then
    some (checkRawCellWith (fun value =>
      if value.isEmpty then
        .ok none
      else
        match checked.validator value
            (checked.declaration.validationContext locale) with
        | none => .ok (some value)
        | some rejection =>
            .error (.registeredCustomValidation rejection)) raw)
  else
    none

end A12Kernel
