import A12Kernel.Elaboration.Flat

/-! # Checked raw-String rule elimination

Raw String declarations close every ordinary value-reading route in `Flat`. The sole legal value-shaped rule is recognized only at this whole-condition boundary and retained as max-length metadata; it never becomes a runtime condition.
-/

namespace A12Kernel

/-- The exact whole-rule declaration eliminated before validation execution. -/
structure CheckedRawStringMaximumLength (model : FlatModel) where
  rowGroup : GroupPath
  authoredField : SurfaceFieldPath
  declaration : FlatFieldDecl
  bound : Rat
  modelWellFormed : model.validate.isOk = true
  resolved :
    model.resolveNonrepeatableFieldUnchecked rowGroup authoredField = .ok declaration
  rawString : declaration.isRawString = true
  integralBound : bound.den = 1

namespace CheckedRawStringMaximumLength

def fieldId (checked : CheckedRawStringMaximumLength model) : FieldId :=
  checked.declaration.id

def integerBound (checked : CheckedRawStringMaximumLength model) : Int :=
  checked.bound.num

end CheckedRawStringMaximumLength

/-- Checked authoring produces either executable validation or eliminated raw-String metadata, never a sentinel runtime condition. -/
inductive CheckedFlatRuleCondition (model : FlatModel) where
  | runtime (condition : CheckedFlatCondition model)
  | rawStringMaximumLength (metadata : CheckedRawStringMaximumLength model)

namespace CheckedFlatRuleCondition

def toRuntime? : CheckedFlatRuleCondition model → Option (CheckedFlatCondition model)
  | .runtime condition => some condition
  | .rawStringMaximumLength _ => none

def toRawMaximum? : CheckedFlatRuleCondition model → Option (FieldId × Int)
  | .runtime _ => none
  | .rawStringMaximumLength metadata =>
      some (metadata.fieldId, metadata.integerBound)

end CheckedFlatRuleCondition

namespace Except

def toRawMaximum? :
    Except ElabError (CheckedFlatRuleCondition model) → Option (FieldId × Int)
  | .ok checked => checked.toRawMaximum?
  | .error _ => none

end Except

private def elaborateRawStringMaximumLength (model : FlatModel)
    (declaringGroup : GroupPath) (authoredField : SurfaceFieldPath)
    (bound : Rat) (modelValid : model.validate = .ok ()) :
    Except ElabError (Option (CheckedRawStringMaximumLength model)) :=
  match hResolved :
      model.resolveNonrepeatableFieldUnchecked declaringGroup authoredField with
  | .error error => .error (.resolve error)
  | .ok declaration =>
      if hRaw : declaration.isRawString = true then
        if hIntegral : bound.den = 1 then
          .ok (some {
            rowGroup := declaringGroup
            authoredField
            declaration
            bound
            modelWellFormed := by rw [modelValid]; rfl
            resolved := hResolved
            rawString := hRaw
            integralBound := hIntegral })
        else
          .error (.rawStringLength declaration.path)
      else
        .ok none

/-- Recognize raw max-length metadata before ordinary condition lowering. Strictness and operand order are exact; every other raw length occurrence reaches `elaborate` and is rejected. -/
def elaborateFlatRuleCondition (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) :
    Except ElabError (CheckedFlatRuleCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () =>
      let candidate := match condition with
        | .lengthCompare .greater field bound =>
            some (field, bound)
        | .literalCompareLength bound .less field =>
            some (field, bound)
        | _ => none
      match candidate with
      | some (field, bound) => do
          match ← elaborateRawStringMaximumLength model declaringGroup field bound hModel with
          | some metadata => pure (.rawStringMaximumLength metadata)
          | none => do
              let checked ← elaborate model declaringGroup condition
              pure (.runtime checked)
      | none => do
          let checked ← elaborate model declaringGroup condition
          pure (.runtime checked)

end A12Kernel
