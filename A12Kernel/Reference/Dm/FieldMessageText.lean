import A12Kernel.Elaboration.RequirednessMessage
import A12Kernel.Elaboration.FieldMessageCheck
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead

/-! # Field-owned message texts read from a DM-JSON field element

The authored text a field reports for its own findings, rendered as the Kernel's full validation
renders it without a display provider: a required field's `requirednessConfig.errorMessage` and an
Enumeration's `errorMessage` for a value outside its domain. A locale's text is the last entry written
for it in a list-valued member, as the field-message check asks it; an object-valued member's winner is not
stated; whether rendering asks the same entry is unmeasured. A
field without an authored text takes the catalog's default, a host input, so these return `none`
there. -/

namespace A12Kernel.Dm

open Lean A12Kernel

private def askedText? (json : Json) (key locale : String) : Except String (Option String) := do
  let entries := (← localizedTextMember json key).map fun (locale, text) => ({ locale, text } : FieldMessageEntry)
  pure (FieldMessageEntry.askedFor? entries locale)

/-- The owning field's display at `locale` in its own messages. -/
def fieldOwnedDisplay (element : Json) (locale : String) : Except String String := do
  pure (fieldOwnedDisplayName (← askedText? (← element.getObjVal? "Field") "label" locale)
    (← element.getObjValAs? String "name"))

/-- The rendered requiredness text of a field element at `locale`. -/
def requirednessMessageText? (element : Json) (locale : String) : Except String (Option String) := do
  let config := ((← element.getObjVal? "Field").getObjVal? "requirednessConfig").toOption.getD (Json.mkObj [])
  match ← askedText? config "errorMessage" locale with
  | none => pure none
  | some template => pure (some (renderRequirednessMessage template (← fieldOwnedDisplay element locale)))

/-- The rendered text an Enumeration field element reports for the stored `value` outside its domain.
Its template meets the String-pattern grammar in the model's condition language, which the model check
has already applied. -/
def enumerationMessageText? (element : Json) (tokens : StringPatternMessageTokens) (locale value : String) :
    Except String (Option String) := do
  let fieldType ← (← element.getObjVal? "Field").getObjVal? "fieldType"
  let body := (fieldType.getObjVal? "EnumerationType").toOption.getD (Json.mkObj [])
  match ← askedText? body "errorMessage" locale with
  | none => pure none
  | some source =>
      let template ← (elaborateStringPatternMessageTemplate tokens source).mapError fun error => s!"{repr error}"
      let inputs : StringPatternMessageInputs := { fieldName := ← fieldOwnedDisplay element locale, fieldValue := value }
      pure (some (template.toRenderPlan inputs).render.text)

end A12Kernel.Dm
