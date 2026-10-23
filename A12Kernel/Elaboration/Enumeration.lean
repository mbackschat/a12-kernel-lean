import A12Kernel.Semantics.Enumeration
import A12Kernel.Elaboration.EnumerationComparability
import A12Kernel.Semantics.String

/-! # A12Kernel.Elaboration.Enumeration — checked ordinary closed declarations

This capsule checks the shared declaration facts needed by stored-token comparison, localized display comparability, and positional category projection. It admits only ordinary closed Enumerations. Table-backed, open, dynamic, partial, and extensible forms remain outside.
-/

namespace A12Kernel

/-- One named category vector in the same declaration order as the stored-token domain. -/
structure EnumerationCategoryDeclaration where
  name : String
  tokens : List String
  deriving Repr, DecidableEq

/-- The normalized ordinary closed declaration. Display facts are flat so the existing comparability profile consumes them without another representation. -/
structure EnumerationDeclaration where
  storedTokens : List String
  displayFacts : List EnumerationDisplayFact := []
  categories : List EnumerationCategoryDeclaration := []
  /-- The optional model-owned default text used by eligible index-default staging, as written: a padded
  or blank one is admitted by its trim yet staged untrimmed, so it need not be a stored token (peer KF574). -/
  defaultStoredToken : Option String := none
  deriving Repr, DecidableEq

inductive EnumerationDeclarationError where
  | emptyStoredDomain
  | duplicateStoredToken (token : String)
  | unknownDefaultStoredToken (token : String)
  | emptyDisplayLocale (stored : String)
  | emptyDisplayText (locale stored : String)
  | unknownDisplayStoredToken (locale stored : String)
  | duplicateDisplayStoredToken (locale stored : String)
  | duplicateDisplayText (locale display : String)
  | incompleteDisplayLocale (locale stored : String)
  | emptyCategoryName (index : Nat)
  | duplicateCategoryName (name : String)
  | categoryArityMismatch (name : String) (expected actual : Nat)
  | emptyCategoryToken (name : String) (index : Nat)
  deriving Repr, DecidableEq

private def firstEmptyIndex? : List String → Nat → Option Nat
  | [], _ => none
  | value :: remaining, index =>
      if value.isEmpty then some index else firstEmptyIndex? remaining (index + 1)

private def firstDuplicate? : List String → Option String
  | [] => none
  | value :: remaining =>
      if remaining.contains value then some value else firstDuplicate? remaining

/-- The S-value law reads the default and the tokens after Java's `String.trim`, and asks nothing of a
default that trims to nothing (spec/01 §1.3). -/
private def invalidDefaultStoredToken? (storedTokens : List String) :
    Option String → Option EnumerationDeclarationError
  | none => none
  | some token =>
      if (javaTrim token).isEmpty || (storedTokens.map javaTrim).contains (javaTrim token) then none
      else some (.unknownDefaultStoredToken token)

private def invalidDisplayFact? (storedTokens : List String) :
    List EnumerationDisplayFact → Option EnumerationDeclarationError
  | [] => none
  | fact :: remaining =>
      if fact.locale.isEmpty then
        some (.emptyDisplayLocale fact.stored)
      else if fact.display.isEmpty then
        some (.emptyDisplayText fact.locale fact.stored)
      else if !storedTokens.contains fact.stored then
        some (.unknownDisplayStoredToken fact.locale fact.stored)
      else if remaining.any (fun candidate =>
          candidate.locale == fact.locale && candidate.stored == fact.stored) then
        some (.duplicateDisplayStoredToken fact.locale fact.stored)
      else if remaining.any (fun candidate =>
          candidate.locale == fact.locale && candidate.display == fact.display) then
        some (.duplicateDisplayText fact.locale fact.display)
      else
        invalidDisplayFact? storedTokens remaining

private def incompleteDisplay? (facts : List EnumerationDisplayFact)
    (storedTokens : List String) : List String → Option EnumerationDeclarationError
  | [] => none
  | locale :: remaining =>
      match storedTokens.find? (fun stored =>
          !facts.any (fun fact => fact.locale == locale && fact.stored == stored)) with
      | some stored => some (.incompleteDisplayLocale locale stored)
      | none => incompleteDisplay? facts storedTokens remaining

private def invalidCategory? (expectedArity : Nat) :
    List EnumerationCategoryDeclaration → Nat → Option EnumerationDeclarationError
  | [], _ => none
  | category :: remaining, index =>
      if category.name.isEmpty then
        some (.emptyCategoryName index)
      else if remaining.any (fun candidate => candidate.name == category.name) then
        some (.duplicateCategoryName category.name)
      else if category.tokens.length != expectedArity then
        some (.categoryArityMismatch category.name expectedArity category.tokens.length)
      else
        match firstEmptyIndex? category.tokens 0 with
        | some tokenIndex => some (.emptyCategoryToken category.name tokenIndex)
        | none => invalidCategory? expectedArity remaining (index + 1)

/-- Validate the shared ordinary closed declaration invariants in deterministic source order. Identity displays are legal, and category tokens may repeat because category projection is many-to-one. An empty stored token is legal: the Kernel loads it and admits it as a value-list literal, while a stored empty cell stays empty, so no cell ever holds it (empty-token capture, 2026-10-14). -/
def EnumerationDeclaration.validate (declaration : EnumerationDeclaration) :
    Except EnumerationDeclarationError Unit :=
  if declaration.storedTokens.isEmpty then
    .error .emptyStoredDomain
  else
    -- Stored values are distinct after Java's `trim`, so `BASIC` beside a padded `BASIC` is refused
    -- (2026-10-21 §2.4).
    match firstDuplicate? (declaration.storedTokens.map javaTrim) with
    | some token => .error (.duplicateStoredToken token)
    | none =>
        match invalidDefaultStoredToken? declaration.storedTokens
            declaration.defaultStoredToken with
        | some error => .error error
        | none =>
            match invalidDisplayFact? declaration.storedTokens declaration.displayFacts with
            | some error => .error error
            | none =>
                let locales := declaration.displayFacts.map (·.locale) |>.eraseDups
                match incompleteDisplay? declaration.displayFacts declaration.storedTokens locales with
                | some error => .error error
                | none =>
                    match invalidCategory? declaration.storedTokens.length declaration.categories 0 with
                    | some error => .error error
                    | none => .ok ()

private theorem firstDuplicate?_eq_none_nodup :
    ∀ tokens : List String, firstDuplicate? tokens = none → tokens.Nodup
  | [], _ => List.nodup_nil
  | value :: remaining, none_ => by
      unfold firstDuplicate? at none_
      split at none_
      · contradiction
      · exact List.nodup_cons.mpr
          ⟨by simpa using ‹¬remaining.contains value = true›,
            firstDuplicate?_eq_none_nodup remaining none_⟩

private theorem invalidCategory?_eq_none_arity (expectedArity : Nat) :
    ∀ (categories : List EnumerationCategoryDeclaration) (index : Nat),
      invalidCategory? expectedArity categories index = none →
        ∀ category ∈ categories, category.tokens.length = expectedArity
  | [], _, _ => by simp
  | category :: remaining, index, none_ => by
      unfold invalidCategory? at none_
      split at none_
      · contradiction
      · split at none_
        · contradiction
        · split at none_
          · contradiction
          · have sameArity : category.tokens.length = expectedArity := by
              simpa using ‹¬(category.tokens.length != expectedArity) = true›
            split at none_
            · contradiction
            · intro candidate member
              cases List.mem_cons.mp member with
              | inl same => subst same; exact sameArity
              | inr later =>
                  exact invalidCategory?_eq_none_arity expectedArity remaining (index + 1)
                    none_ candidate later

/-- A validated declaration lists each stored token once even after Java's `trim` and gives every category exactly one token per stored token. Declaration-notification laws consume this shape instead of re-deriving it from the ordered refusal chain. -/
theorem EnumerationDeclaration.validate_ok_shape (declaration : EnumerationDeclaration)
    (valid : declaration.validate = .ok ()) :
    (declaration.storedTokens.map javaTrim).Nodup ∧
      ∀ category ∈ declaration.categories,
        category.tokens.length = declaration.storedTokens.length := by
  unfold EnumerationDeclaration.validate at valid
  dsimp only at valid
  repeat' split at valid
  all_goals first
    | contradiction
    | exact ⟨firstDuplicate?_eq_none_nodup _ ‹firstDuplicate? (declaration.storedTokens.map javaTrim) = none›,
        invalidCategory?_eq_none_arity _ _ _
          ‹invalidCategory? declaration.storedTokens.length declaration.categories 0 = none›⟩

/-- The proof-bearing declaration consumed by the existing resolved Enumeration boundaries. -/
structure CheckedEnumerationDeclaration where
  declaration : EnumerationDeclaration
  wellFormed : declaration.validate = .ok ()

def elaborateEnumeration (declaration : EnumerationDeclaration) :
    Except EnumerationDeclarationError CheckedEnumerationDeclaration :=
  match valid : declaration.validate with
  | .ok () => .ok { declaration, wellFormed := valid }
  | .error error => .error error

/-- Successful declaration checking preserves the exact authored declaration. This small bridge is shared by every model-owned consumer that attaches the checked Enumeration to a resolved field. -/
theorem elaborateEnumeration_declaration_eq
    (source : EnumerationDeclaration) (checked : CheckedEnumerationDeclaration)
    (elaborated : elaborateEnumeration source = .ok checked) :
    checked.declaration = source := by
  unfold elaborateEnumeration at elaborated
  split at elaborated
  · cases elaborated
    rfl
  · contradiction

/-- A checked S-value trims to nothing or to the trim of a stored token. It need not be a stored token
itself, since staging keeps the text as written. -/
theorem CheckedEnumerationDeclaration.defaultStoredToken_admitted
    (checked : CheckedEnumerationDeclaration) (token : String)
    (selected : checked.declaration.defaultStoredToken = some token) :
    (javaTrim token).isEmpty ∨ javaTrim token ∈ checked.declaration.storedTokens.map javaTrim := by
  have valid := checked.wellFormed
  unfold EnumerationDeclaration.validate at valid
  rw [selected] at valid
  cases named : ((javaTrim token).isEmpty ||
      (checked.declaration.storedTokens.map javaTrim).contains (javaTrim token))
  · simp only [invalidDefaultStoredToken?, named, Bool.false_eq_true, ↓reduceIte] at valid
    repeat' split at valid
    all_goals contradiction
  · simpa using named

def CheckedEnumerationDeclaration.displayProfile
    (checked : CheckedEnumerationDeclaration) : ResolvedEnumerationDisplay :=
  { facts := checked.declaration.displayFacts }

def CheckedEnumerationDeclaration.directComparableField
    (checked : CheckedEnumerationDeclaration) : DirectComparableField :=
  .enumeration checked.displayProfile

/-- The ordinary runtime projection reads the exact checked stored token. -/
def CheckedEnumerationDeclaration.storedProjection
    (_checked : CheckedEnumerationDeclaration) : ResolvedEnumerationProjection :=
  .stored

/-- Resolve one exact category name to the positional runtime projection over the checked stored-token domain. -/
def CheckedEnumerationDeclaration.categoryProjection?
    (checked : CheckedEnumerationDeclaration) (name : String) :
    Option ResolvedEnumerationProjection :=
  match checked.declaration.categories.find? (fun category => category.name == name) with
  | none => none
  | some category =>
      some (.category {
        storedTokens := checked.declaration.storedTokens
        categoryTokens := category.tokens })

/-- Resolve one stored token through an exact checked category name. -/
def CheckedEnumerationDeclaration.categoryTokenFor?
    (checked : CheckedEnumerationDeclaration) (name stored : String) : Option String :=
  checked.categoryProjection? name >>= fun projection => projection.tokenFor? stored

end A12Kernel
