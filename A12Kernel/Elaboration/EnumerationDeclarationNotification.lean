import A12Kernel.Elaboration.Enumeration
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.LegalCharset

/-! # A12Kernel.Elaboration.EnumerationDeclarationNotification — notifications an ordinary Enumeration declaration raises

The Kernel checks an ordinary Enumeration declaration by collecting notifications, not by stopping at the first refusal, so the multiplicity of each class is observable. `EnumerationDeclaration.validate` answers with its first refusal; this module is the collection the Kernel reports, measured against kernel 30.8.1 over a retained capture (`evidence/kernel-30.8.1/captures/enumeration-declaration-findings-2026-10-13/`).

`EnumerationDeclaration.notifications` concatenates six blocks in this order, then keeps only the first occurrence of each notification:

1. A rejected character of a stored token, one notification per rejected UTF-16 code unit, in declaration order. Only a restricted model charset produces this block; the default charset admits any BMP text.
2. One codeless supplementary-plane notification for the whole field when a stored token or a display text holds a supplementary-plane scalar, whatever the charset.
3. Category arity: every category's shortfall notifications (a stored value past the end of the category's token list), then every category's surplus notifications (a token past the stored-value count). A value holding a supplementary scalar draws no shortfall notification, though its position still counts toward the arity.
4. One category-value duplicate per duplicated stored value and category, value-major. The retained rows observe class codes only, so value-major versus category-major is a choice the evidence does not separate.
5. One internal-values duplicate per duplicated stored value.
6. One codeless repeated-value notification per duplicated stored value.

Blocks 4 and 5 skip a duplicated value holding a supplementary scalar; block 6 does not. Collapsing identical notifications is what makes a repeated unclassified value, a repeated surplus token or a repeated rejected character count once. Rows that mix surplus and shortfall categories in either order, including three-category alternations, place every shortfall before every surplus, which neither a category-by-category nor a reverse-category walk gives. The order of categories inside one half is not observable through class codes and stays a choice.

An empty stored-token list yields no notifications because the Kernel never builds such a model; the validator's refusal stays the answer there.

Not claimed: categories whose names or tokens hold supplementary scalars, empty or duplicate category names, empty tokens, defects of display facts other than the supplementary scalar, extensible-Enumeration hint lists, and table-backed Enumerations.
-/

namespace A12Kernel

/-- One notification an ordinary Enumeration declaration raises. Every class is an ERROR. The two without a Kernel code are distinguished by constructor, not by a placeholder code. -/
inductive EnumerationDeclarationNotification where
  /-- One rejected UTF-16 code unit of a stored token under a restricted model charset. -/
  | invalidCharacter (value : String) (unit : Nat)
  /-- A supplementary-plane scalar in a stored token or a display text; raised once per field. -/
  | supplementaryCharacter
  /-- A stored value the category assigns no token to. -/
  | missingCategoryValue (category value : String)
  /-- A category token no stored value corresponds to. -/
  | missingInternalValue (category token : String)
  /-- A duplicated stored value, once per category. -/
  | categoryValueDuplicate (value category : String)
  | internalValuesDuplicate (value : String)
  /-- A duplicated stored value, the codeless companion of the two duplicate classes. -/
  | repeatedValue (value : String)
  deriving Repr, DecidableEq

namespace EnumerationDeclarationNotification

/-- The Kernel code of the notification, absent for the two classes the Kernel raises without one. -/
def kernelCode? : EnumerationDeclarationNotification → Option String
  | .invalidCharacter _ _ => some KernelStaticDiagnostic.enumValueWithInvalidCharacter.kernelCode
  | .supplementaryCharacter => none
  | .missingCategoryValue _ _ => some "MVK_MISSING_CATEGORY_VALUE"
  | .missingInternalValue _ _ => some "MVK_MISSING_INTERNAL_VALUE"
  | .categoryValueDuplicate _ _ => some "MVK_CATEGORY_VALUE_DUPLICATE"
  | .internalValuesDuplicate _ => some "MVK_INTERNAL_VALUES_DUPLICATE"
  | .repeatedValue _ => none

end EnumerationDeclarationNotification

/-- Whether the text holds a scalar outside the Basic Multilingual Plane. -/
def hasSupplementaryScalar (text : String) : Bool :=
  text.toList.any fun character => !isBmpScalar character

namespace EnumerationDeclaration

/-- Whether a stored token or a display text holds a supplementary-plane scalar. Category names and tokens are outside the measured scope. -/
def containsSupplementaryScalar (declaration : EnumerationDeclaration) : Bool :=
  declaration.storedTokens.any hasSupplementaryScalar ||
    declaration.displayFacts.any (hasSupplementaryScalar ·.display)

/-- The distinct stored values occurring more than once, in first-occurrence order. -/
def duplicatedStoredTokens (declaration : EnumerationDeclaration) : List String :=
  declaration.storedTokens.eraseDups.filter fun token =>
    1 < declaration.storedTokens.count token

/-- Block 1. A restricted scan reports every rejected unit of every stored token, duplicates included. -/
def invalidCharacterNotifications (charset : LegalCharset) (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  match charset with
  | .defaultBmp => []
  | .restricted ranges atoms =>
      declaration.storedTokens.flatMap fun value =>
        (restrictedRejectedUnits ranges atoms value).map (.invalidCharacter value)

/-- Block 2. -/
def supplementaryNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  if declaration.containsSupplementaryScalar then [.supplementaryCharacter] else []

/-- Block 3, shortfall half: each category lacks a token for the stored values past its length, except values holding a supplementary scalar. -/
def shortfallNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  declaration.categories.flatMap fun category =>
    ((declaration.storedTokens.drop category.tokens.length).filter
      fun value => !hasSupplementaryScalar value).map
        (.missingCategoryValue category.name)

/-- Block 3, surplus half: each category token past the stored-value count has no stored value. -/
def surplusNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  declaration.categories.flatMap fun category =>
    (category.tokens.drop declaration.storedTokens.length).map
      (.missingInternalValue category.name)

/-- Block 4, value-major. -/
def categoryDuplicateNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  (declaration.duplicatedStoredTokens.filter fun value => !hasSupplementaryScalar value).flatMap
    fun value => declaration.categories.map fun category =>
      .categoryValueDuplicate value category.name

/-- Block 5. -/
def internalDuplicateNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  (declaration.duplicatedStoredTokens.filter fun value => !hasSupplementaryScalar value).map
    .internalValuesDuplicate

/-- Block 6. -/
def repeatedValueNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  declaration.duplicatedStoredTokens.map .repeatedValue

/-- The ordered notifications the Kernel raises for the declaration under the model's charset. The module documentation states the block order and the collapse of identical notifications. -/
def notifications (charset : LegalCharset) (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  if declaration.storedTokens.isEmpty then []
  else
    (declaration.invalidCharacterNotifications charset ++
      declaration.supplementaryNotifications ++
      declaration.shortfallNotifications ++
      declaration.surplusNotifications ++
      declaration.categoryDuplicateNotifications ++
      declaration.internalDuplicateNotifications ++
      declaration.repeatedValueNotifications).eraseDups

end EnumerationDeclaration

end A12Kernel
