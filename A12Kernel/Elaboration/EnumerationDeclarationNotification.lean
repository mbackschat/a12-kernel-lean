import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Elaboration.Enumeration
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.LegalCharset

/-! # A12Kernel.Elaboration.EnumerationDeclarationNotification — notifications an ordinary Enumeration declaration raises

The Kernel checks an ordinary Enumeration declaration by collecting notifications, not by stopping at the first refusal, so the multiplicity of each class is observable. `EnumerationDeclaration.validate` answers with its first refusal; this module is the collection the Kernel reports, measured against kernel 30.8.1 over a retained capture (`evidence/kernel-30.8.1/captures/enumeration-declaration-findings-2026-10-13/`).

`EnumerationDeclaration.notifications` concatenates seven blocks in this order, then keeps only the first occurrence of each notification:

1. A rejected character of a stored token, one notification per rejected UTF-16 code unit, in declaration order. Only a restricted model charset produces this block; the default charset admits any BMP text.
2. One codeless supplementary-plane notification for the whole field when a stored token or a display text holds a supplementary-plane scalar, whatever the charset.
3. One `MVK_NAME_MISSING` for the whole field when a category's name is empty or Java-blank, which kernel 31.1.1 states once at the field (peer `CheckerEmptyMemberAgreementTest` at `1124b523f`, KF367 and KF658). Such a category is paired with nothing, so it takes no part in the next two blocks nor in block 5. That a surplus or a duplicate is also withheld for it is the peer checker's reading, not a measured row: the measured row is its shortfall.
4. Category arity, paired with the stored values by position: every named category's shortfall notifications (a stored value whose position holds no token, past the end of the list or an empty, blank or `null` token), then every named category's surplus notifications (a filled token past the stored-value count, where a blank one is no token and is admitted; peer KF660, `CheckerCategoryTokenAgreementTest`). A value holding a supplementary scalar draws no shortfall notification, though its position still counts toward the arity.
5. One category-value duplicate per duplicated stored value and named category, value-major. The retained rows observe class codes only, so value-major versus category-major is a choice the evidence does not separate.
6. One internal-values duplicate per duplicated stored value.
7. One codeless repeated-value notification per duplicated stored value.

Blocks 4 to 6 read values and tokens after Java's `trim`, so `BASIC` beside `BASIC ` is a duplicate and `HI` beside `HI ` one surplus notification, while block 7 compares them as written and the restricted scan of block 1 judges every written unit ([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.4). The supplementary carriers of block 2 include category tokens and the default value (§2.3). Blocks 5 and 6 skip a duplicated value holding a supplementary scalar; block 7 does not. Collapsing identical notifications is what makes a repeated unclassified value, a repeated surplus token or a repeated rejected character count once. Rows that mix surplus and shortfall categories in either order, including three-category alternations, place every shortfall before every surplus, which neither a category-by-category nor a reverse-category walk gives. The order of categories inside one half is not observable through class codes and stays a choice.

An empty stored-token list yields no notifications because the Kernel never builds such a model; the validator's refusal stays the answer there. So does a declaration whose categories collide on one name, the empty name and an absent one reading as the one key `null`: the readers leave no model there, before any notification is drawn.

Not claimed: categories whose names hold supplementary scalars, defects of display facts other than the supplementary scalar, extensible-Enumeration hint lists, and table-backed Enumerations.
-/

namespace A12Kernel

/-- One notification an ordinary Enumeration declaration raises. Every class is an ERROR. The two without a Kernel code are distinguished by constructor, not by a placeholder code. -/
inductive EnumerationDeclarationNotification where
  /-- One rejected UTF-16 code unit of a stored token under a restricted model charset. -/
  | invalidCharacter (value : String) (unit : Nat)
  /-- A supplementary-plane scalar in a stored token or a display text; raised once per field. -/
  | supplementaryCharacter
  /-- A category named by nothing, the empty text or Java-blank text; raised once per field. -/
  | categoryNameMissing
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
  | .categoryNameMissing => some "MVK_NAME_MISSING"
  | .missingCategoryValue _ _ => some "MVK_MISSING_CATEGORY_VALUE"
  | .missingInternalValue _ _ => some "MVK_MISSING_INTERNAL_VALUE"
  | .categoryValueDuplicate _ _ => some "MVK_CATEGORY_VALUE_DUPLICATE"
  | .internalValuesDuplicate _ => some "MVK_INTERNAL_VALUES_DUPLICATE"
  | .repeatedValue _ => none

end EnumerationDeclarationNotification

namespace EnumerationDeclaration

/-- Whether a stored token, a display text, a category token or the default value holds a
supplementary-plane scalar. Category names are outside the measured scope. -/
def containsSupplementaryScalar (declaration : EnumerationDeclaration) : Bool :=
  declaration.storedTokens.any hasSupplementaryScalar ||
    declaration.displayFacts.any (hasSupplementaryScalar ·.display) ||
    declaration.categories.any (·.tokens.any hasSupplementaryScalar) ||
    declaration.defaultStoredToken.any hasSupplementaryScalar

/-- The distinct values occurring more than once, in first-occurrence order. -/
def duplicated (tokens : List String) : List String :=
  tokens.eraseDups.filter fun token => 1 < tokens.count token

/-- The distinct stored values occurring more than once as written. -/
def duplicatedStoredTokens (declaration : EnumerationDeclaration) : List String :=
  duplicated declaration.storedTokens

/-- The distinct stored values occurring more than once after Java's `trim`. -/
def duplicatedTrimmedTokens (declaration : EnumerationDeclaration) : List String :=
  duplicated (declaration.storedTokens.map javaTrim)

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

/-- The categories that pair with the stored values: those with a name. -/
def namedCategories (declaration : EnumerationDeclaration) : List EnumerationCategoryDeclaration :=
  declaration.categories.filter fun category => !ExecutableDeclaration.blank category.name

/-- Block 3. -/
def categoryNameNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  if declaration.categories.any fun category => ExecutableDeclaration.blank category.name then
    [.categoryNameMissing]
  else []

/-- Block 4, shortfall half: each named category lacks a token for the stored value at a position its list
leaves empty, blank or `null` or does not reach, except values holding a supplementary scalar. -/
def shortfallNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  declaration.namedCategories.flatMap fun category =>
    ((declaration.storedTokens.mapIdx fun index value => (value, category.tokens[index]?)).filter
      fun (value, token) => token.all ExecutableDeclaration.blank && !hasSupplementaryScalar value).map
        fun (value, _) => .missingCategoryValue category.name (javaTrim value)

/-- Block 4, surplus half: each filled category token past the stored-value count has no stored value. -/
def surplusNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  declaration.namedCategories.flatMap fun category =>
    ((category.tokens.drop declaration.storedTokens.length).filter
      fun token => !ExecutableDeclaration.blank token).map
        (.missingInternalValue category.name ∘ javaTrim)

/-- Block 5, value-major. -/
def categoryDuplicateNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  (declaration.duplicatedTrimmedTokens.filter fun value => !hasSupplementaryScalar value).flatMap
    fun value => declaration.namedCategories.map fun category =>
      .categoryValueDuplicate value category.name

/-- Block 6. -/
def internalDuplicateNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  (declaration.duplicatedTrimmedTokens.filter fun value => !hasSupplementaryScalar value).map
    .internalValuesDuplicate

/-- Block 7, one per repeated stored value in first-occurrence order. The order is this account's
choice, not a claim: the Kernel's order matches neither declaration nor second-occurrence order on the
five rows measured, and alphabetical order on only one (peer KF647 and a local probe of 2026-10-29,
`docs/sources/inbound-handbacks.md#src-inbound-2026-10-29`). -/
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
      declaration.categoryNameNotifications ++
      declaration.shortfallNotifications ++
      declaration.surplusNotifications ++
      declaration.categoryDuplicateNotifications ++
      declaration.internalDuplicateNotifications ++
      declaration.repeatedValueNotifications).eraseDups

end EnumerationDeclaration

/-- Whether two categories share a name as the Kernel keys them: the empty name and an absent one are the one
key `null`, so two categories that each carry neither collide, while two blank names that differ as text do
not. The Kernel builds no model from such a declaration. -/
def categoryNamesCollide (categories : List EnumerationCategoryDeclaration) : Bool :=
  let names := categories.map (·.name)
  names.eraseDups.length < names.length

end A12Kernel
