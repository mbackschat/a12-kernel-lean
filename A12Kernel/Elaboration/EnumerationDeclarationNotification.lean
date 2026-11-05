import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Elaboration.Enumeration
import A12Kernel.Elaboration.JavaHashMapOrder
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.LegalCharset

/-! # A12Kernel.Elaboration.EnumerationDeclarationNotification — notifications an ordinary Enumeration declaration raises

The Kernel checks an ordinary Enumeration declaration by collecting notifications, not by stopping at the first refusal, so the multiplicity of each class is observable. `EnumerationDeclaration.validate` answers with its first refusal; this module is the collection the Kernel reports, measured against kernel 30.8.1 over a retained capture (`evidence/kernel-30.8.1/captures/enumeration-declaration-findings-2026-10-13/`).

`EnumerationDeclaration.notifications` concatenates eight blocks in this order, then keeps only the first occurrence of each notification:

1. A rejected character of a stored token, one notification per rejected UTF-16 code unit, in declaration order. Only a restricted model charset produces this block; the default charset admits any BMP text.
2. One codeless supplementary-plane notification for the whole field when a stored token or a display text holds a supplementary-plane scalar, whatever the charset.
3. One `MVK_NAME_MISSING` for the whole field when a category's name is empty or Java-blank, which kernel 31.1.1 states once at the field (peer `CheckerEmptyMemberAgreementTest` at `1124b523f`, KF367 and KF658). Such a category is paired with nothing, so it takes no part in the next two blocks nor in block 5. That a surplus or a duplicate is also withheld for it is the peer checker's reading, not a measured row: the measured row is its shortfall.
4. Category arity, paired with the value entries by position: every named category's shortfall notifications (a stored value whose position holds no token, past the end of the list or an empty, blank or `null` token), then every named category's surplus notifications (a filled token at a position no stored value holds, past the last entry or at an entry that declares no token, where a blank one is no token and is admitted; peer KF660, `CheckerCategoryTokenAgreementTest`). A value holding a supplementary scalar draws no shortfall notification, though its position still counts toward the arity. An entry that declares no token keeps its position, so the values after it still pair by position (kernel 31.1.1, a12-dmkits `CheckerReaderBindingAgreementTest` at 1124b523f, KF655), and it is named by no shortfall notification, there being no value to name; whether one at a position with no category token is judged is unmeasured.
5. One category-value duplicate per duplicated stored value and named category, value-major. The retained rows observe class codes only, so value-major versus category-major is a choice the evidence does not separate.
6. One internal-values duplicate per duplicated stored value.
7. One codeless repeated-value notification per duplicated stored value, and one more when two or more entries declare no token: the absent token repeats as a stored token does, while blocks 5 and 6 read trimmed tokens and never reach it (a12-dmkits `CheckerReaderBindingAgreementTest` at 1124b523f: two token-less entries draw this class and neither duplicate class).
8. One `MVK_INTERNAL_VALUES_MISSING` when entries exist and none declares a token. Its position among the blocks after block 4 is unmeasured: only its place after the surplus half of block 4 is observed (a12-dmkits `EnumCategoryWireShapeLawsTest` at 1124b523f), the other rows comparing class sets.

Blocks 4 to 6 read values and tokens after Java's `trim`, so `BASIC` beside `BASIC ` is a duplicate and `HI` beside `HI ` one surplus notification, while block 7 compares them as written and the restricted scan of block 1 judges every written unit ([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.4). The supplementary carriers of block 2 include category tokens and the default value (§2.3). Blocks 5 and 6 skip a duplicated value holding a supplementary scalar; block 7 does not. Collapsing identical notifications is what makes a repeated unclassified value, a repeated surplus token or a repeated rejected character count once. Rows that mix surplus and shortfall categories in either order, including three-category alternations, place every shortfall before every surplus, which neither a category-by-category nor a reverse-category walk gives. The order of categories inside one half is not observable through class codes and stays a choice.

A declaration with no value entry at all yields no notifications because the Kernel never builds such a model; the validator's refusal stays the answer there. So does a declaration whose categories collide on one name, the empty name and an absent one reading as the one key `null`: the readers leave no model there, before any notification is drawn.

Not claimed: categories whose names hold supplementary scalars, defects of display facts other than the supplementary scalar, extensible-Enumeration hint lists, and table-backed Enumerations.
-/

namespace A12Kernel

/-- One notification an ordinary Enumeration declaration raises. Every class is an ERROR. The two without a Kernel code are distinguished by constructor, not by a placeholder code. -/
inductive EnumerationDeclarationNotification where
  /-- One rejected UTF-16 code unit of a stored token under a restricted model charset. -/
  | invalidCharacter (value : String) (unit : Nat)
  /-- A supplementary-plane scalar in a stored token or a display text; raised once per field. -/
  | supplementaryCharacter
  /-- Entries exist and none declares a token; raised once per field. -/
  | internalValuesMissing
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
  /-- The absent token repeating, as two or more entries declaring none: the codeless class of `repeatedValue`. -/
  | repeatedTokenless
  deriving Repr, DecidableEq

namespace EnumerationDeclarationNotification

/-- The Kernel code of the notification, absent for the two classes the Kernel raises without one. -/
def kernelCode? : EnumerationDeclarationNotification → Option String
  | .invalidCharacter _ _ => some KernelStaticDiagnostic.enumValueWithInvalidCharacter.kernelCode
  | .supplementaryCharacter => none
  | .internalValuesMissing => some "MVK_INTERNAL_VALUES_MISSING"
  | .categoryNameMissing => some "MVK_NAME_MISSING"
  | .missingCategoryValue _ _ => some "MVK_MISSING_CATEGORY_VALUE"
  | .missingInternalValue _ _ => some "MVK_MISSING_INTERNAL_VALUE"
  | .categoryValueDuplicate _ _ => some "MVK_CATEGORY_VALUE_DUPLICATE"
  | .internalValuesDuplicate _ => some "MVK_INTERNAL_VALUES_DUPLICATE"
  | .repeatedValue _ => none
  | .repeatedTokenless => none

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

/-- The positions of the entries that declare no token, the inverse of `valueEntries` over the tokens kept. -/
def tokenlessPositionsOf (entries : List (Option String)) : List Nat :=
  (entries.mapIdx fun index entry => (index, entry)).filterMap fun (index, entry) =>
    if entry.isNone then some index else none

/-- The value entries in declaration order, `none` for an entry that declares no token. The entries are the
stored tokens with a hole at each of `tokenlessPositions`. -/
def valueEntries (declaration : EnumerationDeclaration) : List (Option String) :=
  (List.range (declaration.storedTokens.length + declaration.tokenlessPositions.length)).map fun position =>
    if declaration.tokenlessPositions.contains position then none
    else declaration.storedTokens[position - (declaration.tokenlessPositions.filter (· < position)).length]?

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
    ((declaration.valueEntries.mapIdx fun index entry => (entry, category.tokens[index]?)).filterMap
      fun (entry, token) => entry.bind fun value =>
        if token.all ExecutableDeclaration.blank && !hasSupplementaryScalar value then
          some (.missingCategoryValue category.name (javaTrim value))
        else none)

/-- Block 4, surplus half: each filled category token at a position no stored value holds, past the last entry
or at an entry that declares no token. -/
def surplusNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  declaration.namedCategories.flatMap fun category =>
    ((category.tokens.mapIdx fun index token => ((declaration.valueEntries[index]?).bind id, token)).filterMap
      fun (entry, token) =>
        if entry.isNone && !ExecutableDeclaration.blank token then
          some (.missingInternalValue category.name (javaTrim token))
        else none)

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

/-- Block 7, one per repeated value, the absent token included, in the iteration order of the map the
Kernel fills with one call per occurrence after the first, as written (a12-dmkits
`CheckerBasicSentenceOrderAgreementTest` at `c7afca597`: four Enumeration rows, a shared bucket and a resize on a third
occurrence among them). Where the absent token falls among the stored values is the map's, unmeasured. -/
def repeatedValueNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  -- The map receives no call when no value repeats; the guard states that through the two repeat counts the
  -- valid-declaration law already holds.
  if declaration.duplicatedStoredTokens.isEmpty && declaration.tokenlessPositions.length < 2 then [] else
  let entries := declaration.valueEntries
  let later := (entries.zipIdx.filter fun (entry, index) => (entries.take index).contains entry).map (·.1)
  (JavaHashMap.iterationOrder later).map fun
    | some value => .repeatedValue value
    | none => .repeatedTokenless

/-- Block 8. -/
def valuesMissingNotifications (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  if declaration.storedTokens.isEmpty && !declaration.tokenlessPositions.isEmpty then [.internalValuesMissing]
  else []

/-- The ordered notifications the Kernel raises for the declaration under the model's charset. The module documentation states the block order and the collapse of identical notifications. -/
def notifications (charset : LegalCharset) (declaration : EnumerationDeclaration) :
    List EnumerationDeclarationNotification :=
  if declaration.valueEntries.isEmpty then []
  else
    (declaration.invalidCharacterNotifications charset ++
      declaration.supplementaryNotifications ++
      declaration.categoryNameNotifications ++
      declaration.shortfallNotifications ++
      declaration.surplusNotifications ++
      declaration.categoryDuplicateNotifications ++
      declaration.internalDuplicateNotifications ++
      declaration.repeatedValueNotifications ++
      declaration.valuesMissingNotifications).eraseDups

end EnumerationDeclaration

/-- Whether two categories share a name as the Kernel keys them: the empty name and an absent one are the one
key `null`, so two categories that each carry neither collide, while two blank names that differ as text do
not. The Kernel builds no model from such a declaration. -/
def categoryNamesCollide (categories : List EnumerationCategoryDeclaration) : Bool :=
  let names := categories.map (·.name)
  names.eraseDups.length < names.length

end A12Kernel
