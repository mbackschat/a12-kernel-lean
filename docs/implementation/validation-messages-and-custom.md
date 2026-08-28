# Validation, message, and custom capabilities

### §12 — validation and polarity

<a id="cap-whole-rule-semantics"></a>
#### Whole-rule semantics

- `boundary`: Rule condition states the error condition; unified verdict; fired-only addressed message emission
- `owner`: [`ValidationRule.lean`](../../A12Kernel/Semantics/ValidationRule.lean), [`ValidationRule.lean`](../../A12Kernel/Elaboration/ValidationRule.lean)
- `assurance`: E/P closed for admitted rules; selected C/X
- `remains`: Complete message providers: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-ordinary-once-repeatable-execution"></a>
#### Ordinary/once/repeatable execution

- `boundary`: Once execution plus ordinary validation-row loops over checked flat, numeric, temporal, group, and admitted repeatable leaves; nested implicit contexts are separate from concrete stored topology
- `owner`: [`ValidationCondition/`](../../A12Kernel/Elaboration/ValidationCondition/), [`ValidationRule.lean`](../../A12Kernel/Elaboration/ValidationRule.lean)
- `assurance`: E/P closed per admitted leaf; selected C/X; upstream L partial
- `remains`: Wider leaves/paths: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-partial-validation"></a>
#### Partial validation

- `boundary`: Rule-wide filter skip, per-cell relevance masking, and one-sided soundness without an unrestricted full/partial `iff`
- `owner`: [`PartialValidation.lean`](../../A12Kernel/Semantics/PartialValidation.lean), partial rule owners
- `assurance`: E/P closed for admitted rules; LF23 source-closed; selected C/X
- `remains`: Wider addressed/custom leaves: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion), [SG11](../SEMANTICS-GAPS.md#sg11--custom-condition-checked-orchestration)

<a id="cap-fill-group-quantifiers"></a>
#### Fill/group quantifiers

- `boundary`: Validation fill quantifiers plus resolved group predicates/counts over checked topology
- `owner`: [`ValidationFillQuantifier.lean`](../../A12Kernel/Semantics/ValidationFillQuantifier.lean), [`GroupPresence.lean`](../../A12Kernel/Semantics/GroupPresence.lean)
- `assurance`: E/P closed for admitted shapes; upstream L partial; C none
- `remains`: Group-list completeness: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)

<a id="cap-presence-contradiction-analyzer"></a>
#### Presence contradiction analyzer

- `boundary`: Proof-bearing exact-shape analysis that detects a bounded contradictory presence pattern without claiming general satisfiability
- `owner`: [`Flat/PresenceContradiction.lean`](../../A12Kernel/Elaboration/Flat/PresenceContradiction.lean)
- `assurance`: E/P/Q closed for cold Analyze, Verify, and Synthesize tasks over the exact presence fragment. Lean independently certifies the same-field contradiction and replays the different-field witness; raw SMT UNSAT remains bounded solver output rather than proof. No kernel-evidence claim
- `remains`: Wider analysis requires a new consumer hypothesis


### §13 — message interpolation

<a id="cap-whole-rule-authoring-and-rendering"></a>
#### Whole-rule authoring and rendering

- `boundary`: Checked nonempty printable-ASCII flat rule templates admit text, `$$`, `$Field$`, and `$Field.value$`. A parameter's entity spec is the **shared path grammar** the condition parser uses, decoded into the one existing `SurfaceFieldPath` and resolved by the one existing field resolver rather than a second lookup: a bare name, a group-qualified relative path, an absolute path, and a parent walk with an optional explicit turning point all reach a nonrepeatable field, which must be referenced by the condition before direct lowering to the one-pass post-fire renderer. The value suffix is taken at the end of the whole spec, which the grammar itself settles rather than this fragment choosing: the value terminal is not one of the four a name may end with, so a trailing one is always the suffix.
- `boundary`: A name colliding with a terminal is written in the grammar's single-quote escape, erased before lookup so an unnecessary quote is transparent, and the collision is checked at any path level naming the offending segment; this producer's quoting requirement is deliberately narrower than the condition language's, because a caller-supplied set of terminals is historically accepted unquoted inside an entity name. A field reference may instead carry an Enumeration **category** suffix, whose three gates are the Kernel's own in its order — a missing name, a non-Enumeration field, and an undeclared category name reached through the one existing Enumeration projection boundary — and which carries neither the value suffix's non-starred nor value-validation gate, while ordinary condition membership still applies.
- `boundary`: The checked category access renders through the declaration's category mapping. Enumeration `.value` rendering remains caller-supplied in this fragment, with the canonical display contract selecting the declared value label and falling back to the stored token. A reference may finally carry a **semantic-index key**, `For "k"` or `For SomeField`, decoded in last position after any other suffix, with a quoted literal and a keying-field path as its only two spellings and a nested key refused; because a semantic index needs a repeatable group, this nonrepeatable fragment decodes such a parameter and then refuses it at its own boundary rather than borrowing the Kernel's pairing class, and the measured gate it cannot pose is on the **index** rather than on the field.
- `boundary`: One **non-field** form is admitted: the Base Year terminal with an optional signed offset, gated only on the model declaring a Base Year and resolved at authoring because it depends on the model alone. The selected language's spellings are data rather than built in, since the parameter grammar is bilingual and only five terminals differ. A doubled category arrow retains its first suffix long enough for the Kernel's ordered kind and membership gates, so its class depends on that suffix; other unsupported shapes in this bounded fragment remain parse failures. The certificate retains the authored spelling beside its decoded path, so a diagnostic and an Explain consumer can quote what was written
- `owner`: [`ValidationMessageAuthoring.lean`](../../A12Kernel/Elaboration/ValidationMessageAuthoring.lean), [`ValidationRule.lean`](../../A12Kernel/Semantics/ValidationRule.lean)
- `assurance`: E/P closed for the bounded authoring and admitted flat/mixed rendering boundary; **L is exact for the whole static parameter surface** at the [parameter-grammar checkpoint](../SOURCES.md#src-rule-message-parameter-grammar) — every path form including the turning point and its live wrong-name control, the quote escape beside the exemption's own separator, all four category gates, and the Base Year form on both a configured and an unconfigured model — measured first through `rule add --dry-run` and reconciled against the later read-only `rule check --message` route; the doubled-arrow separator is now exact for declared, undeclared, and non-Enumeration first suffixes.
- `assurance`: The **keyed** parameter form is measured at the [semantic-index checkpoint](../SOURCES.md#src-rule-message-semantic-index), which corrected this project's first gate before it shipped: an admitted row keys a field the condition never names, so the gate reads the index and field membership belongs to the unkeyed form alone. **Rendering is calibrated too** at the [parameter-rendering checkpoint](../SOURCES.md#src-rule-message-parameter-rendering), byte-identically on both codegen strategies: the Base Year form's decimal at three offsets beside the dollar escape, the category access's mapped token beside the same field's stored value and its empty-field behaviour under both suffixes, a declared label against an unlabelled field's short name, a scale-0 Number's bare value, an unfilled String's empty default, and an
- `assurance`: unfilled Number with two minimum fractional digits rendering `0.00` beside the min-0/max-2 control rendering `0` — plus a live omission-versus-value polarity cross-check in the `type` channel.
- `assurance`: That batch moved the category access's rendering **out of the caller**: it had been an opaque supplied run precisely because it was unmeasured, and it now renders through the declaration's own category mapping applied to the caller's stored token. The exact locale presentation table is peer-calibrated for ten tags across Date, Number, DateTime, DateRange, and the unchanged Time control, but Lean does not yet derive that presentation from a locale. A declared label provider remains unreachable by this route, which has no provider surface. [SPEC-2026-08-24-01](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-01) is accepted at the [2026-08-23 reconciliation checkpoint](../SOURCES.md#src-2026-08-23-reconciliation); selected C; X none
- `remains`: The remaining non-field parameter forms, a keyed parameter's **admission** and rendering (which need a keyed condition spine this flat fragment has not got), the grammar's accented name letters that the bounded-ASCII template gate refuses first, locale, providers, and repeatable pointers: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-string-pattern-field-messages"></a>
#### String-pattern field messages

- `boundary`: Checked bounded-ASCII `en_US` templates admit only fixed lowercase `$field$` and `$field.value$`, reject the empty `$$` parameter, lower already-selected owning-field bytes once, and attach resolved text without reclassifying the established pattern error. It shares only the lexical gate and the refusal type with the rule producer, so it owns its own module
- `owner`: [`StringPatternMessage.lean`](../../A12Kernel/Elaboration/StringPatternMessage.lean)
- `assurance`: E/P closed for the measured String-pattern producer; upstream L at [source registry](../SOURCES.md); C/X/Q none
- `remains`: Requiredness grammar, other locales, provider invocation, empty-value fallback, and other field-message producers: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-structural-message-references"></a>
#### Structural message references

- `boundary`: The validation rule message's `referenced` channel as a structural projection of the checked condition at one firing environment. It takes no document, context, or verdict, so it cannot degenerate into a read trace. **One shared coordinate rule** reads the concrete prefix out of the *referenced field's own* repeatable scope and wildcards from the first reopened level down, which is what lets a starred field and a starred group's deeper descendant share it without either re-deriving scope; a nonrepeatable reference carries no coordinates at all. Both connectives contribute every branch, and the deduplicated result's order carries no kernel claim because the engine's own collection is a hash set.
- `boundary`: Classified over the `orderedNumeric` leaf's complete delegated scalar atom family, every shape the scalar fragment admits except the refused fixed group count, including UTF-16 `Length`, range, category-projected conversion, and the three temporal differences, whose declarations may be repeatable under addressed admission and are then concrete at the bound row, over its `FirstFilledValue`, Number value-count, and aggregate atoms with unfiltered direct and starred operands, and over its remaining checked sources, so that leaf is now classified for **every** atom constructor with no catch-all: the token value count projects each declaring field instance; group-bearing entity-list, Boolean/Confirm count, group-list, and group-presence leaves delegate their recursive membership and coordinates to [group-operand
- `boundary`: reference projection](../IMPLEMENTATION-MAP.md#cap-group-operand-reference-projection); stored/category and canonical-token projections remain invisible; filtered stars refuse through their optional filter field; and a row-paired `SumOfProducts` projects both value fields under one shared-path certificate, over the ordinary non-starred `repeatableFieldPresence` leaf, so a standard iteration-guard rule projects end to end with the guard's reference merging into the guarded leaf's by deduplication, and over the `flat` and non-model-indexed `numeric` leaves.
- `boundary`: Membership uses one of two strategies chosen by whether the family can carry a starred operand: explicit traversal where it can, or sieving the model's declarations through the family's own exhaustive `referencesField` where it cannot, which inherits exactly that predicate's coverage. Both sieved families qualify structurally rather than by convention: neither the flat leaf constructors nor the scalar numeric atoms admit a star, and each family's predicate covers every constructor with no catch-all. The fixed group count's arm of that predicate reports the whole counted subtree, which is now the measured relation rather than an admission-gate meaning transported into an output channel, so it is sieved like every other atom and the per-atom sievability gate that briefly refused it is deleted.
- `boundary`: Its remaining boundary is that the kernel account is measured on a nonrepeatable model: a subtree field below a repeatable level deeper than the rule binds fails closed at that exact level rather than choosing between a wildcard and a pinned first repetition. Only `RepetitionNotUnique` and the filtered-star operand still **refuse the whole projection** rather than return a partial set that would read as complete
- `owner`: [`Reference.lean`](../../A12Kernel/Elaboration/ValidationCondition/Reference.lean), [proofs](../../A12Kernel/Proofs/ValidationCondition/Reference.lean), [cases](../../A12Kernel/Conformance/ValidationRule/OrdinaryReference.lean)
- `assurance`: E/P closed for that fragment: exactness and arity are proved once at the shared rule, so a reopened pointer provably never collapses to a `CellAddr` and always carries one coordinate per repeatable level, and the starred-field laws are specializations rather than restatements; the two strategies' pointer shapes are proved complementary, since every sieved pointer provably recovers an exact address while every reopened one provably cannot; connective blindness is proved.
- `assurance`: Twelve non-group mutations each fail a retained case: wildcard the bound prefix, never wildcard, off-by-one on `firstStar`, use a fixed single wildcard, sieve a numeric leaf whose fixed group count would have answered, classify only one comparison side, let a context-free atom contribute or refuse, treat a delegated scalar atom as coordinate-free, project one operand of a two-field atom, report projection-specific rather than declaring identity, admit a filtered star through its optional filter, or project one side of a row-paired product. Group-expansion and unstarred-coordinate separators are owned by [the group record](../IMPLEMENTATION-MAP.md#cap-group-operand-reference-projection). Upstream L for the projection rule at a12-dmkits [source registry](../SOURCES.md); C/X/Q none
- `remains`: Filtered-star operand coordinates in all three families that refuse them, the `RepetitionNotUnique` leaf, `fillToFix`, the message-record channel, and the per-part pointer-shape exclusion: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-shared-message-pointer"></a>
#### Shared message pointer

- `boundary`: One resolved field identity plus concrete/wildcard/unknown coordinates, distinct from exact `CellAddr`, reused by every implemented formal-message and callback error channel
- `owner`: [`MessagePointer.lean`](../../A12Kernel/Semantics/MessagePointer.lean), [`MessagePointer.lean`](../../A12Kernel/Proofs/MessagePointer.lean), [`MessagePointer.lean`](../../A12Kernel/Conformance/MessagePointer.lean)
- `assurance`: E/P closed for the normalized field-instance domain; upstream pointer-domain L at [source registry](../SOURCES.md); C/X/Q none
- `remains`: Raw name/index factory asymmetries, root, accessors, and conversions: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-computation-formal-messages"></a>
#### Computation formal messages

- `boundary`: Shared partial-pointer identity and payload-independent computed/residual partition
- `owner`: [`MessagePointer.lean`](../../A12Kernel/Semantics/MessagePointer.lean), [`ComputationMessage.lean`](../../A12Kernel/Semantics/ComputationMessage.lean)
- `assurance`: E/P closed for the current partition; upstream pointer-domain L at [source registry](../SOURCES.md); C/X/Q none
- `remains`: Error-code mapping and localized payload construction: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-custom-field-formal-messages"></a>
#### Custom-field formal messages

- `boundary`: Shared partial pointer, code, severity/type, and resolved text for the admitted custom-field route
- `owner`: [`MessagePointer.lean`](../../A12Kernel/Semantics/MessagePointer.lean), [`CustomFieldFormalMessage.lean`](../../A12Kernel/Semantics/CustomFieldFormalMessage.lean)
- `assurance`: E/P closed for the local field-instance route; upstream pointer-domain L at [source registry](../SOURCES.md); C/X none
- `remains`: Complete formal-message orchestration under [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)


### §14 — custom conditions

<a id="cap-custom-condition-callback"></a>
#### Custom-condition callback

- `boundary`: One reached pure total callback with explicit data/relevance/formal channels and the shared partial error pointer; no hidden host registry in `World`
- `owner`: [`CustomCondition.lean`](../../A12Kernel/Semantics/CustomCondition.lean), [`MessagePointer.lean`](../../A12Kernel/Semantics/MessagePointer.lean)
- `assurance`: E/P/Q closed for the reached representation boundary; pointer-domain L at [source registry](../SOURCES.md); C/X none
- `remains`: Name grammar, registration, host failure, rule orchestration: [SG11](../SEMANTICS-GAPS.md#sg11--custom-condition-checked-orchestration)

<a id="cap-custom-field-validation"></a>
#### Custom-field validation

- `boundary`: Checked registered custom field, bounds, stored-value mode, cause, validity, and formal-message projection
- `owner`: [`CustomField.lean`](../../A12Kernel/Elaboration/CustomField.lean), custom-field semantic owners
- `assurance`: E/P/Q closed for admitted route; upstream L now locks the **per-cell** observation cardinality at a12-dmkits [source registry](../SOURCES.md) across both kernel strategies and the interpreter, which the pure-oracle account satisfies by construction because only an impure validator could observe the count; C/X none
- `remains`: Complete integration: [SG7](../SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion), [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)

<a id="cap-explicit-validity-predicates"></a>
#### Explicit validity predicates

- `boundary`: Two-argument `Valid(field, "Name")` and `Invalid(field, "Name")` over a **partial** host registry. Any nonempty authored name is admitted and carries whatever the world resolved for it, the fixed German no-bounds stored-value context samples a resolved validator, and the value-specified gate answers UNKNOWN for an absent or present-empty operand before any registry contact. A resolved name makes the two polarities exact complements; an unresolved name is degenerate and makes **both** fire VALUE on the same value, with the two indistinguishable no-usable-validator kernel states collapsed deliberately
- `owner`: [`CustomFieldValidity.lean`](../../A12Kernel/Semantics/CustomFieldValidity.lean), [proofs](../../A12Kernel/Proofs/CustomFieldValidity.lean), [cases](../../A12Kernel/Conformance/CustomFieldValidity.lean)
- `assurance`: E/P closed over the registration × fill × polarity matrix, including the proved non-law that complementation needs its resolved hypothesis; Kernel-locked for the unregistered observable by `UnregisteredPredefinedTypeObservableDiffTest` and the strengthened `PredefinedTypeValidityDiffTest` at a12-dmkits [source registry](../SOURCES.md); C/X/Q none
- `remains`: Enumeration and extensible-Enumeration operands, the operand field/wildcard/value-validation static gates, and validation-condition-leaf integration: [SG7](../SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion)
