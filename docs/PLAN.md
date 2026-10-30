# Conformance closure and consumer transition

<a id="active-unit"></a>
## Next action and accepted baseline

- `status`: K01–K22 are accepted. K22 closed on 2026-10-25 at `a8c0dc58`: every gap-shard bullet is a calibration limit, host or representation boundary, consumer item or reopen condition, the final cold review of `0c5b160a..e951cb5e` was disposed in that commit after the [count-amount twin batch](sources/group-count-topology.md#src-k22-runtime-r11), and the [population replay](CONFORMANCE-COVERAGE.md#axis-r--population-replay) matches all 105710 admitted instances of its 4000 rows. The conformance phase is complete.
- `next`: the [spec rewrite](#spec-rewrite-plan) is active; spec/02, spec/10, the spec/14 operator reference, spec/09, spec/07, spec/12, spec/11, spec/05, spec/03, spec/04, spec/06, spec/08, spec/01 and the non-normative SEMANTICS-MAP have landed, the closure check has run over all twelve original chapters, and the cross-chapter pass is done; the [U02 plan](#u02-plan) is [closed](consumer-probes/EXECUTE.md#run-u02-close) against the U01 baseline; its debrief is [triaged](consumer-probes/EXECUTE.md#run-u02-close), and U03 is next. Each later chapter moves its operator membership facts into a spec/14 column. The chapter notes under [reviews/spec-rewrite/](../reviews/spec-rewrite/) carry the edits other chapters owe. U01 is [closed after M4](consumer-probes/EXECUTE.md#run-u01-close) as the baseline for U02, a fresh cold run on the rewritten spec.
- `sync`: the [October 27 handback](sources/inbound-handbacks.md#src-inbound-2026-10-27) settled the 33 spec-rewrite entries, `SPEC-2026-10-26-01` to `-30` and `SPEC-2026-10-27-01` to `-03`: 26 accepted, 4 rejected with the local account corrected, and 3 answered with parts the letter left unmeasured. The [October 28 handback](sources/inbound-handbacks.md#src-inbound-2026-10-28) accepted `SPEC-2026-10-28-01` to `-06`. The [October 28b handback](sources/inbound-handbacks.md#src-inbound-2026-10-28b) accepted `-07` and `-08`. The [October 29a handback](sources/inbound-handbacks.md#src-inbound-2026-10-29a) accepted `SPEC-2026-10-29-01`. The [October 29b handback](sources/inbound-handbacks.md#src-inbound-2026-10-29b) accepted `SPEC-2026-10-29-02`. The [October 29c handback](sources/inbound-handbacks.md#src-inbound-2026-10-29c) accepted `SPEC-2026-10-29-03`, the starred group's non-repeatable descendant coordinate U02's Q-003 found. The [October 29e reconciliation](sources/inbound-handbacks.md#src-inbound-2026-10-29e) accepted `SPEC-2026-10-29-04` and `-05`, U02's Q-004 and Q-005. The [October 30 letter](sources/inbound-handbacks.md#src-inbound-2026-10-30) accepted `SPEC-2026-10-29-06`, the evaluator's refusal of a check-only frame shape. The [October 30a letter](sources/inbound-handbacks.md#src-inbound-2026-10-30a) accepted `SPEC-2026-10-30-01`, the unsupported condition language's classless refusal. The [October 30b letter](sources/inbound-handbacks.md#src-inbound-2026-10-30b) accepted `SPEC-2026-10-30-02`, the Base Year completion of a yearless field copied into a dated target. The [October 30d letter](sources/inbound-handbacks.md#src-inbound-2026-10-30d) accepted `SPEC-2026-10-30-03`, two date operands of different component sets, and `-04`, the yearless day-shift anchor and its year-keeping comparison.
- `decision`: The owner-ordered 2026-10-28 [SG9](gaps/paths-and-groups.md#gap-sg9) keyed-read residuals have landed: the missing-row read, keyed lower groups, the key over a root or fixed-group index and the error-field scope below the key ([below-key routes](sources/model-structure-and-declaration-probes.md#src-below-key-routes), [single-instance key](sources/model-structure-and-declaration-probes.md#src-single-instance-key), [below-key error scope](sources/model-structure-and-declaration-probes.md#src-below-key-error-scope)).
- `cleanup`: The presence-polarity classification is written twice, in `omissionLeafPointers` and `ParallelFieldReference.reads`; R2 found them agreeing. Extract one owner as its own change when either changes. Custom-condition name admission is written in four lowerings; extract one owner as its own change when a fifth carrier needs it.
- `baseline`: K22 passed one integrated build, `lake test` (5924 rule-check rows agree), the trust audit (3051 theorem roots) and the population replay after its last disposition. 171 rows have no matching retained observation and 8 cannot be read or prepared as a whole, four requests needing the host pattern compiler or registered custom validators; matching is calibration over this population only.
- `oracle`: [Inbound provenance](sources/inbound-handbacks.md#src-inbound-2026-10-12) and the owning family checkpoints supply evidence. The [legacy profile disposition](sources/custom-field-probes.md#src-custom-legacy-profile) leaves no outstanding peer request; modern-route implementation and its mode/target distinctions are owned by [custom-field coverage](implementation/validation-messages-and-custom.md#cap-custom-field-validation).
- `calibration`: K18 owns the remaining uncalibrated CustomCondition validation cell. [Construct evidence](CONFORMANCE-CONSTRUCTS.tsv) owns calibration labels; this evidence need is distinct from K01 and peer receipts do not create replay gains.
- `sequence`: K21 checks semantic transport, K22 accepts conformance, then U01 implements the Rust interpreter, U02 repeats it cold on the rewritten spec, and U03 builds the SMT consumer. Concrete repository, dependency and public-contract choices retain their existing decision boundaries.
- `stop`: Stop the conformance phase at K22 and select U01. A genuine blocker keeps its task unchecked. Do not append an automatic conformance-tail programme or require the consumer products before K22.

<a id="single-track-breadth-queue"></a>
## Priority and closure rules

Work in numbered order, one shared mechanism batch at a time. High-risk behavior comes first, including rare triggers: wrong computed values, stale data surviving clears, swallowed failures, cross-row selection leaks and silent admission/metadata loss. Then close ordinary accepted-language reach and consequential evidence gaps. This is an engineering judgment; no production-model frequency data is available.

- Rarity and risk are separate. A high-risk failure of promised coverage cannot be excluded as long tail. K19 owns host/service boundaries; the other tasks own their stated mechanisms. Explicit unsupported/context requirements must not silently become wrong answers.
- An unchecked item is a closure obligation, not automatically a missing implementation. Inspect its named owners, current code, proofs and existing separators once. Sufficient evidence closes the row with an evidence link and a corrected gap claim; do not reimplement, recapture or rebuild it.
- Each listed acceptance matrix is frozen. Fixture values and commands may be concretized at entry, but no semantic axis is added. Name the shared mechanism and falsify it with the listed contrasts. A failure belongs to its existing K task, not a new task or limitations receipt. If two rounds produce prerequisites without acceptance progress, revise the approach within that deliverable.
- Use [focused red/green and the command ladder](TESTING.md#command-ladder), applicable integrated gates, [same-context assessment](TESTING.md#same-context-capsule-closure-assessment) and [triggered cold review](TESTING.md#trigger-based-cold-review). Reuse gates after non-invalidating edits; commits, builds and agent activity are not closure.
- Use retained observations first and follow the [replay cadence](TESTING.md#population-replay-cadence). A new capture needs an unresolved alternative and a finite matrix. Passing it ends the batch; no automatic extra depth, kind or permutation.
- Completion requires the promised reader-to-evaluator/output result, evidence and honest exclusions. Ordinary supported inputs must execute and agree with their oracle; unsupported ordinary inputs remain gaps. A missing in-scope case cannot be relabelled a limitation or hidden by a replay rate over supported cases. Do not create a percentage-measurement programme.
- Preserve order and scope. A concrete dependency may change execution order within these tasks but creates no new deliverable. Adjacency, curiosity and available tooling do not authorize extra work. Detailed semantics remain in linked owners; add no tracking framework, harness or recurring verification loop.

## Context groups and sequential delegation

These groups retain useful context across consecutive tasks. They are not new tasks, acceptance denominators or permission to change numbered risk order. A group can contain several mechanisms whose closures remain separate.

| Tasks | Context retained | Why reuse helps |
|---|---|---|
| K01–K02 | Custom ingestion and computation report boundary | Callback admission, invalid-pointer sets and result assembly share the same source/result distinctions and fixtures. |
| K03–K07 | Addressing, admission and row selection | Authored identity, bound/candidate rows, coverage and pointer contexts reuse the same path and selection owners. |
| K08–K10 | Computation state, reads and application | Producer ordering, clear/poison state and later observation use the same computation lifecycle. |
| K11–K12 | Temporal profile and expression adapters | Declaration formats, precision and world context carry across loading, targets and composed expressions. |
| K13–K15 | Domains, generated findings and rendering | Internal values, diagnostic identity and host display inputs reuse domain and message contracts. |
| K16 | Numeric ingress mechanism | Lexical transport and conversion need their own oracle and source context. |
| K17 | Declaration mechanism | Static declaration findings and refusal precedence need their own admission denominator. |
| K18 | Callback mechanism | Factory resolution, invocation payload and external calibration form a distinct contract. |
| K19–K22 | Convergence, readback and acceptance sequence | Retain evidence and boundary context across distinct disposition, correspondence, consumer-readiness and acceptance decisions; no shared implementation is implied. |

- Keep one writer and one sequential HIGH/MEDIUM/LOW track under the [allocation rule](../CLAUDE.md#highmediumlow-task-allocation). HIGH owns semantic judgment, route discovery, one representative end-to-end path and the finite acceptance matrix before handing off a coherent settled batch. MEDIUM implements the supplied contract with focused red/green; LOW runs gates, sweeps and exactly specified edits; HIGH waits, inspects the actual diff or output and accepts it.
- Reuse the same MEDIUM context within the same mechanism only after explicitly refreshing the changed contract, intervening edits, ownership and stop conditions. Use a fresh MEDIUM context when the mechanism is unrelated. A context group does not establish semantic equivalence or authorize stale assumptions.
- Run integrated and triggered cold review at the frozen family boundary under the existing [review disposition](TESTING.md#review-convergence-and-landing-gate). Name the concrete trigger before commissioning a cold review; a K checkbox or routine acceptance-matrix extension is not itself a reusable capability boundary. Adjacent K tasks may share a gate cycle only when the mechanism and closure are the same; grouping alone never broadens a task or waives its evidence. A warm implementer/reviewer cannot replace the required fresh cold review.

<a id="remaining-conformance-checklist"></a>
## K01–K22 — remaining conformance before consumers

Owner direction, 2026-10-11, resumed with the 2026-10-12 handbacks: close the relevant remaining semantic obligations, then move to actual consumer development, including a Rust interpreter and SMT-backed analysis. K-item status follows verified outcomes, not the existence of a plan or a peer receipt.

The denominator is the current residual mechanisms in all 24 SG families, including the concrete inbound corrections linked below. Each task fixes a finite separating matrix rather than a Cartesian product of every depth, kind and host profile. At entry, recover existing implementation, proofs and observations; sufficient existing evidence can discharge a row without new code. A stale gap is deleted only after that check. A task that only prepares prerequisites remains unchecked.

An implementation task is done when its named reader-to-evaluator/output cases are settled, the shared mechanism and applicable laws/non-laws preserve them, needed correspondence is retained or precisely source-grounded, and applicable gates/review pass. Admission refusals require otherwise-admissible controls and exact promised classes; a generic refusal does not discharge a specific diagnostic obligation. New observations need independent discriminators, including a second composition. A peer implementation choice is not a Kernel oracle.

### K01 — reserved Custom ingestion and continuation

- [x] Close the measured reserved-result behavior through validation, computation and cache admission. [SG7](gaps/strings-and-messages.md#gap-sg7), [test-range source](sources/custom-field-probes.md#src-custom-test-range).
- Matrix: exact `testIDNummer`, ordinary rejection, acceptance and near-spelled keys; raw versus normalized text; absent/empty/relevant/excluded input; seeded/unchanged targets and an independent computation; full examination versus abort mode.
- Done: finding, readable payload, invalid-pointer membership and continuation agree with the committed modern-route observations. Preserve callback invocation order and normalize once.
- The [verified legacy profile boundary](sources/custom-field-probes.md#src-custom-legacy-profile) removes the external profile blocker under the existing expanded-A12 contract. This boundary does not claim the unmeasured legacy true-arm behavior.

### K02 — computation report assembly and whole-call failure

- [x] Reconcile duplicate diagnostic assembly after computation with the returned partitions and application boundary. [SG4](gaps/keystone.md#gap-sg4), [SG16](gaps/keystone.md#gap-sg16), [inbound evidence](sources/inbound-handbacks.md#src-inbound-2026-10-12).
- Matrix: two findings at the same full error pointer versus distinct physical rows; an independent callback computation; selected duplicate versus ordinary malformed source; root-only computation beside an unused custom index.
- Done: computation execution, report assembly failure and availability of an applied snapshot remain distinct. No early abort, swallowed whole-call failure or invented applied result. Use the peer's committed duplicate-diagnostic controls before requesting a capture.

### K03 — captured Having environments and ordered consumption

- [x] Close remaining binding and consumption compositions in [SG17](gaps/paths-and-groups.md#gap-sg17), [SG20](gaps/paths-and-groups.md#gap-sg20) and [SG23](gaps/numeric-and-temporal.md#gap-sg23).
- Matrix: overlap and uniqueness with discriminating disjoint/mixed values under two enclosing rows; ordinary/indexed twins; two off-path captured references and a marked group; full/partial/computation callers; dense threshold and sparse successor versus unread later failure.
- Done: enclosing and candidate rows cannot be interchanged, unavailable/filter-failure states stay distinct, and each consumer retains its scan policy. Reuse the inbound correlation and sparse-consumer observations; source equivalence can discharge another depth without another capture.

### K04 — authored identity and static admission

- [x] Close the remaining reference-classification gates in [SG9](gaps/paths-and-groups.md#gap-sg9), [SG19](gaps/paths-and-groups.md#gap-sg19) and [SG29](gaps/paths-and-groups.md#gap-sg29).
- Matrix: the retained `Other` companion's negative-iteration class and guarded twin; direct/selected/key-field references; group-as-field slots and category/root/duplicate precedence; target self-read before/after common guards; starred CurrentRepetition and repetition-uniqueness sibling fixed-group keys.
- Done: authored identity survives lowering and ordinary levels bind only where admitted. Each distinct gate gets an isolated positive/negative pair; named competing-gate cases keep their precedence. This is not an exhaustive permutation of every diagnostic pair.

### K05 — selected addressing and key fitting

- [x] Close key interpretation and selected row identity in [SG29](gaps/paths-and-groups.md#gap-sg29), including selected error-field reanchoring.
- Matrix: literal/field keys; Number signed zero/scale and String padding/whitespace/UTF-16/non-ASCII distinctions; valid/missing/duplicate keys; same key under two parents; partial lower-star selection with complete/incomplete coverage; selected error/reference/fill coordinates.
- Done: key fit, value availability and message association remain separate. Preserve selected ancestry through nested payload/filter and typed computation callers. Custom codecs receive an explicit contract rather than implicit String coercion.

### K06 — group extent, relevance and capacity

- [x] Close the residual shared product/coverage mechanism in [SG13](gaps/paths-and-groups.md#gap-sg13) and [group runtime](implementation/cross-clause.md#cap-boolean-confirm-group-value-count).
- Matrix: bound ancestor plus three reopened levels; independent and repeated operands; complete/diagonal/missing declared-slot selections; impossible fixed suffix coordinates; absent versus empty versus malformed-only content; capacity overflow with a valid sibling.
- Matrix: Number, token/category and Boolean group callers; presence, counts, memberships, extrema/distinct and generated self-validation use their distinct gates. Include a fully covered negative large-domain control without requiring materialized products.
- Done: current-reader outcomes and coordinates agree across full/partial/computation routes. Fixed-suffix and structural follow-on evidence is reconciled, and no generic coverage helper erases a consumer-specific gate.

### K07 — parallel joins and cross-root dispatch

- [x] Close remaining parallel/cross-root runtime compositions in [SG9](gaps/paths-and-groups.md#gap-sg9), [SG29](gaps/paths-and-groups.md#gap-sg29) and [SG10](gaps/strings-and-messages.md#gap-sg10).
- Matrix: two parents with reversed/same keys; unmatched and invalid keys; numeric lexical aliases; independent ordinary and parallel levels; differing partial selectors; cross-root operands and selected error targets.
- Done: key visits, original leaf relevance, frame traversal and message multiplicity retain their separate identities. The peer's IF376 first-admitted policy is never used as an exact pointer oracle. Host-order-dependent winners remain explicit context requirements checked by K19.

### K08 — computation guards, dependency reads and formal scope

- [x] Close the wider operation/guard compositions in [SG4](gaps/keystone.md#gap-sg4). [Accepted mixed-plan coverage](implementation/computations.md#cap-mixed-computation-plan) and [non-Number tables](implementation/repeatable-computations.md#cap-non-number-alternatives) retain the execution and evidence boundaries.
- Matrix: indexed/correlated membership guard with a fresh computed key/payload; multiple alternatives and repeated targets; parallel operands from different declarations; mixed producer chain with an independent branch; false guard, reached poison and malformed unused operand.
- Done: per-authored-operation preprocessing, dependency ordering, first-match selection and formal-input unions agree. Same-call dependents distinguish clean clear from poison, including equal formal-error inventories. Whole-model admission remains enforced; partial-plan stale storage cannot silently execute.

### K09 — first-filled and cross-carrier value identity

- [x] Close first-filled list and value-identity boundaries in [SG4](gaps/keystone.md#gap-sg4), [SG8](gaps/strings-and-messages.md#gap-sg8) and [SG18](gaps/keystone.md#gap-sg18). [Accepted carrier composition](implementation/strings-and-enumerations.md#cap-first-filled-carrier-composition) records the source, target and evidence boundaries.
- Matrix: own-level/foreign-root stars, nested missing prefix and multi-operand order; String/Enumeration and Boolean/Time carrier pairs with admitted/refused twins; category projection; selected missing/duplicate keys; first available value before a later failure.
- Done: compatible carriers retain their value identity and target rendering, incompatible pairs retain the measured refusal, and scanning neither drops missing-prefix provenance nor evaluates an unread suffix.

### K10 — result projection, application and later observation

- [x] Close the remaining observable application compositions in [SG16](gaps/keystone.md#gap-sg16) and [SG15](gaps/targets-and-derivation.md#gap-sg15). [Accepted typed result/application coverage](implementation/repeatable-computations.md#cap-typed-result-application) records ingress identity, application composition and observation boundaries.
- Matrix: successful unchanged result versus omitted outcome versus clear; seeded/fresh target; target rejection; cross-group/materialized topology; same-model independent destination; subsequent generated/explicit validation and dependent read.
- Done: result partitions, source-relative changes and applied state agree on each materially distinct carrier policy. Preserve original ingress identity where normalization loses it. Separate-destination/object-only observations use their existing source routes and retain API limits; no per-clear causal attribution is invented.

### K11 — temporal loading, interpretation and target policy

- [x] Close declared temporal profile handling in [SG6](gaps/numeric-and-temporal.md#gap-sg6), [SG21](gaps/numeric-and-temporal.md#gap-sg21), [SG15](gaps/targets-and-derivation.md#gap-sg15) and [SG18](gaps/keystone.md#gap-sg18).
- Matrix: format-less default versus explicit format; malformed versus outside-profile stored value; partial/yearless Date with BaseYear and leap boundary; fixed/row target copy versus render; DateTime model-zone discontinuity and omitted target component; world-backed Time components.
- Done: loaded declaration metadata determines interpretation and rendering consistently. Closed formats reuse the shared temporal profile; pre-floor eras and unsupported host-zone data have the explicit boundary verified under K19.

### K12 — temporal expressions and selected range compositions

- [x] Close recursive temporal expression composition in [SG6](gaps/numeric-and-temporal.md#gap-sg6), [SG23](gaps/numeric-and-temporal.md#gap-sg23) and [SG8](gaps/strings-and-messages.md#gap-sg8).
- Matrix: nested Difference with BaseYear on one/both operands; selected/filtered partial Date extraction and ValueAsDate; DateFromDateTime through application; DateRange fragment endpoints with literal/field Number and String keys; missing/duplicate/invalid selected rows and unselected malformed controls.
- Done: comparison, constructor, extraction, overlap, extrema and distinct adapters preserve precision, world context and reached failure. Wrong-kind component and selected-key precedence have admitted twins. Reuse evidence for equivalent profiles; no repeated search for an unwitnessed bare DateRange literal.

### K13 — String, Enumeration and custom field contracts

- [x] Close remaining ingestion, formal checking and domain crossings in [SG7](gaps/strings-and-messages.md#gap-sg7) and [SG8](gaps/strings-and-messages.md#gap-sg8).
- Matrix: raw/checked String and restricted character sets; reached versus bypassed empty pattern; repeated Custom values and newline normalization; Enumeration token versus display/category; membership numeric fallback; closed-domain containment, distinct and uniqueness; custom conversion before/after length/charset checks.
- Done: runtime uses the intended internal value while diagnostics and display use their own representation. Registry/factory lookup, shipped-validator delegation and codecs have explicit invocation contracts; implementing arbitrary external validator algorithms is not required.

### K14 — structural and generated findings

- [x] Close finding multiplicity, suppression and coordinates in [SG10](gaps/strings-and-messages.md#gap-sg10) and [SG7](gaps/strings-and-messages.md#gap-sg7).
- Matrix: Enumeration declarations and withholding combinations; required/empty/default values; nonempty versus empty partial selection; repeated over-capacity present-null/empty fields; generated self-validation after computation; error/reference/fill-to-fix coordinates.
- Done: observable code/type/severity/cardinality and full pointer identity are retained where promised. Independent notifications must not collapse merely because one code is absent. Localized catalog prose stays external.

### K15 — message parameter grammar and rendering inputs

- [x] Close remaining ordinary authoring and structured rendering inputs in [SG25](gaps/strings-and-messages.md#gap-sg25), SG26 and [SG10](gaps/strings-and-messages.md#gap-sg10).
- Matrix: parallel positive-presence guard and invalid hash/repetition parameter; repeatable names and deeper RuleGroup/multi-root references; selected/index/category parameters; four outstanding composed-index/type/display/repeatability refusal classes; empty/default/provider output and computation message context.
- Done: parse success, admission and rendering context remain separate. Compare structured parameters and exact promised diagnostic classes; lexer offsets and all locale wording are not silently claimed. Protected message text is supplied by the host.

### K16 — Number ingress and representation boundaries

- [x] Close material numeric representation distinctions in [SG5](gaps/numeric-and-temporal.md#gap-sg5) and [SG27](gaps/numeric-and-temporal.md#gap-sg27).
- Matrix: authored scale versus rational equality; leading zeros/signed zero/plus/separators; wire overflow and scientific numeric strings; display-to-internal conversion; one-/three-decimal money formatting inputs; guarded versus reached conversion.
- Done: declaration admission, stored validity, arithmetic and display conversion do not substitute for one another. Each supported public ingress preserves relevant original text; unsupported ingress has a named refusal/profile boundary. Money wording remains provider-owned.

### K17 — model declarations and static denominator

- [x] Resolve the residual ordinary declaration surface and classify the six H-model classes in [SG28](sources/model-structure-and-declaration-probes.md#src-field-declaration-notifications-k17), with [SG8](gaps/strings-and-messages.md#gap-sg8), [SG9](gaps/paths-and-groups.md#gap-sg9) and [SG21](gaps/numeric-and-temporal.md#gap-sg21).
- Matrix: empty fixed groups, variant/default declarations, all catalogued field-type bodies, table-backed Enumeration provider metadata, hint/sort references, rule/computation name and notification controls; a condition's first-raised class beside a parse defect and the field type's combined classes beside a refused declaration (from K14); the per-carrier multiplicity of the xml-prefix, value-validation-off String and unspecified-type classes ([KF558](sources/inbound-handbacks.md#src-inbound-kf558-multiplicity)). The Number `-1` fractional sentinel's runtime account ([SG5](gaps/numeric-and-temporal.md#gap-sg5), from K16). The length and digit-count member ranges with their codeless verdicts and silenced dependent laws, and a 61-character nested group name's path-shape notifications ([inbound](sources/inbound-handbacks.md#src-inbound-2026-10-13)).
- Done: every named declaration class is implemented, already evidenced, or tied to a measured/source-defined host/service boundary. Four classes living outside H packages cannot be excluded by package name. No ordinary supported declaration is silently dropped by the reader.

### K18 — CustomCondition callback contract and calibration

- [x] Close the remaining callback invocation evidence in [SG11](gaps/strings-and-messages.md#gap-sg11) and [SG12](gaps/conformance-evidence.md#gap-sg12).
- Matrix: successful/missing factory lookup and precedence; fixed/repeated/parallel contexts; full/partial relevance; exact row coordinates and invalid-pointer payload; reached versus bypassed call.
- Done: the pure callback contract is usable by an independent interpreter, and the currently uncalibrated validation construct cell has retained correspondence evidence. Mutable host effects and arbitrary thrown exceptions remain explicit external behavior, not invented pure semantics.

### K19 — host boundaries and relevance disposition

- [x] Discharge the remaining host/API boundaries and assign every residual bullet a concrete outcome, using all [gap owners](SEMANTICS-GAPS.md).
- Matrix: missing regex/compiler/validator/provider; unavailable temporal profile; absent actual cache-order context beside an unaffected query; incomplete computation plan; non-JSON/object-only input; H-model service versus validation/computation; unobservable clear cause.
- Done: each boundary has a named contract, discriminator and consumer consequence. A restriction is acceptable only when it expresses an actual host dependency, separate service or genuinely unobservable distinction. Missing instrumentation, rarity or an unchecked implementation is not a completion reason.
- D13 mandatory-information analysis and D17 transformation theorems are assigned to the consumer phase below. Prove the required evaluator distinctions now; do not build an analyzer or optimizer as a prerequisite. Any material evaluator omission discovered here returns to its owning K task.

### K20 — correspondence and held-out composition check

- [x] Reconcile [SG12](gaps/conformance-evidence.md#gap-sg12) against the completed K01–K19 matrices, current construct inventory and unchanged replay population.
- Matrix: every formerly uncalibrated cell; each newly implemented observable branch; reported rows without artifacts; explicit host preparation refusals; full/partial/computation/application channels. Each absent row receives a case-level disposition rather than being hidden by admitted-only totals.
- Done: retained evidence is current, material missing observations are resolved, and the applicable integrated, evidence and population gates pass. Use one coherent capture per unresolved family; no blanket recapture or measured-percentage claim.

### K21 — consumer readiness at the semantic boundary

- [x] Run bounded independent Execute and Analyze/Synthesize readbacks against the material a Rust interpreter and SMT consumer will receive. [Use cases](USE-CASES.md), [implementer contract](IMPLEMENTER-GUIDE.md), [SMT proposal](SMT-SOLVER-SUPPORT-PROPOSAL.md). Closed 2026-10-24 by [`k21-execute-02`](consumer-probes/EXECUTE.md#run-k21-execute-02) and [`k21-analyze-synthesize-01`](consumer-probes/ANALYZE.md#run-k21-analyze-synthesize-01) on the [K21 capture](sources/consumer-readiness-probes.md#src-consumer-readiness-k21); the three outputs the packet left unstated entered `spec/` as [SPEC-2026-10-24-01](https://github.com/mbackschat/a12-kernel-lean/blob/255d971f369efe847a4b39d5127b8a290e4f37ff/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-10-24-01).
- Matrix: fresh producer/clear/poison; partial selected rows and duplicate host context; formal versus generated versus authored validity; error-condition reachability versus model acceptance; a finite witness with UNKNOWN/empty input and a computation before validation.
- Done: an isolated consumer can reconstruct these decisions and identify host/bound assumptions without Kernel archaeology. Any missing semantic distinction returns to K01–K19; a missing consumer adapter or shipment is work for U01/U03. Readback success is not Rust or SMT implementation qualification.

### K22 — final conformance acceptance and transition

- [x] Review K01–K21 against every live residual and the declared validation/computation contract. Complete the existing triggered final HIGH review and only invalidated gate reruns. Closed 2026-10-25 at `a8c0dc58`. Kernel coverage and convergence is reached as close as the available evidence and explicit host contracts permit; no known relevant semantic work remains before consumer development. Material limits: the calibration bullets of the [gap shards](SEMANTICS-GAPS.md) name compositions that share a measured mechanism without their own observation, the host boundaries there stay explicit contracts, the [ledger](A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue)'s fifteen pending entries await a12-dmkits reconciliation and reopen their owners if refused, and correspondence is calibrated over the retained population, not proved for every composition.
- Done: all required tasks have evidence-linked dispositions; no known relevant evaluator behavior, static legality, output distinction or consequential evidence gap remains unresolved. Remaining host/service boundaries have K19 dispositions and consumer work has explicit ownership. A checkbox cannot be earned by moving an implementation gap into exclusions.
- The intended report is: “Kernel coverage and convergence is reached as close as the available evidence and explicit host contracts permit; no known relevant semantic work remains before consumer development.” State any material limit alongside it. Do not claim universal equivalence, a measured percentage or that finite tests prove all possible compositions.
- Then select U01. Do not append an automatic conformance-tail programme. A later consumer counterexample reopens its exact semantic owner; it does not restart a general completeness campaign.

<a id="consumer-development"></a>
## After K22 — consumer development

This phase is owner-requested work, not an optional aspiration or another prerequisite for declaring K01–K22 complete. Rust first is the recommended order because an independent evaluator exercises the complete transport contract before SMT adds encoding and solver-trust obligations. Existing [Rust correlation work](IMPLEMENTER-KIT-CORRELATION.md#fresh-rust-runtime-consumer-probe) is a bounded prior asset, not a general interpreter; inspect and reuse it where its contract fits.

- [ ] **U01 — Rust interpreter.** Freeze the evaluator shipment and implementation profile, then implement and qualify the agreed validation/computation surface in Rust, including exact numbers, row identity, partial relevance, computation state and host interfaces. Completion requires an actual runnable consumer and differential/property evidence, not another readback. Prepare concrete repository/session and dependency choices at entry under the [consumer handoff rules](IMPLEMENTER-GUIDE.md#lessons-from-the-first-cold-implementation); no downstream checkout is created by this planning change. Lean replays rules and computations one at a time and owns built-in findings per family, so the whole-call message inventory, carrying the built-in channel shape of [spec/02 §B.1](../spec/02-logic-and-formal-errors.md#b1-what-a-formal-error-is), is assembled and differentially checked by this consumer ([K21](consumer-probes/EXECUTE.md#run-k21-execute-01)).
- [ ] **U03 — SMT-backed analysis and synthesis.** Use the [existing proposal](SMT-SOLVER-SUPPORT-PROPOSAL.md) to settle a finite initial query profile, then implement its translation, solver interaction and checked results. Distinguish condition/rule reachability from model inhabitance and computation-alternative coverage. Replay decoded SAT witnesses through the accepted evaluator semantics; bound UNSAT claims by encoding completeness and solver/certificate trust. Resolve relevant mandatory-information and transformation needs here, instead of using them to defer consumer work indefinitely.

The request adopts this sequencing and the two consumer objectives. It does not silently adopt every optional feature in the SMT proposal or choose new dependencies, repository creation, releases or public compatibility claims. Those concrete choices belong to the implementation boundary, with existing approval rules applied only where needed.

<a id="u01-plan"></a>
### U01 plan

- `state`: [closed after M4](consumer-probes/EXECUTE.md#run-u01-close) on 2026-10-26 by the owner, without M5; the entries below record how it ran.
- `decisions`: the owner settled the entry decisions on 2026-10-25, each the recommended option. The first profile is the replay-compared surface: DM-JSON model and document reading, full and partial validation with their message projection, and computations with their operand-error channel; custom conditions and pattern compilation fail closed. The work happens in a new sibling repository `../a12-rust-interpreter` under MIT, worked by a fresh session that sees only the packet. `num-bigint`, `num-rational` and `serde_json` are approved runtime dependencies; regex and time-zone crates wait for a later decision. The retained Kernel captures travel inside the packet as the differential oracle, and the toolchain is the existing Homebrew `rustup`.
- `report-transport`: superseded by the owner on 2026-10-25, the experiment running without owner decisions. This session watches `../a12-rust-interpreter` read-only through `git` and reviews each milestone when a new section lands in its `reports/QUALIFICATION.md`, without the worker waiting. It messages the worker session only with the kit's resumption prompt, a new-packet notice or the M5 instruction, never with answers or findings, which return only as packet versions.
- `gates`: the owner settled the entry decisions above and starts the worker session; after that the run needs no owner decision, as the [implementer guide](IMPLEMENTER-GUIDE.md#lessons-from-the-first-cold-implementation) now requires for every U experiment. Triage measurements and gates in this repository run without a per-run ask. The owner remains needed only for a push, and is told of U01's completion.
- `packet`: `spec/*.md` at a pinned commit, the [host-input contract](IMPLEMENTER-GUIDE.md#host-input-contract), the retained captures with a manifest digest, and the committed [evaluator kit](IMPLEMENTER-KIT-EVALUATOR.md) holding the comparison contract, the profile and its exclusions, and the session prompts with its allowed reads and never-wait rules. The packet is assembled outside this repository, carries a version and digest, and is never edited in place; a correction is a new version.
- `isolation`: the Rust session reads only the packet and its own repository, plus a new packet version's named path when replacing `packet/`. It never asks this session or the owner a question and never waits: an undetermined case goes into its questions-and-guesses log with a chosen reading, and an answer returns only as a new packet version.
- `scale`: a multi-week effort across many sessions, not one run. The owner expects about 40,000 lines of Rust and as much again in tests; for comparison, this repository's semantics and elaboration hold about 108,000 nonblank Lean lines and its DM reader about 48,000, half of them locks, measured 2026-10-25.
- `rust-handoff`: the Rust repository owns its own plan and handoff record, seeded by the packet's prompt, and each Rust session resumes from that repository's state alone. This plan tracks only the gates, packet versions and accepted milestones.
- `milestones`: M1 reads DM-JSON models and documents and fails closed outside the profile. M2 adds full validation and its whole-call message inventory, M3 computations and their operand-error channel, and M4 partial validation; each of M2–M4 lands as family slices in the spec's chapter order, each slice reporting its capture match rate per family. M5 adds seeded mutations, one at a time, and the qualification record. Review happens at owner-named commits that close a slice batch, not at every commit.
- `packets`: expect several packet versions; each correction is a new version, and every Rust report names the version it was built against. Each version is cut from one committed revision by [`assemble-evaluator-packet.py`](../scripts/assemble-evaluator-packet.py) into the owner's Downloads folder. v1, cut 2026-10-25 from `955ec3de`, holds 1980 files whose `MANIFEST.sha256` has SHA-256 `ca1cc64ffdfcdd752dd9bfe4f0065bd3ffd47a03b56e6be13806fda422db4708`. v2, cut the same day from `2e5faf0c` before any implementation work, changes only the kit to the never-wait rules; its `MANIFEST.sha256` has SHA-256 `a5b68fe1e229a7f66e69ac89da0918ac22e50cd5455b285748733fec5435b3c7`. v3, cut after the M1 review from `f09769fb`, settles the worker's Q-001 and Q-003; its `MANIFEST.sha256` has SHA-256 `213457432f7b200c281f4b52ba987fd1bab2d00d55b59b0b2df7ebb1a7b26397`.
- `reports`: committed in the Rust repository at each milestone: the questions-and-guesses log, per-row differential results against the captures (match, diverge with both values, or unsupported), and the qualification record pinning the packet digest, Rust commit, commands and raw results; M5 adds the mutation results.
- `triage`: each divergence follows the [disagreement protocol](IMPLEMENTER-GUIDE.md#disagreement-and-missing-semantics-protocol) from its first divergent boundary. A case the spec decides is a Rust defect fixed there, and repeated misreadings of one clause are rewritten here. A case the spec leaves open is a spec defect: the clause, a Lean lock where behavior is involved, a ledger entry when a12-dmkits must reconcile, and a new packet. Rust following the spec against a capture Lean matches is spec prose drifted from Lean, corrected in `spec/`. A case no retained capture separates gets a local Kernel probe before any account is chosen. The [evaluator kit](IMPLEMENTER-KIT-EVALUATOR.md#comparison-contract) compares whole-call message sets with built-in findings, partial-call references and the full outcome pointer set, none of which the Lean replay compares, so a divergence there is first checked against Lean's own output before any account is chosen.
- `acceptance`: HIGH reviews the Rust source and tests at the reported commit before accepting a milestone, since a report alone hides fixture branching. Each milestone leaves a run record under the [Execute category](consumer-probes/EXECUTE.md); process lessons go to the implementer guide's lessons and durable Lean lessons to `LEAN-FINDINGS.md`.
- `completion`: U01 closes when every in-profile capture row matches or carries an explained profile exclusion, the questions log holds no open semantic question, the mutation gate passes, and the qualification record names the final packet.
- `deferred`: a Lean-reference differential over generated inputs, which needs a DM-JSON reference operation and its own approval; host features beyond fail-closed; and U03, which waits until U01's first profile qualifies.

<a id="u02-plan"></a>
### U02 plan

- `state`: running in `../a12-rust-interpreter-u02`, whose first commit is `8cb07d6`: M1 and [M2](consumer-probes/EXECUTE.md#run-u02-m2) accepted on packet v5, [M3](consumer-probes/EXECUTE.md#run-u02-m3) and [M4](consumer-probes/EXECUTE.md#run-u02-m4) accepted on packet v6, adopted at `8565a10`; [M5](consumer-probes/EXECUTE.md#run-u02-m5) accepted on packet v7 with MUT-3 rerun on v8; [closed](consumer-probes/EXECUTE.md#run-u02-close) on 2026-10-30 after its debrief at Rust `793b3c5`; v4 is superseded unrun.
- `decisions`: U01's settled decisions carry over unchanged: the profile, MIT licensing, the three approved crates, the isolation boundary, the report transport and the never-wait rules. The worker starts in an empty sibling repository, recommended as `../a12-rust-interpreter-u02`, so that U01's code stays the comparator and nothing is carried over.
- `kit-changes`: the kit classifies each channel on its own and reports per-channel totals, because U01's whole-row classes hid `messages` divergences behind a refused `partialMessages` channel. The packet ships spec/14 and `docs/sources/`, so the chapters' provenance links resolve inside it.
- `milestones`: M1–M4 as the kit states, from scratch. The M5 mutation set is designed against the rewritten spec after M4 and arrives as a separate instruction.
- `comparison`: U01's close record is the baseline: questions decided from captures or by choice, rules read in another chapter than their owner, and passages that disagreed. U02 should log fewer of each; a repeated question names a clause the rewrite left unclear.
- `packets`: v4 is cut by [`assemble-evaluator-packet.py`](../scripts/assemble-evaluator-packet.py) into the owner's Downloads folder as `a12-u02-packet-v4`, from `496d4a05e61dd5c3335fd33224beef795777d665` on 2026-10-27. It holds 2012 files, all 858 spec links into `docs/sources/` resolve inside it, and its `MANIFEST.sha256` has SHA-256 `deb0eb1dabc5700549b3801d5b7b78c8163bea1afb5ac3125d30062b97933187`. v5, cut the same way as `a12-u02-packet-v5` from `db49b29332775a5d716e72381b428a5affea1ce9` on 2026-10-29, carries the spec, sources and captures of the October 27 to 29 handbacks and is the packet U02 starts on. It holds 2045 files, its 922 spec links into `docs/sources/` resolve inside it, and its `MANIFEST.sha256` has SHA-256 `665e0ca21043728c759f7fa1a92000f72f3a6be3f09066c5af39397347e01a70`. v6, cut the same way as `a12-u02-packet-v6` from `0d13acf1e49ecc1dd2691058ea599dd3386505d0` on 2026-10-29, answers U02's Q-001, Q-002, Q-004 and Q-005 in spec/01, spec/08, spec/09 and the kit, carries the Q-003 coordinate correction and names those clauses on its changes line. It holds 2045 files, every spec and kit link into the packet resolves, and its `MANIFEST.sha256` has SHA-256 `6253f911c0bf7828885de6fea3df096bd1e536d01596a4b399b64870e3ffc7f6`. v7, held by owner decision of 2026-10-30 until another change required a packet, carries the kit's [M5 mutation set](IMPLEMENTER-KIT-EVALUATOR.md#m5-mutation-set) with the spec changes since v6. It is cut the same way as `a12-u02-packet-v7` from `f63ffb01b2eb776fd6d735a92d507e302383be37` on 2026-10-30, holds 2051 files including the yearless direct copy capture, and its `MANIFEST.sha256` has SHA-256 `80e0c9a2400c13e6c9b0955cee21678f08c8821925ab4101bd79cab4463466d2`. Its spec and kit links resolve except the seven v6 also left open: six semantics-map provenance links to documents outside the packet and spec/01's link to a capture without an artifact; the M5 instruction follows its notice once U02 has adopted it, and the frozen predictions sit in the [M5 record](consumer-probes/EXECUTE.md#run-u02-m5). U02's Q-007 is settled in favour of the reading (a) its questions log records at `8eb5c7c`, by the [yearless direct copy](sources/temporal-constant-and-base-year-probes.md#src-yearless-direct-copy-base-year) measurement, so it adds no packet either. U02's Q-008 is settled in favour of its implemented reading (a) by the [fragment pair comparison](sources/temporal-constant-and-base-year-probes.md#src-fragment-pair-comparison) measurement, and its Q-009 reading (a) is correct, the kit's MUT-3 being reworded; its Q-010 is answered by neither of its readings, a shifted yearless value keeping the year it reaches from the anchor 2000, and its Q-011 in favour of its reading (a), which spec/05 §3.2 already stated, by the [Time component provenance](sources/temporal-runtime-fold-probes.md#src-time-component-missing-provenance) reading, and its Q-012 in favour of its reading (a), one shared leap year, by the [yearless shift anchor](sources/temporal-constant-and-base-year-probes.md#src-yearless-shift-anchor) measurement; v8 carries these answers, their spec/05 clauses and the reworded kit, cut because the Q-010 answer refutes the reading U02 implemented: cut the same way as `a12-u02-packet-v8` from `ac5cb8ae` on 2026-10-30, it holds 2072 files including the fragment pair comparison and yearless shift anchor captures, its `MANIFEST.sha256` has SHA-256 `4b20908fc212d6631cd3f3076b74934ee1feb22c00dce53601a07b401aa45ee8`, and its unresolved spec and kit links are exactly v7's.

<a id="spec-rewrite-plan"></a>
### Spec rewrite plan

- `goal`: rewrite `spec/01`–`12` and `SEMANTICS-MAP.md` around mechanisms so that a cold implementer can work from the packet alone. U02, a fresh cold run in a new directory on the rewritten spec, measures the result against the [U01 baseline](consumer-probes/EXECUTE.md#run-u01-close).
- `inputs`: the verified [spec audit of 2026-10-26](../reviews/2026-10-26-spec-audit.md) (212 chapter findings, 6 cross-chapter contradictions), the U01 questions log and `reports/SPEC-FEEDBACK.md` at `../a12-rust-interpreter` revision `49e24fe`.
- `preserve`: every normative rule a chapter states before its rewrite is stated after it or listed as deliberately changed. A fresh verifier compares the old and new chapter rule by rule before each commit.
- `behavior`: content changes only where a verified contradiction or gap requires one. Lean decides the surviving side where it implements it; otherwise a measurement comes first, and an unmeasured item stays as written and marked. Each locally originated behavioral change carries its `SPEC-` ledger entry, batched for a12-dmkits.
- `self-contained`: no normative content stays reachable only through `docs/` or a12-dmkits. Checkpoint and inbound links leave normative sentences for one provenance line per section, and packet v4 ships `docs/sources/` beside the captures so those links resolve. A direct a12-dmkits link becomes its local inbound record where one exists.
- `operator-reference`: one normative per-operator table, `spec/14-operator-reference.md`, owns operator membership facts now scattered across chapters: empty, invalid and UNKNOWN reads in validation and computation, polarity and filter escalation, content-gate family membership, classification enablement, traversal and partial extent predicate. Chapters state the mechanisms and point to the table rather than enumerating members, and [the implementation map](IMPLEMENTATION-MAP.md) names each column's Lean owner.
- `stable`: `§n` numbers and existing anchors stay valid. Unverified audit items stay unchanged until measured.
- `order`: spec/02 as pilot, then an owner review of the pilot before continuing, as the owner confirmed on 2026-10-26. Then spec/10 with the operator table, spec/09, spec/07, spec/12, spec/11, spec/05, then spec/03, spec/04, spec/06, spec/08 and spec/01, and `SEMANTICS-MAP.md` last as a declared non-normative summary. A cross-chapter pass over the new chapters' rule digests closes the rewrite.
- `cycle`: per chapter, HIGH settles the finding list from the three inputs. A fresh opus agent drafts, a second fresh opus agent checks preservation and finding closure, and HIGH reviews the diff, decides each behavioral change, and commits after the guards pass.
- `closure`: the cross-chapter pass opens with a corpus closure check against the pre-rewrite spec at `1a9199a7`: one fresh verifier per original chapter, run in sequence, finds each old rule anywhere in the final `spec/` or in a declared change in the chapter notes or the sync ledger, and writes its statement table to `reviews/spec-rewrite/closure/`. A rule found in neither place is a loss, restored before packet v4.
- `closure-result`: the check ran on 2026-10-27 with tables under [reviews/spec-rewrite/closure/](../reviews/spec-rewrite/closure/). It found one lost rule, one altered and seventeen narrowed, all restored or declared before the cross-chapter pass. The per-chapter check had missed dropped trap markers, dropped scope labels and undeclared negative-existential softenings, so the cross-chapter pass checks its own diff for those three as well as for lost rules.
- `u02`: after the rewrite, packet v5 carries the rewritten spec and a kit that classifies each channel separately, so a refused channel no longer hides another's result. U02 runs M1–M5 from scratch, and the M5 mutation set is designed against the rewritten spec.
- `stop`: two consecutive chapters whose commit still loses a rule stop the sequence until the method is revised. The preservation check stays mandatory, and a draft loss it catches and restores before commit does not count, as the owner settled on 2026-10-27 after spec/04 and spec/06 each lost one draft rule.

<a id="remaining-gap-routing"></a>
## Residual ownership and former exclusions

The old D identifiers explain the C01–C22 boundary only. They no longer exclude a K task. Each SG family below has an executable-work destination; a residual not discharged there blocks K22 unless K19 establishes its explicit host/service boundary.

| Gap family | Required K owners | Consumer-only continuation |
|---|---|---|
| SG4, SG18, SG16 | K02, K08–K12, K20 | U01 |
| SG5, SG27 | K04, K06, K16 | U01 |
| SG6, SG21, SG23 | K03, K11–K12, K19 | U01/U03 |
| SG7, SG8 | K01, K09, K13–K14, K17 | U01 |
| SG25, SG10 | K07, K14–K15 | U01 |
| SG11 | K18 | U01/U03 |
| SG9, SG29, SG19 | K04–K07, K17, K19 | U01 |
| SG13, SG17, SG20 | K03, K06, K19 | U03 transformation/analysis only |
| SG15 | K10–K12 | U01 |
| SG14 | K19 service boundary | U03 mandatory-information analysis |
| SG28 | K17, K19 | U01/U03 |
| SG12 | K18, K20 | U01/U03 qualification |

| Former exclusion | Current disposition |
|---|---|
| D01–D02 depth, arity and capacity | K03, K05–K06: settle mechanisms and separating depths/capacities; no arbitrary permutation campaign |
| D03 calendar profiles | K11–K12 implementation; K19 explicit host floor/zone boundary |
| D04 cache history | K05, K07 and K19 context contract; retain exact Kernel semantics despite peer IF376 |
| D05 lexical key fitting | K05 |
| D06 diagnostic combinations | K04, K15, K17; exact named gates, not every pairwise permutation or parser resource ceiling |
| D07–D08 multiplicity and index classes | K14–K15 |
| D09 provider/locale breadth | K14–K15 host inputs; catalog prose remains external under K19 |
| D10 regex/Unicode | K13 semantics and K19 compiler/host contract |
| D11 callbacks/codecs | K01, K13, K18 local work; [legacy profile disposition](sources/custom-field-probes.md#src-custom-legacy-profile) supplies the expanded-A12 boundary |
| D12 Number display ingress | K16 |
| D13 mandatory-information service | K19 boundary, then U03 when its query profile needs the service |
| D14 partial plans | K08 enforcement and K19 contract; no silent stale-field execution |
| D15 application/explanation | K10; K19 distinguishes observability limits from evaluator state |
| D16 declarations/importing | K11, K17; a general importer is a separate consumer |
| D17 transformation theorem | Evaluator effects in K03; transformation-specific theorem/probe in U03 when adopted |
| D18 legacy/public API breadth | K04–K07 and K14–K15 semantic distinctions; U01 owns needed transport, legacy API parity is not implied |
| D19 declaration catalog | K17 |
| D20 extra carriers/chains | K08–K12 and K20: material policy distinctions, not arbitrary extra lengths |
| D21 temporal target/literal search | K11–K12: named target policies; unwitnessed syntax stays reachability-unknown |
| D22 coordinates/cross-root/RNU | K04–K07 |
| D23 capacity/category/filter calibration | K03, K06, K13 and K20 |
| D24 structural faults/unobservable choices | K02, K08 and K19: preserve total semantics, require a discriminator before another measurement |

<a id="build-audit-deferrals"></a>
## Deferred build work

These come from the owner-approved build audit of 2026-10-22. Each waits on its named trigger and does not interrupt the K sequence.

- [ ] **B01 — single CI evidence replay.** With the next change that touches [the CI workflow](../.github/workflows/lean_action_ci.yml), delete its explicit `lake test` step: lean-action's auto-configuration already runs `lake test`.
- [ ] **B02 — vocabulary distinctness cost.** When `KernelStaticDiagnostic` passes about 350 classes or [its laws module](../A12Kernel/Proofs/StaticDiagnostic.lean) peaks above about 2.5 GiB, move the distinctness check to the conformance lane as a `native_decide` lock. Nothing consumes it as a theorem. That module's comment records why the cheaper kernel routes measured slower.
- [ ] **B03 — line budget and comments.** If WHY-comments are cut to keep a module under the 800-line review target, count only code lines for that target and keep the 1,200-line ceiling on all nonblank lines.

## Historical navigation

<a id="reconciliation-checklist"></a>
<a id="ordered-checklist"></a>
<a id="deferred-work"></a>
The completed R/C records and detailed C exclusions are retained in the [frozen prior plan](https://github.com/mbackschat/a12-kernel-lean/blob/126404f220f7c78fb7eff68c1356340120105ab7/docs/PLAN.md). These compatibility anchors also route readers to the [live K checklist](#remaining-conformance-checklist) and [current SG/D ownership](#remaining-gap-routing).
