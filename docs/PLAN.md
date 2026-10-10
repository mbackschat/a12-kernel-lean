# Ordered kernel-conformance work

Owner-directed reset, 2026-10-10. The requested finish line is good-enough Lean coverage of Kernel 30.8.1: complete the substantial ordinary validation/computation behavior and leave the esoteric long tail out. The owner's “99–99.5%” describes that practical scope, not a measured percentage of all possible programs. Universal conformance remains a long-term aspiration, not a reason to continue this work indefinitely.

The numbered tasks below serve that finish line. Twenty-two is the current list, not a quota: close stale items from existing evidence, add any genuinely missing ordinary mechanism explicitly, and stop when the acceptance conditions at C22 hold. Do not add a product launch, downstream adoption, new interpreter, SMT integration or qualification programme as a prerequisite. Consumer probes remain occasional checks that the semantics is usable.

The autonomous goal is paused. This planning change does not resume semantic implementation. On resumption start at C01, not at the former next group-topology capture.

<a id="single-track-breadth-queue"></a>
## Priority and closure rules

Work in numbered order, one shared mechanism batch at a time. High-risk behavior comes first, including rare triggers: wrong computed values, stale data surviving clears, swallowed failures, cross-row selection leaks and silent admission/metadata loss. Then close ordinary accepted-language reach and consequential evidence gaps. This is an engineering judgment; no production-model frequency data is available.

- Rarity and risk are separate. A high-risk defect cannot be excluded as long tail because its trigger is unusual. A host/profile limitation is safely excluded only when unsupported inputs are explicitly rejected or require explicit context; silently choosing a wrong answer is a high-priority gap.
- An unchecked item is a closure obligation, not automatically a missing implementation. Code-confirmed boundaries below were inspected for this plan. Recorded gaps need a focused current-code/evidence check at entry; calibration tasks need the stated external discriminator.
- Inspect the named owners and existing separators once. If they already discharge the item, check it off with an evidence link and correct its stale gap claim. Do not implement, capture or rebuild it again.
- Freeze each task's listed acceptance matrix. Name the common selection, observation, scheduling, admission or emission mechanism, and test a second composition that could falsify it. Implement all ready family members through that mechanism, not one branch per example.
- A new case inside the matrix corrects that mechanism. A new independent mechanism gets a separately triaged task, never a silently expanded batch. Two rounds producing new blockers/prerequisites without an acceptance-case closure require repartitioning.
- Use existing focused red/green, applicable integrated gates, same-context assessment and triggered cold review. Reuse gates after non-invalidating edits. Commits, builds, extra rows and agent activity are not task closure.
- Use retained observations first. A new capture needs an unresolved alternative and a finite matrix. Passing it ends the batch; no automatic “one more depth/kind/permutation.”
- Completion requires the promised reader-to-evaluator/output result, evidence and honest exclusions. A known missing in-scope case cannot be checked off by relabelling it a limitation.
- Good-enough coverage requires ordinary accepted inputs to be executable and ordinary outcomes to agree with their oracle. Unsupported ordinary inputs remain gaps; a high replay pass rate over only supported cases does not establish completion. Use existing coverage, gaps and evidence owners rather than creating a new percentage-measurement programme.
- Record any reordered dependency or promoted consumer blocker here. Adjacency, curiosity and available tooling are not priority reasons. Report C12 before proceeding to the subsequent queue; never enter deferred work automatically.
- PLAN has no word limit for this owner-requested checklist. Detailed semantics remain in linked owners. This adds no tracking framework, harness or recurring verification loop.

<a id="ordered-checklist"></a>
## Checkpoint 1 — ordinary Execute/Explain reliability

C01–C12 are the required sequence. This checkpoint is a bounded consumer-reliability claim, not full conformance or public-protocol coverage.

### C01 — risk boundary check and independent consumer baseline

- [ ] First check the high-impact exclusion boundaries: partial-plan stale calculated fields; missing pattern compiler/custom validator; missing cache-order context; out-of-profile calendar inputs; omitted/cleared result application. Use existing code and failure controls to establish explicit refusal/context requirements or identify a dangerous admitted path. Any silent wrong result becomes a named priority fix before lower-risk work; do not wait for the consumer run.
- [ ] Freeze and run an Execute/Explain task with eight concrete scenarios: fresh computed producer replacing stale storage; false guard clearing a seeded target; reached versus bypassed poison; first matching alternative; identical keys in different parents; missing versus duplicate selected keys; partial coverage of a fixed group below a star; generated error after applying a result.
- Supply only canonical clauses and concrete inputs to an isolated consumer. Require values/clears, firing, row identity and structured errors where defined; missing information must be identified, not guessed. HIGH compares answers with checked APIs and retained observations.
- Done: record all eight dispositions and any representation/transport blocker in [Execute probes](consumer-probes/EXECUTE.md). Reuse the narrow [cache-context](consumer-probes/EXECUTE.md#run-message-cache-context-readback-01) and [traversal](consumer-probes/EXECUTE.md#run-filter-traversal-readback-01) boundaries. This is broader semantic transport, not qualification of an independent interpreter.

### C02 — fresh dependencies through selected computation group guards

- [ ] Close the former keyed-lower-star computation queue as a guard/scheduling batch. Indexed/keyed guards already exist in [ComputationNumericGuard](../A12Kernel/Elaboration/ComputationNumericGuard.lean); check their actual reader and scheduler paths first.
- Matrix: one String-indexed parent and one lower star; fresh computed key/payload; absent/duplicate key; false guard; malformed selected content. Put an independent decisive operand before/after selection and seed the target.
- Done: target outcomes and downstream reads preserve fresh producer state, ordered bypass, reached poison and clearing. Reuse the selected extent; validation UNKNOWN is not computation poison. [SG4](gaps/keystone.md#gap-sg4), [SG13](gaps/paths-and-groups.md#gap-sg13), [SG29](gaps/paths-and-groups.md#gap-sg29).

### C03 — preserve results through application and later reads

- [ ] Reconcile remaining Number, Boolean/Confirm and Enumeration result/application boundaries against current carriers.
- Matrix: fresh/seeded target; produced/guard-cleared/target-rejected result; fixed/two-row target; separate same-model destination; subsequent explicit validation and dependent read. Existing String application observations are controls, not evidence for another kind.
- Done: returned outcome, applied contents and later observation agree with retained Kernel results on each selected kind. Neither rejected attempted payload nor stale stored value survives. [SG16](gaps/keystone.md#gap-sg16), [SG18](gaps/keystone.md#gap-sg18).

### C04 — retain reached validator failures through ordinary conditions

- [ ] Resolve the remaining complete-caller boundary for named-validator failures. [Evaluation](../A12Kernel/Elaboration/ValidationCondition/Evaluation.lean) already transports failures from direct/indexed validity leaves.
- Matrix: failing leaf before/after a false And sibling and true Or sibling; direct/indexed twins; covered/uncovered partial input; missing registration versus normal validator rejection.
- Done: full/partial checked rules distinguish reached whole-call failure, bypassed callback and normal invalid verdict. Existing complete evidence closes this task without code changes. [SG7](gaps/strings-and-messages.md#gap-sg7), [SG11](gaps/strings-and-messages.md#gap-sg11).

### C05 — preserve categories through the shared entity reader

- [ ] Correct the code-confirmed terminal-star group category erasure in [LowerEntity](../A12Kernel/Reference/Dm/LowerEntity.lean). Reconcile its generic starred-field category refusal with the dedicated token value-count route that already retains projection.
- Matrix: plain group/category-on-group; direct/starred Enumeration field with the same category; filtered/unfiltered projected star. Cover filled-field count, token value count and token first-filled where each admits the form.
- Done: illegal group categories cannot become legal plain groups; legal category reads retain projected rather than stored tokens through shared lowering. Admitted and refused twins reach every affected consumer. [SG9](gaps/paths-and-groups.md#gap-sg9), [SG8](gaps/strings-and-messages.md#gap-sg8).

### C06 — first-match alternatives for non-Number targets

- [ ] Close remaining table gaps for String, Enumeration, Boolean/Confirm and temporal targets at fixed/two-row targets. [LowerRows](../A12Kernel/Reference/Dm/LowerRows.lean) already covers many operations; do not rebuild that baseline.
- Matrix: false first guard then match; two matches; no match on a seeded target; invalid reached operation; direct/FirstFilledValue operation. Use the common row-table selector; add an operation adapter only where its source contract is settled.
- Done: accepted forms execute once per instance with exact first-match and clear/poison outcomes; otherwise-admissible unsupported forms are explicitly accounted for. [SG4](gaps/keystone.md#gap-sg4), [row-table owner](../A12Kernel/Elaboration/RowComputationTable.lean).

### C07 — partial group operands share admitted observations

- [ ] Close recorded partial-validation gaps for Number group operands, Boolean group value counts and token group operands using existing product/stream owners.
- Matrix: fixed two-field group, then below one repeatable parent; complete/incomplete coverage; empty/filled/malformed content; mixed Number signedness; category/stored-token projection. Legacy raw-Document APIs are excluded.
- Done: maintained checked rules admit supported forms and return the correct full/partial result without per-operator expansion code. Counts, presence and aggregates keep distinct result domains. [SG5 group runtime](gaps/numeric-and-temporal.md#gap-sg5-number-token-group-runtime), [SG13](gaps/paths-and-groups.md#gap-sg13).

### C08 — omission and reference coordinates in visible errors

- [ ] Implement/reconcile one omission selector for presence-only operands, upward count comparisons, filter references and positive root-group expansion. Keep referenced and fill-to-fix sets distinct.
- Matrix: presence; count operands on both sides; candidate/captured filter read; selected payload/key reference; mixed group count with starred/deeper descendant. Reproduce the suspected coordinate defect in [Reference](../A12Kernel/Elaboration/ValidationCondition/Reference.lean) before changing its mixed-count field sieve.
- Done: exact sets and coordinates agree with the [message-construction oracle](sources/message-and-pointer-probes.md#src-message-construction-route) and retained [Having caller observations](sources/having-filter-probes.md#src-having-caller-runtime). Code/pointer/type agreement alone does not close this. [SG10](gaps/strings-and-messages.md#gap-sg10), [H10-R1/R2](gaps/paths-and-groups.md#gap-sg17-closure-matrix).

### C09 — parallel banded Number rounding

- [ ] Close the recorded parallel-coordinate output-policy refusal using existing target rounding. Fixed and target-bound repeated rounding already exist.
- Matrix: Exact/RoundUp/RoundDown; positive/negative band boundaries; unique-key match/no-match; generated comparison against the unrounded operation; fixed-target twins.
- Done: parallel results and generated validation preserve separate rounding stages with exact outputs and mode refusals. [Banded locks](../A12Kernel/Reference/Dm/BandedComputationLocks.lean), [SG5](gaps/numeric-and-temporal.md#gap-sg5).

### C10 — partial-Date FirstFilledValue selection

- [ ] Extend the existing temporal selector to the inbound partial-Date policy wherever the current carrier still refuses it.
- Matrix: year-only/year-month/complete values; earlier empty source; zero-date/malformed source before valid fallback; direct list/one star; validation/computation.
- Done: checked reader, earliest-day selection and target results retain phase-specific unavailability and correct fallback reach. No additional zone or pre-calendar-floor scope. [SG6](gaps/numeric-and-temporal.md#gap-sg6), [temporal first-filled shape](../A12Kernel/Elaboration/TemporalFirstFilledShape.lean).

### C11 — Number length checks retain leading-zero text

- [ ] Resolve the recorded formal-check gap for leadingZerosAllowed declarations without confusing stored spelling with numeric value.
- Matrix: 0012/12 at identical value, below/above declared length, flag on/off, stored input/computed replacement; reuse existing selected-number text controls.
- Done: lexical length and numeric equality remain independently observable on admitted inputs. A new refusal of a Kernel-valid ordinary input does not close this task. [SG27](gaps/numeric-and-temporal.md#gap-sg27).

### C12 — report the first consumer-reliability checkpoint

- [ ] Run a fresh Execute/Explain consumer on the eight C01 scenarios plus the C05 category, C10 partial-Date and C11 lexical distinctions. Freeze the task and compare actual outputs.
- Done: C01–C11 have evidence dispositions, no known in-scope wrong answer remains, consumer readback is green and applicable reviews/gates are complete. State the actual replay boundary; full replay remains governed by its existing cadence.
- Report the supported task, closed items and limitations before moving on. Consumer failure returns to its semantic owner, never a consumer-specific workaround. This is not full conformance or Rust/SMT qualification.

## Subsequent order — visible language and evidence closure

C13–C22 follow the reported first checkpoint and finish the ordinary-behavior scope. C12 is an intermediate checkpoint; C22 is the stopping boundary. These tasks cannot become hidden prerequisites delaying the C12 report.

### C13 — index message parameters reach checked authoring

- [ ] Connect existing index-name/suffix checkers to [message authoring](../A12Kernel/Elaboration/ValidationMessageAuthoring.lean), whose indexField branch still throws invalidParameter. Share condition-reference metadata with keyed group parameters.
- Done: String/Enumeration indices, value/category suffixes, English/German syntax, plain/keyed/starred references and two parent rows have exact admission and rendering. Rare composed-index diagnostics stay deferred. [SG25](gaps/strings-and-messages.md#gap-sg25), [SG26](gaps/strings-and-messages.md#gap-sg26).

### C14 — mixed parallel numeric tables use complete operations

- [ ] Reconcile and close Sum/DayFromDate operands, a numeric comparison guard, a fallback without a joined operand and a computed producer feeding one side.
- Done: one two-group unique-key matrix executes authored alternatives and fresh dependencies through the [existing parallel step](../A12Kernel/Elaboration/ParallelNumericStep.lean); no new join algorithm or third group. [SG4](gaps/keystone.md#gap-sg4).

### C15 — row-set temporal expressions compose with comparisons

- [ ] Close MinValue/MaxValue over direct/one-star lists inside comparison and DifferenceInDays, for complete Date and yearless/common-BaseYear profiles.
- Done: full/partial validation and computation retain calendar metadata, empty/formal outcomes and ordinary Berlin date-boundary behavior through the shared tree. Pre-floor, arbitrary-zone and deeper nesting are excluded. [SG6](gaps/numeric-and-temporal.md#gap-sg6), [SG23](gaps/numeric-and-temporal.md#gap-sg23).

### C16 — Enumeration/String domain crossings retain value identity

- [ ] Settle unlabelled Enumeration-to-String copy and ordinary String target Enumeration-domain/pattern interaction.
- Done: differing stored/display token, outside-domain token, pattern-valid/domain-invalid value and its converse yield exact copy/refusal/target errors through existing token readers. [SG7](gaps/strings-and-messages.md#gap-sg7), [SG8](gaps/strings-and-messages.md#gap-sg8), [SG15](gaps/targets-and-derivation.md#gap-sg15).

### C17 — ordinary declaration and admission outcomes

- [ ] Distinguish unreadable model, build failure, codeless notification and keyed diagnostic; settle rule-name/blank-error-code admission and target-read versus empty-precondition ordering.
- Done: single-defect and competing-defect twins at those named boundaries yield the right tier and structured result. No exhaustive diagnostic-pair campaign or copied catalog prose. [SG28](gaps/targets-and-derivation.md#gap-sg28), [SG10](gaps/strings-and-messages.md#gap-sg10), [SG7](gaps/strings-and-messages.md#gap-sg7).

### C18 — five pending tolerance calibration cells in one batch

- [ ] Calibrate DiffersWithToleranceRange2 validation/computation, Range5 computation, Range10 validation/computation.
- Done: retained below/at/above-boundary and sign controls, output rounding where applicable and checked-reader agreement for all five cells. Reuse C09 observations, not five separate gate cycles. [Construct evidence](CONFORMANCE-CONSTRUCTS.tsv), [SG12](gaps/conformance-evidence.md#gap-sg12).

### C19 — three pending temporal calibration cells in one batch

- [ ] Calibrate DifferenceInMinutes/DifferenceInSeconds validation and QuarterFromDate computation.
- Done: signed completed-unit boundaries, quarter-end/start and empty/formal controls settle all three cells through shared temporal owners. [Construct evidence](CONFORMANCE-CONSTRUCTS.tsv), [SG6](gaps/numeric-and-temporal.md#gap-sg6).

### C20 — membership and constructed-Date validity evidence

- [ ] Calibrate FieldValueNotIncludedInValueList validation and Valid/Invalid computation.
- Done: membership hit/miss/empty/invalid and constructed-Date guards with valid/leap-invalid/empty/formally invalid components settle the three cells, including a seeded target cleared by a false guard. ValidType/InvalidType callback tests do not discharge Valid/Invalid. [Construct evidence](CONFORMANCE-CONSTRUCTS.tsv), [SG6](gaps/numeric-and-temporal.md#gap-sg6), [SG8](gaps/strings-and-messages.md#gap-sg8).

### C21 — one independent, already-authored computation sample

- [ ] Compare peer ComputationReadTest cases with the [retained corpus](sources/evaluation-and-application-routes.md#src-peer-corpus-replay); select only non-overlapping admitted shapes and their actual runtime observations.
- Done: enumerate the selected cases and reproduce mismatches at the shared mechanism they contradict. Round-trip assertions are not runtime evidence. Independent new mechanisms are separately prioritized, not an unlimited corpus campaign. [SG12](gaps/conformance-evidence.md#gap-sg12).

### C22 — accept good-enough Lean kernel coverage and stop

- [ ] Reconcile C01–C21 with the current implementation and retained observations. All catalog construct/arm main forms must remain broadly represented; the selected ordinary validation/computation compositions must execute, with no known unresolved ordinary-behavior mismatch or silently discarded input. Existing held-out C21 cases and C01/C12 consumer probes must support that claim.
- Done: each required task has an evidence disposition, applicable gates/reviews pass, and every remaining known obligation is specifically listed in the excluded section with its reason. A newly found substantial ordinary gap returns to its owning mechanism; another depth, unusual host profile or rare diagnostic does not expand the finish line.
- Report supported behavior, verified evidence limits and the excluded long tail, then stop at this boundary. Do not claim a statistically measured 99.5%, full universal conformance, downstream adoption or product qualification. An Analyze/optimizer probe is not required for this finish line.

<a id="deferred-work"></a>
## Excluded long tail — outside the good-enough finish line

These are candidate low-risk exclusions from the current completion scope, not a follow-on queue after C22. C01 checks the dangerous boundaries explicitly. A reproduced high-risk defect is promoted immediately even with a rare trigger; only low-risk breadth, safely refused profiles and bounded diagnostic refinements remain excluded. Ordinary behavior blocked by an exclusion also requires promotion. Retain the exact limitations for honest coverage claims; do not implement them just to approach universal completeness.

| ID | Specific work | Deferral / promotion trigger | Owner |
|---|---|---|---|
| D01 | Third/further ancestors, three reopened stars, nested independent axes, higher list arities | Promote a distinct behavior or real consumer input, not one more depth. | [SG13](gaps/paths-and-groups.md#gap-sg13), [SG29](gaps/paths-and-groups.md#gap-sg29) |
| D02 | Huge fully covered negative group scans and wider membership/uniqueness capacity combinations | Promote measured unacceptable cost or a different admitted result; no synthetic capacity sweep. | [SG13](gaps/paths-and-groups.md#gap-sg13), [H10-R6](gaps/paths-and-groups.md#gap-sg17-closure-matrix) |
| D03 | Below-Gregorian-floor DateTime, nonpositive eras, additional zones and exhaustive formats | Requires a faithful wider calendar profile and a concrete workload. | [SG6](gaps/numeric-and-temporal.md#gap-sg6), [SG21](gaps/numeric-and-temporal.md#gap-sg21) |
| D04 | Hash-tree cache ordering, capacity-sensitive winners, non-JSON ingress, on-the-fly bypass sets | Explicit actual context already handles underdetermination; promote a consumer needing its derivation. | [MC1/MC3](gaps/paths-and-groups.md#gap-sg29-cache-order) |
| D05 | UTF-16, whitespace, non-ASCII and custom-type key-fitting corners | Promote a reachable consumer shape or shared parser defect. | [SG29](gaps/paths-and-groups.md#gap-sg29) |
| D06 | Every diagnostic-pair precedence, parser depth ceiling, lexer positions and rare RNU starred spellings | Values and accepted ordinary inputs come first; promote a diagnostic consumer. | [SG9](gaps/paths-and-groups.md#gap-sg9), [SG19](gaps/paths-and-groups.md#gap-sg19), [SG25](gaps/strings-and-messages.md#gap-sg25) |
| D07 | Full Enumeration declaration finding multiplicity and all withholding combinations | Promote a consumer reproducing complete declaration reports. | [SG7](gaps/strings-and-messages.md#gap-sg7), [SG10](gaps/strings-and-messages.md#gap-sg10) |
| D08 | Index-message composed-index, display-mapping, inconsistent-type and non-iteration repeatability classes | Ordinary C13 first; promote a reachable mismatch rather than an unwitnessed code count. | [SG26](gaps/strings-and-messages.md#gap-sg26) |
| D09 | Locale/provider breadth, form-label rendering and extra over-limit message wording | Structured keys/parameters remain primary; promote a specified Explain requirement. Protected catalog prose is never copied. | [SG10](gaps/strings-and-messages.md#gap-sg10), [SG25](gaps/strings-and-messages.md#gap-sg25) |
| D10 | General Java regex, grapheme and surrogate profile breadth | Extra profiles may be excluded; treating a missing compiler as a valid semantic match/nonmatch or fabricated formal error is high risk, checked in C01. | [SG7](gaps/strings-and-messages.md#gap-sg7) |
| D11 | CustomCondition remaining callback calibration, reserved test-range callbacks, shipped-validator cascades and custom codec invocation | Ordinary callback support is distinct from the blocked reserved-key matrix. Promote a usable observation or consumer requirement; do not guess registration/conversion placement. | [SG7](gaps/strings-and-messages.md#gap-sg7), [SG11](gaps/strings-and-messages.md#gap-sg11) |
| D12 | Display-to-internal Number conversion and one-/three-decimal money wording | Different ingress/rendering service; promote its named consumer. Leading-zero formal length remains C11. | [SG27](gaps/numeric-and-temporal.md#gap-sg27) |
| D13 | Mandatory-information branching count graphs, arbitrary Boolean formulas, contributing cross-root sets and generated-rule closure | Promote a required-field-analysis task; longer graphs alone are not new mechanisms. | [SG14](gaps/targets-and-derivation.md#gap-sg14) |
| D14 | Partial-plan stripping of calculated fields outside the plan | Exclude only if the ordinary entry point enforces whole-model execution or explicitly rejects partial plans. An admitted stale producer read is high risk and must be promoted. | [SG4](gaps/keystone.md#gap-sg4) |
| D15 | Omitted result versus explicit clear, index-clear attribution and cross-model application certificates | Promote when an Explain/transport task needs the distinction; C01/C12 may expose that need. | [SG16](gaps/keystone.md#gap-sg16) |
| D16 | Table-backed Enumeration, empty fixed group declarations, variants and format-less loading | Outside current normalized model/host contracts; promote a named importer with required core-change authorization. | [SG8](gaps/strings-and-messages.md#gap-sg8), [SG9](gaps/paths-and-groups.md#gap-sg9), [SG21](gaps/numeric-and-temporal.md#gap-sg21), [SG28](gaps/targets-and-derivation.md#gap-sg28) |
| D17 | Generic theorem and dedicated Analyze probe for moving predicates across nested filters | Evaluation needs no such transformation; promote only an adopted optimizer task. | [H10-R5](gaps/paths-and-groups.md#gap-sg17-closure-matrix) |
| D18 | Legacy raw-Document parity, public diagnostic expansion and structural-message transport | Checkpoints use maintained checked routes. Promote a real public consumer/shipment. | [SG5](gaps/numeric-and-temporal.md#gap-sg5), [SG20](gaps/paths-and-groups.md#gap-sg20), [SG29](gaps/paths-and-groups.md#gap-sg29) |
| D19 | H-model diagnostic reachability, hint/sort-list laws and all field-type body declarations | Promote an importer need or ordinary misadmission; static catalog completeness follows execution. | [SG28](gaps/targets-and-derivation.md#gap-sg28) |
| D20 | Additional calibrated carrier permutations and fourth/fifth producer chains | Promote a distinct dependency observation, target policy or failing composition, not more rows. | [SG4](gaps/keystone.md#gap-sg4), [SG18](gaps/keystone.md#gap-sg18), [SG15](gaps/targets-and-derivation.md#gap-sg15) |
| D21 | Bare DateRange literal search, DateTime overlap/seed variations and extra yearless target policies | Promote a legal witness or concrete target-policy difference; no repeated search for an unwitnessed form. | [SG15](gaps/targets-and-derivation.md#gap-sg15) |
| D22 | Selected error-field reanchoring, wider cross-root rules and RNU sibling-fixed-group keys | Independent addressing families; promote concrete consumer models, not as C02/C08 extensions. | [SG9](gaps/paths-and-groups.md#gap-sg9), [SG29](gaps/paths-and-groups.md#gap-sg29) |
| D23 | More carrier-specific over-capacity, category-domain and filter-runtime calibrations beyond C05/C07/C15 | Preserve evidence limits; promote a consumer-relevant discriminator, not blanket recapture. | [SG8](gaps/strings-and-messages.md#gap-sg8), [SG13](gaps/paths-and-groups.md#gap-sg13), [SG23](gaps/numeric-and-temporal.md#gap-sg23) |
| D24 | Unauthorable structural-fault witnesses and filter false/UNKNOWN choices with no distinguishing output | Reopen only with an authorable witness or new observable channel. | [SG4](gaps/keystone.md#gap-sg4), [SG13](gaps/paths-and-groups.md#gap-sg13), [SG17](gaps/paths-and-groups.md#gap-sg17) |

## Reconciliation and coverage of the list

Every one of the 24 existing SG family records has a destination above. This is a triage of known obligations, not proof that no behavior remains undiscovered. New obligations must get a visible checklist destination; no invisible side tasks.

Do not convert these stale blanket claims into work:

- The reader already performs authored-number scale preflight; [LowerLocks](../A12Kernel/Reference/Dm/LowerLocks.lean) contains 1/1.00 and suppression controls. The narrower low-level flat surface does not prove the reader accepts invalid comparisons.
- [LowerRows](../A12Kernel/Reference/Dm/LowerRows.lean) already carries guarded String, Enumeration, Boolean/Confirm and temporal operations. C06 selects the actual table boundary.
- [ComputationNumericGuard](../A12Kernel/Elaboration/ComputationNumericGuard.lean) already accepts indexed fields/keyed groups. C02 concerns actual selected-star scheduling.
- [Validation evaluation](../A12Kernel/Elaboration/ValidationCondition/Evaluation.lean) already preserves direct/indexed validity failures. C04 must inspect full callers and retained controls before assuming a defect.

The twelve pending construct/arm calibration cells have destinations: five tolerance cells C18; three temporal C19; three membership/validity C20; CustomCondition validation D11. [Construct evidence](CONFORMANCE-CONSTRUCTS.tsv) owns the labels. A blocked reserved callback matrix does not mean every CustomCondition observation is blocked.

<a id="active-unit"></a>
## Resumption and accepted baseline

- Next after explicit resumption: C01. Check the five named high-risk exclusion boundaries, then freeze the eight scenarios and clause packet in the existing Execute probe owner and run the isolated consumer. Start no other batch in parallel.
- The [outer-bound keyed-star family](sources/group-count-topology.md#src-bound-keyed-star-predicates) is committed and freshly reviewed. Its former computation follow-up is bounded inside C02.
- Semantic implementation remains paused. Inspect Git status before resumption.
- The latest [cache-context probe](consumer-probes/EXECUTE.md#run-message-cache-context-readback-01) passed its narrow task; it does not discharge C01/C12. C01 is due on resumption, with the second bounded probe at C12. C22 uses those results and the subsequent evidence; it does not automatically trigger another consumer programme.
- One writer and sequential HIGH/MEDIUM work. HIGH settles the account and representative reader fixture; MEDIUM gets a complete bounded batch. Reuse warm context only for the same settled mechanism. HIGH acceptance does not replace triggered fresh cold review.
- Verify admitted fixture controls, carrier phase and entry API before expanding a matrix. Never edit compiler inputs while a build is live; report refreshes never justify replay.
- Carry-forward fixture constraints: settle mixed/topology fixtures at HIGH until each carrier has a passing reader control and projected expectations. Check context forwarding and refusal locks before widening an API; preserve empty outer scope and test exact errors on otherwise-admissible inputs.
- Carry-forward execution constraints: inspect scalar full/partial entry points because runRule can mask a missing addressed context. Per-row computation readback uses the complete numeric checker with row target scope; the legacy fixed-target checker changes implicit-message growth. Bind a dependent lowering result before destructuring its pair/sum to avoid expensive elaborator reduction.
- Consumer-facing changes still require exact target policy, aggregate fillability and dependency observations from their owning folds; do not substitute a successful fixture admission for runtime coverage. [Source routing](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) and [probe procedure](TESTING-KERNEL-PROBES.md#the-kernel-runtime-probe-route) own external commands and preconditions.

## Verified gate boundary

- Outer-bound evidence-only readback: 10,816 full and 10,816 partial pointer/type matches, fresh HIGH review with no actionable finding, final hygiene and local commit complete.
- Preceding executable boundary: 2,162-job integration and 51-projection evidence gate passed; subsequent edits did not change execution.
- Last full replay: 59,766 matches; zero divergence/fault/unattributed; 3,052 rows, 217 without matching artifacts, six preparation refusals. The outer-bound capture is checked separately; one evidence-only family has closed since replay.
- [Command ladder](TESTING.md#command-ladder), [replay cadence](TESTING.md#population-replay-cadence) and [review disposition](TESTING.md#review-convergence-and-landing-gate) govern future gates. This planning change requires documentation checks only.
- The [custom test-range route](sources/custom-field-probes.md#src-custom-test-range) owns its specific observation blocker. The [sync ledger](A12-DMKITS-SPEC-SYNC-LEDGER.md) owns handoffs; the owner carries requests. Do not resend them or infer upstream completion.
