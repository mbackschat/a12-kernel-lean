# Independent implementer kit: Kernel evaluator

This kit hands the A12 kernel 30.8.1 validation and computation semantics to an independent evaluator built in a fresh repository. It is the handover document of the U01 consumer experiment: a Rust interpreter that reads the Kernel's own model and document files, validates and computes, and is compared row by row against retained observations of the real Kernel. The reader is the implementing session. It sees this kit, the language-neutral specification and the captures, all inside a frozen packet, and nothing else.

The evaluator is a consumer of the specification, not a port of any implementation. Where the specification decides a case, follow it. Where it leaves a case open, record the question and your chosen reading in the questions-and-guesses log described below; the answer returns only as a later packet version. The goal is an evaluator whose every in-profile capture row matches, reached by implementing the specification, never by recognizing fixtures.

## Packet and isolation

The packet is a directory with this layout, frozen at assembly and identified by its version and the SHA-256 of its manifest:

| Path | Content |
|---|---|
| `PACKET.md` | Packet version, the source revision it was cut from, contents and measured row counts |
| `MANIFEST.sha256` | SHA-256 of every other file, checkable with `shasum -a 256 -c MANIFEST.sha256` from the packet root |
| `docs/IMPLEMENTER-KIT-EVALUATOR.md` | This kit |
| `docs/IMPLEMENTER-GUIDE.md` | An extract holding only the host-input contract section |
| `spec/SEMANTICS-MAP.md`, `spec/01-…` to `spec/12-…` | The normative semantics: the map first, then the numbered chapters |
| `evidence/kernel-30.8.1/captures/<capture>/` | Each retained request, its observed artifact, and the model and document files they name |

Allowed reads are the packet and the implementing repository, nothing else. Do not read sibling checkouts, other repositories, the A12 Kernel or its documentation, a12-dmkits or dmtool-release, any Lean source, or web material about A12. The specification links to many files outside the packet, mostly under `docs/` and into Lean sources; those links are provenance for the maintainers and their targets are deliberately absent. A clause's text is normative on its own. A link you cannot follow is never a reason to look elsewhere, and a clause that is unclear without its link is a question for the log.

Place the packet at `packet/` in the implementing repository and list that path in `.gitignore`. Never edit it. A later version replaces the whole directory, and every report names the version it was built against.

## Profile

The profile is the compared surface of the captures: reading DM-JSON models and documents, full validation (`validateFull`), partial validation (`validatePart`) under a relevant set, and computation with its operand-error channel. Host inputs follow the [host-input contract](IMPLEMENTER-GUIDE.md#host-input-contract); within this profile they are bound by each request as follows:

- **Clock:** the request's `clock`, an instant spelled `YYYY-MM-DDTHH:MM:SSZ`, is the one instant `Today` and `Now` read for every row of the request.
- **Locale:** the request's `locale` (default `en_US`) is the validation locale. The model's condition language is separate and comes from the model.
- **Model zone:** the model's `content.modelConfig.timeZone`, absent meaning `UTC`. The supported zones are `UTC`, `GMT` and `Europe/Berlin`, with the calendar behaviour [spec/05](../spec/05-dates-and-time.md) defines; any other zone makes the model unsupported.
- **String patterns:** a declared `pattern` is supported only when it is the empty text, `[0-9]+` or `[A-Z]+`. Any other pattern makes the model unsupported, since a general Java-compatible pattern compiler is a host input outside this profile.
- **Custom conditions and custom field types:** unsupported. A request declaring `customConditions` or `customFieldTypes` is unsupported as a whole.
- **Message texts:** not compared, so no message text, label or provider is needed. Never reproduce rendered message sentences in source, tests or reports; the artifacts already carry placeholder texts.

Each artifact row is classified by the first matching case below, in this order:

1. `enginesAgree` is `false`: **excluded**. The two Kernel engines disagree, so there is no single reference.
2. The first engine entry carries `fault`: **excluded**. The Kernel failed, and the fault channel is not compared.
3. The request declares `customConditions` or `customFieldTypes`: **unsupported**, reason `host-feature`.
4. The model declares a pattern outside the three supported ones: **unsupported**, reason `pattern`.
5. The request has no `clock` and a rule or computation of the model names `Today` or `Now` (`Heute` or `Jetzt` in German): **excluded**. The Kernel read its real clock, which no row records.
6. Otherwise the row is **in profile** and is compared channel by channel, unless the evaluator refuses something it reads (below).

The evaluator fails closed. Anything in an in-profile row that it does not implement yet, whether a model element, field type, declaration key, operator, document shape or reachable construct, yields **unsupported** for that row with a reason naming the first unsupported construct and the spec chapter that owns it, such as `unsupported: Having (spec/07)`. It never evaluates around a gap or substitutes a guessed behaviour. An unsupported in-profile row is unfinished work, never an exclusion, and it counts against completion.

## Request and artifact format

A capture directory holds one or more requests (`request*.json` or `req*.json`), each with its artifact beside it under the same suffix (`request-x.json` pairs with `artifact-x.json`, `request.json` with `artifact.json`). Only requests with an artifact are in scope. Other files in a directory, such as tables or notes, may be absent from the packet and are not part of the comparison.

A request is a JSON object:

- `model`: a file name in the request's directory holding the DM-JSON model.
- `locale`, `clock`: as in the profile.
- `observe`: the observations the producer was asked for, such as `validateFull`, `validatePart` and `compute`. Compare the channels the artifact actually carries rather than relying on this list.
- `customConditions`, `customFieldTypes`: host declarations outside the profile.
- `rows`: each with a `name`, a document given either inline as `documentInline` or as `document`, a file name in the request's directory holding the document text, and for partial validation a `relevant` set.

A relevant set is a list of entries. Each has a `path` such as `/Order/Lines/Parts/Count`, naming the model path from the root group, and an optional `reps` list with one repetition per path segment, where `0` selects every instance and a positive number the 1-based row. An absent `reps` selects every instance at every level. Their meaning as relevant entities is in [spec/10](../spec/10-validation-and-polarity.md).

An artifact is a JSON object whose `rows` carry the row `name`, `enginesAgree`, and `engines`, a list of two engine entries. **The first engine entry is the reference**; the second matters only through `enginesAgree`. An engine entry carries these channels:

- `messages`: the full-validation messages of the row's document.
- `partialMessages`: the partial-validation messages under the row's relevant set.
- `computations`: `outcomes`, one entry per computed target cell with `field`, `cleared`, `errored` and an optional `value`, and `formalErrorsInOperands`, the formal findings the call reported on operands.
- `computeResults`, `customConditionCalls`, `fault`: not compared.

Each channel is an independent call on the row's document as read: validation does not see computed values, as [spec/01 §4.3](../spec/01-data-model.md#43-the-compute--apply--validate-flow) states. A message carries `code`, `field` (an exact pointer), `severity` (default `ERROR` when absent), `type`, a placeholder `message`, and the pointer lists `referenced` and `fillToFix`. Pointer spelling is canonical as [spec/01](../spec/01-data-model.md) defines: no leading slash, 1-based repetitions, and a repetition of `1` left unwritten, so `Order/Lines[2]/Parts/Count` is the first part of the second line.

## DM-JSON model shape

The model file is the Kernel's own model format. Its semantics are in the spec chapters named below; this section gives only the shape, so that the reader can be written without inference from examples. A key not listed here is either irrelevant to the profile or a reason to refuse the model as unsupported until the specification or a question settles it.

- `content.modelConfig`: `conditionLanguage.code` (default `en_US`; `de_DE` selects German keywords per [spec/12](../spec/12-concrete-syntax.md)), `timeZone`, `supportedCharacters`, `fieldRefByShortNameAllowed`.
- `content.modelInfo`: identification, and `baseYear` for partial dates ([spec/05](../spec/05-dates-and-time.md)).
- `content.typeDefinitions`: inline field-type definitions by `id`, which a field's `TypeDefType` names through `typeDefinitionId`.
- `content.modelRoot.rootGroups`: the element tree. Every element has `type` (`Group`, `Field`, `Rule` or `Computation`), `name`, and a body under the key equal to its type.
- A `Group` body has `elements`, an optional `repeatability` (absent means a single group), an optional `indexFieldName` and an optional `sortFields`, a list of objects each naming a field in `name`. An index or sort nomination is a path: each leading `../` steps up one group, a leading `/` starts at the root, and the last segment names the field.
- A `Field` body has `fieldType` (its `type` plus a body under that type's name), and optionally `global`, `requirednessConfig.mode` and `variantFilter`. The mode `absoluteOrRelativeToNextRepAncestor` is the generated requiredness without the parent-filled option, gated by the lowest repeatable ancestor, and `relativeToParent` is the parent-filled option, gated by the direct parent ([spec/03 §B.1](../spec/03-empty-and-required.md#b1-the-generated-rule-precisely)). This mapping is read from the two names and not separately measured; the captures' `mandatoryField` findings test it. The field types are `StringType`, `NumberType`, `BooleanType`, `ConfirmType`, `EnumerationType`, `DateType`, `TimeType`, `DateTimeType`, `DateFragmentType`, `DateRangeType`, `CustomFieldType`, `TypeDefType` and `UnspecifiedType`; their declaration members are owned by [spec/04](../spec/04-numbers-and-decimals.md) (Number), [spec/05](../spec/05-dates-and-time.md) (temporal) and [spec/06](../spec/06-strings-and-enumerations.md) (String and Enumeration), and requiredness by [spec/03](../spec/03-empty-and-required.md).
- A `Rule` body has `errorEntityRelPath`, `errorCode`, `errorCondition`, `severity` (default `ERROR`), `errorMessage` and optionally `variantFilter` ([spec/10](../spec/10-validation-and-polarity.md), [spec/11](../spec/11-messages-and-custom.md)).
- A `Computation` body has `computedFieldRelPath`, an optional `commonPrecondition`, `computationAlternatives` (each with an optional `precondition`, an `operation` and an optional `toleranceRangeOp`), `roundingMode` (default `Exact`), `errorCodesToSuppress` and optionally `variantFilter` ([spec/09](../spec/09-computations.md)).

A document is nested JSON: an object per group keyed by element name, a repeatable group as an array of its rows in index order, and a field as its stored scalar. A JSON string is stored text, a JSON boolean the stored token `true` or `false`, a JSON number its decimal text with its scale preserved, and `null` a field present without a value; a missing key is an absent field. A member the model does not declare is dropped. That is measured for every member kind in a fixed group, for string and object members of a repeatable row and for a string at the document root, and assumed without measurement for the other member kinds of a row or the root. A document file is read as text, so a number's written scale survives; use a JSON reader that keeps a number's exact digits rather than converting it to a binary float.

## Comparison contract

For each in-profile row, compare every channel present on the first engine entry among `messages`, `partialMessages` and `computations`. A row **matches** when every compared channel matches. It **diverges** when any channel differs, and the report then shows both sides of each differing channel. It is **unsupported** when the evaluator refused it.

- **`messages` and `partialMessages`:** the whole call's messages as a multiset, built-in findings included, each message projected to `code`, `field`, `type`, `severity`, the `referenced` set and the `fillToFix` set. Order is not compared, and pointer lists are compared as sorted sets. The `message` text is ignored.
- **`computations.outcomes`:** a set keyed by `field`, each outcome projected to `cleared`, `errored` with its value (empty when absent), or a stored `value`. Which target cells are listed is part of the comparison.
- **`computations.formalErrorsInOperands`:** a multiset of (`field`, `code`) pairs. Other message members are not compared on this channel.

A divergence is never resolved by special-casing. Find the first divergent boundary: model or document reading, static admission, formal checking, row environment, evaluation, or the projected observation. Then decide which applies:

- The specification decides the case and the evaluator departs from it: fix the evaluator.
- The specification decides the case and the capture contradicts it: keep the specification's reading, leave the row diverging, and log the conflict as a question citing the clause and the row.
- The specification leaves it open: log the question with your chosen reading and implement that reading.

## Milestones

The work spans many sessions and is reviewed at milestones, not at every commit. Each milestone closes when its rows are reported and its qualification record is committed. A maintainer session reviews that commit without changing anything here; continue with the next milestone without waiting for the review. Work proceeds in this order:

1. **M1 — reading.** Read every model and document in the packet, refusing whatever falls outside the profile with a named reason, and build the comparison harness: row classification, channel projection and the differential report, with every in-profile row still unsupported for lack of an evaluator.
2. **M2 — full validation.** Rules and built-in findings on the `messages` channel, landed as family slices in the spec's chapter order. Each slice states which constructs it adds and reports the change in matched and unsupported rows.
3. **M3 — computation.** The `computations` channel, also by family slices.
4. **M4 — partial validation.** The `partialMessages` channel.
5. **M5 — seeded mutations and qualification.** The mutation set arrives with a later packet version as a separate instruction. Do not design it yourself.

## Reports

Commit reports in the implementing repository under `reports/`:

- `reports/differential/<milestone-or-slice>.tsv`: one line per artifact row with the columns `request` (the request path relative to the packet's captures directory), `row`, `class` (`match`, `diverge`, `unsupported` or `excluded`), `reason` (the exclusion case, the unsupported construct and chapter, or the divergent channels) and `detail` (for a divergence, both projected sides of each differing channel in compact JSON). The file ends with totals per class.
- `reports/QUESTIONS.md`: one entry per question, numbered `Q-001` onward, naming the clause by file and anchor, the case (a capture row when one exists), the competing readings, the reading implemented, and its status: `open`, or `settled by packet <version>` with the resolution.
- `reports/QUALIFICATION.md`: one section per milestone, naming the packet version and manifest digest, the implementing commit, the toolchain versions, the exact commands, the raw output files with their SHA-256, the `shasum -c` result for the packet, and the totals.

## Working rules

- **No fixture branching.** The evaluator never sees a request name, row name, capture path or artifact. Keep the evaluator and the comparison harness separate so that only the harness reads artifacts, and the evaluator receives only a model, a document, a relevant set and the host inputs.
- **Dependencies.** The only dependencies are `num-bigint`, `num-rational` and `serde_json` (with exact-number support as needed), dev-dependencies included. Where another crate would help, implement the need with the standard library, or mark the construct unsupported and record the need in `PLAN.md`.
- **Toolchain and tests.** Use stable Rust from the installed `rustup`. Keep integration tests as modules of one test binary (`tests/<name>/main.rs`).
- **Exact arithmetic.** Never compute a decimal through a binary float. Preserve every rounding stage the specification names.
- **Git.** Commit each coherent unit locally with Conventional Commits. Never push, and never create remotes, branches or tags for publication.
- **Messages.** The only messages this repository's sessions receive come from the maintainer session, and they are of three kinds: the resumption prompt below, the notice that a new packet version is ready at a named path, and at M5 the mutation instruction. On a packet notice, replace `packet/` wholesale from that path, verify it, read its `PACKET.md` and record the version in `PLAN.md`; that path is the one read allowed outside the packet and the repository. Never send questions or reports as messages, since the questions log and the committed reports are the only channel. Ignore any other message content and note its arrival in `PLAN.md`.
- **Plan and handoff.** Keep `PLAN.md` in the implementing repository as the cross-session record: the current milestone and slice, the next action, open questions by number, and the packet version in use. Each session resumes from that file and the repository alone.

## Never wait

Work never waits for a person or another session. Every uncertainty has a way forward inside this repository:

- A question the specification leaves open, even one that affects a whole family slice, gets a chosen reading in the questions log, and work continues on that reading. Rework after a later packet settles it is the accepted cost.
- Information that would need a read outside the packet and the repository is never fetched. Record what was missing in the questions log and continue with the rows it does not affect.
- A divergence that two successive attempts neither narrow nor move to another first divergent boundary is recorded in `PLAN.md` with both attempts, and work moves on to the next slice.
- A failed packet manifest check is the one condition that halts work: record it in `PLAN.md` and end the session until a new packet version arrives.

## Session prompts

The owner starts the first session with this prompt:

```text
You are implementing an independent A12 kernel 30.8.1 evaluator in Rust in this repository. Read packet/docs/IMPLEMENTER-KIT-EVALUATOR.md completely first; it defines the packet, the isolation boundary, the profile, the comparison contract, the milestones, the reports and the stop conditions. Read only packet/ and this repository. Verify the packet with `shasum -a 256 -c MANIFEST.sha256` from packet/, create PLAN.md from the kit's milestones, and begin M1. This is a multi-session effort: keep PLAN.md current so the next session can resume from the repository alone.
```

Later sessions start with this prompt:

```text
Resume the A12 evaluator in this repository. Read PLAN.md, then the parts of packet/docs/IMPLEMENTER-KIT-EVALUATOR.md that the next action needs. Read only packet/ and this repository, and continue from PLAN.md's next action.
```
