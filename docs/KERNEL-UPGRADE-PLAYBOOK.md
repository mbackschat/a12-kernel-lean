# Kernel upgrade playbook

This playbook owns the routine for moving the theory from one A12 kernel release to the next. It was worked once, from kernel 30.8.1 to 31.1.1 between 2026-11-02 and 2026-11-04; that upgrade's decisions, batches and close are recorded in [the migration section of the plan](PLAN.md#kernel-31-migration), which is the worked example to read beside this routine. A later upgrade gets its own section in [`PLAN.md`](PLAN.md) for its sequencing; this document owns only the steps and the traps that recur.

## Rules that hold throughout

- **The owner decides the target and the floor.** The default is a single floor: one theory targets one kernel version, and the previous account stays buildable from a tag. Dual support is a separate owner decision, and the release selector it needs is introduced at the first measured divergence, never in advance ([`ARCHITECTURE.md`](ARCHITECTURE.md#one-kernel-version-per-theory)).
- **A clause moves only on a measured row:** a verdict-delta row from a12-dmkits (input, observed on the old kernel, observed on the new one, oracle) or this project's own measurement. A changelog or a source reading moves no clause by itself.
- **Retained evidence is never rewritten.** Bundles keep their bytes and their kernel stamp; observations on the new kernel go into a new `evidence/kernel-<version>/` root ([`EVIDENCE.md`](EVIDENCE.md#evolution)).
- **A code's name is not its meaning.** Check every static diagnostic code the theory emits against its meaning on the new kernel, because a code can keep its name and change its trigger. Kernel 31.1.1 moved `MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED` from `SumOfProducts` to `SumOfTerms`.
- **a12-dmkits measures; this project adopts.** A correction from a committed, reviewed peer revision is an inbound change with no ledger entry. Only a correction this project originates becomes a `SPEC-` entry (the `spec/` hard rule in [`CLAUDE.md`](../CLAUDE.md)).

## 1. Decide and freeze

1. Record the owner's decision in a new [`PLAN.md`](PLAN.md) section with the keys the 31.1.1 section uses: `decision`, `frozen`, `method`, the old-kernel measurement route, `owed`, `models`, one checkbox per batch, `next` and `close`.
2. Tag the last commit that targets the old kernel locally as `kernel-<old>-final`, and name the tag in the plan section.
3. Change the goal line of [`CLAUDE.md`](../CLAUDE.md) to the new version.
4. Repoint the kernel source routes in [`SOURCES.md`](SOURCES.md) at the new `../a12-kernel` revision, keeping the sentence "at revision `<rev>` of the `../a12-kernel` checkout": the [coverage report](../scripts/report-conformance-coverage.sh) reads the pin from it and refuses a checkout at another revision. Readings taken on the old kernel stay cited at the old revision.

## 2. Collect the deltas

1. Ask a12-dmkits for its change inventory. It is changelog and source reading and schedules work only. Before every further request, search the peer's [`KERNEL-FINDINGS.md`](../../a12-rulekit/docs/KERNEL-FINDINGS.md) heading-first for an existing measurement.
2. Settle the retained probe models. a12-dmkits migrates them through the new kernel's model migrator; re-check every migrated model against its original on an exact-decimal parse here, and record what changed in the plan's `models` key. For 31.1.1 only the version stamp changed.
3. Receive the verdict-delta letters. Give each one an inbound record in [the inbound handbacks](sources/inbound-handbacks.md) with its file hash, peer revision, oracle, and what was and was not adopted. Classify each claim by the claim-discharge table before adopting it: a letter that supplies an outcome has not discharged its mechanism, and a peer row that contradicts the letter's prose wins (31.1.1's `SumOfTerms` empty-read rule was corrected this way).

## 3. Adopt in batches

1. Group the letter rows into batches that share one mechanism and order them risk-first. The 31.1.1 order started with temporal behaviour, because that kernel replaced its calendar backend.
2. For each batch, follow the ordinary family routine in [`TESTING.md`](TESTING.md): adopt the rows into `spec/` as an inbound change with its [`SOURCES.md`](SOURCES.md) update, implement them in Lean red/green, run one integrated gate and one cold review at the batch boundary, and write the batch's adoption record in [the inbound handbacks](sources/inbound-handbacks.md). Record each row the letters leave unmeasured as a gap bullet in its family shard.
3. Keep the frozen replay honest. A retained row whose code the new kernel renamed is compared under the new name through the rename map in [`RuleCheckProjection.lean`](../A12Kernel/Evidence/RuleCheckProjection.lean). A row whose outcome the new kernel changed is deferred there with a named reason. Neither is re-expected. The map is pairwise, so a second upgrade over the same frozen bundle composes it with the next one.
4. Replay the frozen population at each batch boundary, not only at the close, and attribute every new divergence to the batch's adopted rows. `lake test` replays the retained rule-check, declaration and compact observations but none of the retained runtime requests, so the population replay is the only check that runs those against the theory; after one batch its new divergences are still few enough to attribute. A new operator the peer catalog gains also gets its row in [the construct inventory](CONFORMANCE-CONSTRUCTS.tsv) in its own batch, or the coverage report refuses to run.
5. Collect every high-blast edit of the upgrade behind one rebuild, as [`CLAUDE.md`](../CLAUDE.md#building--running) directs.
6. A measured clause adopted into `spec/` before its Lean batch is listed in the plan's `owed` key until that batch lands.

## 4. Close

Each step names the surface it changes; together they are the close commit set.

1. **Version stamp.** Set `kernelVersion` in [`Basic.lean`](../A12Kernel/Basic.lean) to the new version and leave `retainedEvidenceKernelVersion` at the version of the frozen bundles. If a bundle of the new kernel already exists by then, the bundle reader must accept each retained version, which is a decision for that close.
2. **Protocol.** Keep `protocolVersion` while the wire format is unchanged: the request's `kernelBehaviorVersion` follows `kernelVersion`, and a client asserting the old version is refused with `kernelBehaviorVersionMismatch`, an explicit error. Update every request and response under [`examples/reference-cli/`](../examples/reference-cli/), the suites under [`reference/`](../reference/), [`PROTOCOL.md`](PROTOCOL.md), the top-level [`README.md`](../README.md) and the implementer kits. The process test's wrong-kernel control then uses the old version. Mark the commit as a breaking change.
3. **Frozen requests.** Retained protocol requests are replayed and matched to suite cases under the current version through `currentRequest` in [`ValidationProjection.lean`](../A12Kernel/Evidence/ValidationProjection.lean); confirm it still covers every retained request family.
4. **Scope statements.** State the new version in [`spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) §0, keeping its sentence that a clause the upgrade did not revisit rests on the old kernel's evidence. Update the frozen-bundle paragraph of [`EVIDENCE.md`](EVIDENCE.md#evolution). Neither states new kernel behaviour, so neither needs a ledger entry.
5. **Records.** Bring the `state` and `sync` lines of the upgrade's inbound records up to date: a line saying Lean does not yet implement an adopted clause goes stale at the close.
6. **Gates.** Run the public-process command list in [`TESTING.md`](TESTING.md#command-ladder) and the trust audit, then regenerate [`CONFORMANCE-COVERAGE.md`](CONFORMANCE-COVERAGE.md) with its population replay. Every divergence, fault and refused row it shows must trace to an adopted delta, recorded in the plan section with the method of attribution; the committed divergence table is then the baseline whose diff shows a later regression.
7. **Measurement checkout.** Re-pin the [measurement checkout](sources/cross-layer-routes.md#src-measurement-checkout-route) when the first measurement on the new kernel runs, not before, and say in its record meanwhile that the pinned launcher measures the old kernel.
8. **Peer reply.** Send a12-dmkits a pointer-based reply: record anchors, the closing revision and pending ledger entries, not a fresh account.
9. **Consumers.** Move consumer handovers, such as the evaluator kit's packet, to the new version when their next packet is assembled. Frozen packets keep the version they were built on.
10. **Retire.** Delete upgrade-specific proposals once their items have graduated to their owners, and mark the plan section closed.

## 5. First calibration on the new kernel

The upgrade closes with most clauses carried forward on old-kernel evidence. The first calibration batch re-pins the measurement checkout, opens `evidence/kernel-<new>/`, re-captures the retained requests on the new kernel and replays them: the rows that disagree are the remaining behaviour-change worklist, and each agreeing row moves its clause onto new-kernel evidence. The unmeasured rows the batches recorded as gap bullets are its first candidates.

## Traps seen in the 31.1.1 upgrade

- The sibling kernel names its runtime package after the release (`_30_8`, `_31_1`). The coverage report finds the package instead of naming it; any new script that reads kernel sources must do the same.
- The theory's evidence loader, the candidate-conformance check and the replay of retained requests all compared against the single version constant. Changing it alone breaks retained evidence, which is why the retained version is a separate constant.
- A letter's prose and its locked rows can disagree; adopt the rows.
- Unmeasured rows are easy to lose between letters and batches. Record each as a gap bullet when its batch lands, not at the close.
- The 31.1.1 batches skipped the population replay, and the close found 1604 divergences to attribute at once. Nearly all read temporal values, many through daylight-saving-gap constants that probes outside the temporal families used as poison discriminators, so one temporal delta reached captures about traversal and membership.
- A retained model keeps the model format of the kernel it was captured on, which the new kernel's launcher refuses (`RK_MODEL_VERSION_INCOMPATIBLE` on 31.1.1 for a 30.8.1 model), and a rule check against it can still return refusal codes beside that diagnostic. The first 31.1.1 batch re-authored its models with the structured verbs; read the model-check verdict before any row of a reused model.
- A replay fault is not always a defect: Lean models kernel 31.1.1's whole-call assembly failure for a leap-day target as a refusal, which the frozen 30.8.1 rows record as a stored value.
