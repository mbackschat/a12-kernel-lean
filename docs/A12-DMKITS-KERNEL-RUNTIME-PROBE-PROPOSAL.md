# Cross-project proposal: an autonomous kernel-runtime observation route

Temporary proposal, live until a12-dmkits accepts or refuses it. After disposition its durable producer facts move to a12-dmkits' own owners and this file is deleted; only the local consequence stays here, in [`SOURCES.md`](SOURCES.md) and the affected gap entries.

## What this asks for

One JVM-only, non-shipped probe entry point in a12-dmkits that runs the **real kernel's runtime evaluation** over a supplied model and document, and writes a deterministic JSON observation artifact. Invoked as a Gradle task, not a CLI verb.

It asks for **no** change to the released binary, the native profile, or the eval path Groovy was severed from.

## Why this project cannot do it locally

Static legality is already self-serve and works well: `rule check`, `model check`, and `computation add --dry-run` reach the real kernel's consistency oracle and report `verification: KERNEL_CONFIRMED`. Two operator families were measured here that way on 2026-08-11 with no upstream involvement, 58 rows total.

Kernel **runtime** has no local route at all. The CLI's runtime verbs run the kernel-free `:interpreter` (`engine: DM_INTERPRETER`), which is triangulation and not kernel evidence, and this project must never link, call, or ship the kernel itself. So every runtime question becomes an `EXP-` round trip through the owner. [`EXP-2026-08-11-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#exp-2026-08-11-01--does-the-referenced-channel-expand-an-unstarred-group-operand) cost one full handoff to answer one question, and it was answered in a purpose-written Kotlin test.

Five recorded obligations are blocked on runtime observation and would become self-serve: the filtered-star operand's coordinates, an unbound deeper repeatable descendant of an expanded group, `RepetitionNotUnique`'s cross-repetition reference coordinates, `fillToFix` in every family, and SG4's multi-step String/Number composition calibration.

## The constraint this proposal respects

Read-only audit at a12-dmkits `8094f6643ef3ad01d40dd6d3675356196374e104`:

- `docs/ARCHITECTURE.md` states the kernel's runtime evaluation does Groovy runtime codegen and is not AOT compilable. The runtime verbs therefore run on the kernel-free `:interpreter` as the sole runtime eval engine, `Cli.JVM_ONLY_VERBS` is empty, Groovy is excluded from `nativeImageClasspath`, and the `--kernel` eval option was retired in Set V (2026-07-12). `NativeImageRuntimeVerbsTest` asserts the retired flag is rejected on every profile.
- Groovy is retained in the JVM build for exactly one purpose, the consistency oracle behind `rule check`.

So a CLI runtime verb is the wrong shape: it would repopulate `JVM_ONLY_VERBS`, re-couple Groovy to an eval path that was deliberately severed, and force the native-image guards to carry an exception. Nothing in this proposal touches that boundary.

Linkage is not the obstacle and is not being asked for: `adapter/src/main/java` already links the kernel (`KernelAdapter`, `KernelModelPreparation`, `KernelResolvers`), which is what makes `rule check` a real kernel verdict.

## The capability already exists one layer in

`adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/RuntimeLaws.java` (1631 lines at the audited revision) already owns kernel execution for both strategies and is JVM-only by construction:

| surface | what it gives |
|---|---|
| `kernelEngine(String modelJson)` | dynamic Groovy `KernelEngine` |
| `kernelJavaEngine(String modelJson)` | generated Java `JavaKernelEngine` |
| `doc()` | fluent document instance builder |
| `model(String)`, `withRule(...)`, `withComputation(...)`, `withTieredComputation(...)` | model assembly |

`UnstarredGroupReferenceDiffTest` and `CurrentRepetitionDiffTest` already read complete `referenced` sets and tri-check dynamic Groovy against generated Java against the interpreter. The gap is only that none of this is reachable without authoring a new Kotlin test per question.

## Requested shape

A Gradle task on the module that already owns the harness:

```
./gradlew :adapter:kernelProbe -Prequest=<request.json> -Pout=<artifact.json>
```

**Request**: a `dmtool`-authored model file plus optional rule or computation additions plus one or more documents, as an ordered list of named rows. Authoring stays on the existing structured verbs; the probe should not grow a second authoring surface.

**Artifact**, per row and per engine: the fired messages with code, message type and polarity, error pointer, `referenced`, and `fillToFix`, in a deterministic order, plus a header carrying `schemaVersion`, `dmtoolVersion`, kernel built and runtime versions, the source revision, and whether the revision or the worktree was used. An explicit per-row `enginesAgree` flag, never a merged set.

**Not requested**: a CLI verb, any native-profile change, Groovy on the release eval path, a new authoring surface, new semantics, and any artifact this project would have to keep re-deriving.

## Producer and consumer responsibility

a12-dmkits owns kernel invocation, engine identity, and the artifact schema and its version. This project owns pinning the artifact bytes by SHA-256 and replaying them in its `Evidence/` tree, which is exactly how the existing retained observation bundle is consumed. No kernel dependency, linkage, or shipped component enters this repository, and no producer contract is assumed to be standing.

## Compatibility and retirement

Purely additive and invisible to the release: no verb, no native surface, no change to `JVM_ONLY_VERBS` or the Groovy exclusion. If the capability is later retired, artifacts already produced stay valid as immutable evidence because they carry their own version header, and this project falls back to `EXP-` requests. Nothing here becomes a second live upstream specification.

## Separating acceptance cases

Each is chosen to fail a plausible wrong implementation rather than to confirm the intended one.

1. **Engine disagreement must survive.** A row where dynamic Groovy and generated Java differ reports both engines separately with `enginesAgree: false`. A merged or first-wins set fails this case, and it is the one that would silently destroy the evidence value.
2. **Coordinate identity round-trips.** A starred group's expanded `referenced` pointer comes back wildcarded and an unstarred one concrete, reproducing `KF183` through the probe instead of through a hand-written test. This is the case that proves the probe can replace a bespoke test.
3. **Polarity and `fillToFix` stay coupled.** An OMISSION firing reports non-empty `fillToFix`, a VALUE firing reports empty.
4. **Determinism.** Two runs over identical input produce byte-identical artifacts, so the consumer can pin a SHA-256.
5. **A statically refused model is a refusal, not silence.** A model the consistency oracle rejects fails with its diagnostics rather than yielding an empty runtime observation, which would read as "nothing fired".
6. **The release boundary is untouched.** `NativeImageRuntimeVerbsTest` is unchanged and still green, `--kernel` is still rejected on every profile, and `JVM_ONLY_VERBS` is still empty.

## Acceptance gates

The project's existing gate tiers green; the six cases above present as maintained tests; the artifact schema documented or published the way `schema result` is; and the handback naming the exact reviewed revision, the task invocation line, the schema location, and a per-surface disposition including anything refused with its reason.

## What a refusal should say

A reasoned refusal is more useful than a partial build. It should name which of the six cases cannot be met and why, and whether an `EXP-` round trip remains the intended route for runtime questions. This project will then keep filing `EXP-` entries and record the refusal as the reason the route stays closed.
