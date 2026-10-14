# Residual semantic obligations

This is the open-only inventory of residual obligations toward conformance with A12 Kernel 30.8.1. [K01–K22](PLAN.md#remaining-conformance-checklist) is the owner-requested closure checklist, followed by [Rust and SMT consumer development](PLAN.md#consumer-development). C01–C22 and R01–R03 are completed baselines. Historical D identifiers in the shards no longer exclude required work: the [current routing table](PLAN.md#remaining-gap-routing) assigns every family and former exclusion. Broad coverage and calibration do not close all compositions.

## Query contract

[`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns implemented/proved/evidenced behavior, [`SOURCES.md`](SOURCES.md) owns provenance and [`PLAN.md`](PLAN.md) owns selection. This hub preserves stable links to the 24 family records in six shards. The shards retain only residual distinctions and links to their owners; completed milestones are removed.

- `remaining` and `diagnostics` identify residual behavior or exact output distinctions, bounded by the record's scope/exclusion links. Since the K19 disposition (2026-10-14), a `remaining` bullet is an evaluator omission that names its item in the [returned-omission queue](PLAN.md#k19-returned-omissions), and `diagnostics` and `evidence-needed` are correspondence work for K20.
- `evidence-needed` means additional correspondence is missing; it does not by itself mean executable support is absent.
- `host-boundary` and `representation-boundary` preserve caller requirements or explicit limits of a named API. Every host input the account takes is a row of the [host-input contract](IMPLEMENTER-GUIDE.md#host-input-contract). They are not permission to silently produce a wrong result.
- `consumer-gated` identifies transport, proof or product work whose exact consumer contract must be selected in the planned consumer phase; it is not automatically evaluator work.
- `verification-needed` and `api-audit` preserve an unresolved historical claim or predicted API distinction without promoting it to a confirmed current defect. A current reader discriminator must settle it before work is selected.
- `reopen-when` states the trigger; `route-state: discovery-required` describes investigation readiness, not an instruction to resume. A reproduced accepted-scope defect belongs in the selected correction, never in an exclusion by relabelling.

| shard | families |
|---|---|
| [`keystone.md`](gaps/keystone.md) | computation scheduling, addressed-family calibration, result projection |
| [`numeric-and-temporal.md`](gaps/numeric-and-temporal.md) | Number authoring and targets, calendar and temporal carriers, extrema and distinct-count folds, the runtime Number formal cascade |
| [`strings-and-messages.md`](gaps/strings-and-messages.md) | String and custom-field completion, enumerations and value lists, message construction and its parameter grammar, the custom-condition callback |
| [`paths-and-groups.md`](gaps/paths-and-groups.md) | addressing and static legality, group lists and counts, the `Having` filter and its reference gates, repetition-reference binding |
| [`targets-and-derivation.md`](gaps/targets-and-derivation.md) | bare-constant targets, mandatory-information derivation, the refusal-class denominator |
| [`conformance-evidence.md`](gaps/conformance-evidence.md) | retained Kernel-correspondence coverage |

```sh
rg -n '^### SG' docs/SEMANTICS-GAPS.md                                    # locate a family
rg -n '^<a id="gap-' docs/gaps                                            # its detailed record
rg -n '^- `state`:|^- `blocked-on`:|^- `reopen-when`:|^- `remaining`:|^- `route-state`:' docs/gaps
```

A gap carries only current missing behavior, prerequisites, discriminators, consumer consequences, evidence needs, route state, and reopening triggers. Implemented detail stays behind an implementation-map link, exact source revisions stay behind a source-record link, and completed narrative is deleted.

## Dependency boundary

The former SG1 → SG2 → SG4 construction sequence is represented. [Checked-document construction](IMPLEMENTATION-MAP.md#immutable-checked-document-construction), [addressed operands](IMPLEMENTATION-MAP.md#9--repetition-and-iteration) and [computation scheduling](gaps/keystone.md#gap-sg4) are existing foundations. Their residual profiles do not schedule reconstruction or another prerequisite programme.

## Keystone residuals

### SG4 — computation scheduling and state transition

<a id="gap-sg4"></a>
- [residual record](gaps/keystone.md#gap-sg4)

<a id="sg18--addressed-computation-family-calibration"></a>
### SG18 — addressed computation family calibration

<a id="gap-sg18"></a>
- [residual record](gaps/keystone.md#gap-sg18)

### SG16 — computation result projection and application

<a id="gap-sg16"></a>
- [residual record](gaps/keystone.md#gap-sg16)

## Semantic-family gaps

### SG5 — numeric authoring and target completion

<a id="gap-sg5"></a>
- [residual record](gaps/numeric-and-temporal.md#gap-sg5)
<a id="gap-sg5-unstarred-repeatable-group-presence-reference"></a>
- [unstarred repeatable group presence reference](gaps/numeric-and-temporal.md#gap-sg5-unstarred-repeatable-group-presence-reference)

### SG6 — temporal authoring, calendar, and target completion

<a id="gap-sg6"></a>
- [residual record](gaps/numeric-and-temporal.md#gap-sg6)
<a id="gap-sg6-temporal"></a>
- [temporal record alias](gaps/numeric-and-temporal.md#gap-sg6-temporal)

<a id="sg23--the-temporal-extrema"></a>
### SG23 — the temporal extrema: operand gate, element type, and fold

<a id="gap-sg23"></a>
- [residual record](gaps/numeric-and-temporal.md#gap-sg23)

<a id="sg21--the-declared-kindformat-split-across-temporal-carriers"></a>
### SG21 — the declared kind/format split across temporal carriers

<a id="gap-sg21"></a>
- [residual record](gaps/numeric-and-temporal.md#gap-sg21)

### SG7 — String, pattern, and custom-field completion

<a id="gap-sg7"></a>
- [residual record](gaps/strings-and-messages.md#gap-sg7)

### SG25 — the message parameter grammar and its terminal set

<a id="gap-sg25"></a>
- [residual record](gaps/strings-and-messages.md#gap-sg25)

### SG8 — Enumeration and value-list completion

<a id="gap-sg8"></a>
- [residual record](gaps/strings-and-messages.md#gap-sg8)

### SG9 — paths, indices, and static legality completion

<a id="gap-sg9"></a>
- [residual record](gaps/paths-and-groups.md#gap-sg9)

### SG10 — message construction and formal-output integration

<a id="gap-sg10"></a>
- [residual record](gaps/strings-and-messages.md#gap-sg10)

### SG11 — custom-condition checked orchestration

<a id="gap-sg11"></a>
- [residual record](gaps/strings-and-messages.md#gap-sg11)

### SG29 — semantic-index reads beyond the scalar lookup

<a id="gap-sg29-overlap-matrix"></a>
- [Selected overlap closure matrix](gaps/paths-and-groups.md#gap-sg29-overlap-matrix)
<a id="gap-sg29"></a>
- [residual record](gaps/paths-and-groups.md#gap-sg29)
<a id="gap-sg29-cache-order"></a>
- [Shared message-cache producer closure matrix](gaps/paths-and-groups.md#gap-sg29-cache-order)

### SG13 — group-list and group-count completion

<a id="gap-sg13"></a>
- [residual record](gaps/paths-and-groups.md#gap-sg13)

<a id="sg17--having-filter-leaf-and-connective-completion"></a>
### SG17 — `Having`-filter leaf and connective completion


<a id="gap-sg17"></a>
- [residual record](gaps/paths-and-groups.md#gap-sg17)
<a id="gap-sg17-closure-matrix"></a>
- [Remaining Having closure matrix](gaps/paths-and-groups.md#gap-sg17-closure-matrix)

<a id="sg20--filter-reference-scope-and-iteration-gates"></a>
### SG20 — filter reference scope and iteration gates

<a id="gap-sg20"></a>
- [residual record](gaps/paths-and-groups.md#gap-sg20)

<a id="sg19--repetition-reference-binding"></a>
### SG19 — repetition-reference binding and its two sources

<a id="gap-sg19"></a>
- [residual record](gaps/paths-and-groups.md#gap-sg19)

<a id="sg15--bare-constant-target-families"></a>
### SG15 — bare-constant target families

<a id="gap-sg15"></a>
- [residual record](gaps/targets-and-derivation.md#gap-sg15)

### SG14 — mandatory-information derivation

<a id="gap-sg14"></a>
- [residual record](gaps/targets-and-derivation.md#gap-sg14)

### SG27 — Number presentation information and the remaining formal key families

<a id="gap-sg27"></a>
- [residual record](gaps/numeric-and-temporal.md#gap-sg27)

## Cross-family conformance gap

### SG12 — retained Kernel correspondence coverage

<a id="gap-sg12"></a>
- [residual record](gaps/conformance-evidence.md#gap-sg12)
