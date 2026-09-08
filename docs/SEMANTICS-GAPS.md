# Open semantic gaps

This is the open-only work index for convergence toward complete semantic conformance with A12 Kernel 30.8.1. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns implemented, proved, and evidenced coverage. Working context selects uninterrupted work from this index. [`PLAN.md`](PLAN.md) persists a selection only for cross-session handoff.

## Query contract

This file is the hub: it owns selection, the hard-frontier order, and one stable compatibility entry per gap. The detailed obligations live in family shards under [`gaps/`](gaps/), one record per `gap-` anchor, and that is where every edit goes. Read the hub to choose; read the shard to work.

| shard | families |
|---|---|
| [`keystone.md`](gaps/keystone.md) | computation scheduling, addressed-family calibration, result projection |
| [`numeric-and-temporal.md`](gaps/numeric-and-temporal.md) | Number authoring and targets, calendar and temporal carriers, extrema and distinct-count folds, the runtime Number formal cascade |
| [`strings-and-messages.md`](gaps/strings-and-messages.md) | String and custom-field completion, enumerations and value lists, message construction and its parameter grammar, the custom-condition callback |
| [`paths-and-groups.md`](gaps/paths-and-groups.md) | addressing and static legality, group lists and counts, the `Having` filter and its reference gates, repetition-reference binding |
| [`targets-and-derivation.md`](gaps/targets-and-derivation.md) | bare-constant targets, mandatory-information derivation, the refusal-class denominator |
| [`conformance-evidence.md`](gaps/conformance-evidence.md) | retained Kernel-correspondence coverage |

```sh
rg -n '^### SG' docs/SEMANTICS-GAPS.md                                    # choose a gap
rg -n '^<a id="gap-' docs/gaps                                            # its detailed record
rg -n '^- `state`:|^- `blocked-on`:|^- `reopen-when`:|^- `remaining`:|^- `route-state`:' docs/gaps
```

A gap carries only current missing behavior, prerequisites, discriminators, consumer consequences, evidence needs, route state, and reopening triggers. Implemented detail stays behind an implementation-map link, exact source revisions stay behind a source-record link, and completed narrative is deleted.

## Hard-frontier critical path

The binding construction order is **SG1 → SG2 → SG4**. SG1 and SG2 are closed. [Immutable checked-document construction](IMPLEMENTATION-MAP.md#immutable-checked-document-construction) supplies one model-certified input, and the [repetition/iteration boundary](IMPLEMENTATION-MAP.md#9--repetition-and-iteration) supplies canonical addressed operands. SG4 must consume both with an explicit processing context rather than redefine document or address state.

## Keystone construction gaps

### SG4 — computation scheduling and state transition

<a id="gap-sg4"></a>
- [open obligation](gaps/keystone.md#gap-sg4)

<a id="sg18--addressed-computation-family-calibration"></a>
### SG18 — addressed computation family calibration

<a id="gap-sg18"></a>
- [open obligation](gaps/keystone.md#gap-sg18)

### SG16 — computation result projection and application

<a id="gap-sg16"></a>
- [open obligation](gaps/keystone.md#gap-sg16)

## Semantic-family gaps

### SG5 — numeric authoring and target completion

<a id="gap-sg5"></a>
- [open obligation](gaps/numeric-and-temporal.md#gap-sg5)
<a id="gap-sg5-unstarred-repeatable-group-presence-reference"></a>
- [unstarred repeatable group presence reference](gaps/numeric-and-temporal.md#gap-sg5-unstarred-repeatable-group-presence-reference)
<a id="gap-sg5-number-token-group-runtime"></a>
- [Number token group runtime](gaps/numeric-and-temporal.md#gap-sg5-number-token-group-runtime)

### SG6 — temporal authoring, calendar, and target completion

<a id="gap-sg6"></a>
- [open obligation](gaps/numeric-and-temporal.md#gap-sg6)
<a id="gap-sg6-temporal"></a>
- [temporal record alias](gaps/numeric-and-temporal.md#gap-sg6-temporal)

<a id="sg23--the-temporal-extrema"></a>
### SG23 — the temporal extrema: operand gate, element type, and fold

<a id="gap-sg23"></a>
- [open obligation](gaps/numeric-and-temporal.md#gap-sg23)

<a id="sg21--the-declared-kindformat-split-across-temporal-carriers"></a>
### SG21 — the declared kind/format split across temporal carriers

<a id="gap-sg21"></a>
- [open obligation](gaps/numeric-and-temporal.md#gap-sg21)

### SG7 — String, pattern, and custom-field completion

<a id="gap-sg7"></a>
- [open obligation](gaps/strings-and-messages.md#gap-sg7)

### SG22 — `NumberOfDifferentValues` operand domain and its two homogeneity codes

<a id="gap-sg22"></a>
- [open obligation](gaps/numeric-and-temporal.md#gap-sg22)

### SG25 — the message parameter grammar and its terminal set

<a id="gap-sg25"></a>
- [open obligation](gaps/strings-and-messages.md#gap-sg25)

<a id="sg26--the-index-terminal-in-a-message-parameter"></a>
### SG26 — the `index(...)` terminal in a message parameter

<a id="gap-sg26"></a>
- [open obligation](gaps/strings-and-messages.md#gap-sg26)

### SG8 — Enumeration and value-list completion

<a id="gap-sg8"></a>
- [open obligation](gaps/strings-and-messages.md#gap-sg8)

### SG9 — paths, indices, and static legality completion

<a id="gap-sg9"></a>
- [open obligation](gaps/paths-and-groups.md#gap-sg9)

### SG10 — message construction and formal-output integration

<a id="gap-sg10"></a>
- [open obligation](gaps/strings-and-messages.md#gap-sg10)

### SG11 — custom-condition checked orchestration

<a id="gap-sg11"></a>
- [open obligation](gaps/strings-and-messages.md#gap-sg11)

### SG13 — group-list and group-count completion

<a id="gap-sg13"></a>
- [open obligation](gaps/paths-and-groups.md#gap-sg13)

<a id="sg17--having-filter-leaf-and-connective-completion"></a>
### SG17 — `Having`-filter leaf and connective completion

<a id="gap-sg17"></a>
- [open obligation](gaps/paths-and-groups.md#gap-sg17)

<a id="sg20--filter-reference-scope-and-iteration-gates"></a>
### SG20 — filter reference scope and iteration gates

<a id="gap-sg20"></a>
- [open obligation](gaps/paths-and-groups.md#gap-sg20)

<a id="sg19--repetition-reference-binding"></a>
### SG19 — repetition-reference binding and its two sources

<a id="gap-sg19"></a>
- [open obligation](gaps/paths-and-groups.md#gap-sg19)

<a id="sg15--bare-constant-target-families"></a>
### SG15 — bare-constant target families

<a id="gap-sg15"></a>
- [open obligation](gaps/targets-and-derivation.md#gap-sg15)

### SG14 — mandatory-information derivation

<a id="gap-sg14"></a>
- [open obligation](gaps/targets-and-derivation.md#gap-sg14)

### SG27 — the Number formal cascade's conversion route and its two unmodelled readings

<a id="gap-sg27"></a>
- [open obligation](gaps/numeric-and-temporal.md#gap-sg27)

### SG28 — refusal-class reachability and the shared denominator

<a id="gap-sg28"></a>
- [open obligation](gaps/targets-and-derivation.md#gap-sg28)

## Cross-family conformance gap

### SG12 — retained Kernel correspondence coverage

<a id="gap-sg12"></a>
- [open obligation](gaps/conformance-evidence.md#gap-sg12)
