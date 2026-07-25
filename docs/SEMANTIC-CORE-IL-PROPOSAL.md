# Proposal — a semantic core IL with proved lowering

> ## ⛔ CLOSED — read [§10](#10-closed--the-universal-shared-core-claim-is-rejected-2026-07-25) first
>
> **Status: closed 2026-07-25 with a negative architectural result.** The universal shared-core claim is **rejected**, Route B is **not** this project's derivation architecture, the `U1 → U2 → U6 → U5 → U4 → U3` sequence is **cancelled**, and `Semantics/CoreIL.lean` and `Proofs/CoreIL.lean` are **deleted**.
>
> **Sections 1–9 are preserved as the historical record and are not corrected in place beyond the inline markers below.** Several of their claims are withdrawn. Do not act on any of them without reading §10, which owns the verdict, the retained result, Route A as the incremental default, and the six conditions for reopening a checked-plan IL.
>
> What survives: `scanAtLeastOne_nil_members` in [`Proofs/ValueList.lean`](../A12Kernel/Proofs/ValueList.lean), plus [`LF73`](LEAN-FINDINGS.md), [`LF74`](LEAN-FINDINGS.md), [`LF76`](LEAN-FINDINGS.md).

---

## 1. Why this exists

Derivation is this project's animating principle. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#why-derive--the-animating-principle-and-its-assurance-classes) states it plainly: capturing the semantics is worthless if the knowledge cannot be pulled back out and used, so the theory exists to be extracted from rather than merely to be correct. The intended economics are to invest once in expressing the kernel's behaviour more precisely than prose, then derive each consumer at low marginal cost — in deliberate contrast to a peer clean-room interpreter, which must run its own campaign of kernel probes and reviews.

The recorded procedure does not yet deliver those economics, and it is worth being exact about why rather than treating it as a gap to be closed by effort.

A consumer today receives a **semantic shipment** ([`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#portable-shipment-contents)), whose eleven items are carefully specified — and whose load-bearing parts are prose. Item 3 requires "an original semantic decision procedure … written from the distilled behavior". Item 7 links to Lean theorems explicitly "rather than requiring the implementer to interpret Lean". Both are deliberate and defensible choices. Their consequence is that an implementer reimplements the union of 50 `Elaboration/` families' worth of behaviour from prose, and the resulting conformance is empirical over executed inputs.

That path has a defect class this repository produced **twice in one session**, both times in its own prose rather than in its Lean:

- [`LF72`](LEAN-FINDINGS.md#lf72--demoting-a-route-detail-does-not-make-it-removable-an-eager-decomposition-can-make-the-guard-carry-the-contract): after correctly demoting the `NotAll` prepass from the observable contract, `spec/06` went on to advise consuming the values side unconditionally. That advice would have broken **both** existing implementations, because both classify values-side poison eagerly and therefore depend on the guard.
- The parallel-iteration authoring rejections, stated as unconditional beside a computation-route finding when all of them sit in a rule-path-only check — recorded as the fifth instance of the shape named in [`SOURCES.md`](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit).

In both cases the mitigation was a prose warning, which is the same mechanism that failed. A path whose correctness depends on an implementer reading a warning is not a derivation path; it is a well-organized handover. That is the problem this proposal addresses.

## 2. Which consumers this serves, and which can inherit proof at all

The ten categories in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#general-consumer-task-categories) do not share one derivation story, and conflating them has obscured a strategically important fact.

| # | Category | Can it inherit proof? | Best mechanical route | Recorded status |
|---|---|---|---|---|
| 1 | **Execute** (independent interpreter, service) | **no** — evaluates continuously, produces no artifact a checker can validate | core IL + generated vectors | 2 kits, 1 archived Rust probe |
| 2 | **Translate** (JSON Schema importer, migration) | **yes** — output is a static artifact | certificate | not implemented |
| 3 | **Transform** (refactoring, simplification) | **yes** — the before/after pair is checkable | certificate over core terms | not implemented |
| 4 | **Compile** (target-code generator, plans) | **yes** — compiler correctness is provable | *this category is the generator* | not implemented |
| 5 | **Analyze** (SMT, equivalence, satisfiability) | **yes** | certificate | [proposal](SMT-SOLVER-SUPPORT-PROPOSAL.md) |
| 6 | **Verify** (invariants, preservation) | **yes**, by construction | certificate | not implemented |
| 7 | **Synthesize** (test data, repair, witnesses) | **yes** — a witness is checkable by definition | certificate | not implemented |
| 8 | **Qualify** (conformance, differential, mutation) | n/a — it *is* the checking role | bounded exhaustive generation | partly built |
| 9 | **Explain** (traces, change reports) | partial | generated traces rather than narrated ones | limited |
| 10 | **Govern** (manifests, gates) | n/a | metadata | partly built |

> ⛔ **Withdrawn (§10).** The table below has **six** `yes` rows, not eight, and a static artifact is not automatically proof-carrying: Translate needs source and target semantics plus a checked relation, Compile a compiler-correctness theorem, Synthesize validates a witness rather than generator completeness, and Explain needs a checked trace relation this proposal never supplies. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) is the more careful account.

**Eight of ten categories can carry genuine inherited assurance.** The independent interpreter — the most legible product, and the usual first choice — is one of the two that structurally cannot, because it produces no artifact to check. Any plan that proves the derivation thesis by shipping an interpreter first is proving it in the one place it cannot be proved.

One recorded defect found while assembling this table: the certificate row in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#why-derive--the-animating-principle-and-its-assurance-classes) omits **Translate**, although an importer emits a static artifact a Lean checker can validate. Not fixed here; fix it when that table is next edited.

## 3. Why a core IL rather than better tooling

The decisive distinction is not widely appreciated, and is worth stating plainly for readers who do not work in Lean.

Writing a program that reads an arbitrary Lean **function body** and emits equivalent Rust is not practical. That is exactly why the extraction row in the mechanism table is honestly marked unavailable, and no amount of tooling investment changes it. But writing a program that walks a Lean **data value** and prints it as Rust, Python, SMT-LIB, or JSON is trivial — it is pretty-printing, a few dozen lines per target.

So the leverage is not in tooling. It is in **where the semantics live.** Decision content held in `match` arms inside functions is invisible to any generator; the same content held as data is mechanically exportable, while Lean still proves theorems about the interpreter that consumes it. That single observation yields two routes.

### Route A — semantics as data

Move a decision table out of a function and into a value, with a proved-equivalent lookup:

```lean
-- today: the decision is inside the function, invisible to a generator
def conj : Verdict → Verdict → Verdict
  | .notFired, _ => .notFired
  | .unknown,  _ => .unknown
  …

-- exportable: the decision is a value; the function interprets it
def conjTable : List (Verdict × Verdict × Verdict) := …
def conj (a b : Verdict) : Verdict := lookup conjTable a b   -- proved equal to the above
```

Every existing law still holds, and a generator can emit `conjTable` to any target. This suits truth and polarity tables, operator dispatch, rounding stages, admission matrices, and enumeration mappings — a large share of §1–§8. It does **not** suit ordered, stateful, poison-propagating computation scheduling; tabulating that would relocate the prose rather than remove it.

### Route B — a core IL with a proved lowering (selected)

Instead of exporting each family's tables, reduce every family to one small shared core and **prove the reduction**. The two routes are complementary rather than alternatives: the model-zone calendar profile, for instance, is data and ships as a table even under Route B.

Route B is selected because it attacks the cost directly. Route A makes each family's content exportable but leaves the number of families untouched; Route B collapses the families.

For completeness, so the ground is covered: Lean can export its environment, but what that yields is Lean terms for proof checkers, not usable target code. There is no third mechanical option.

## 4. Design

A **semantic core IL** is the smallest set of constructs into which checked surface forms lower without losing a kernel-observable distinction. It is not a bytecode VM, not an optimization IR, and not a second evaluator. It is the object a consumer implements *instead of* A12.

**The test of the design is subtraction.** If the core still has a construct per surface operator, it is a renaming.

The public contract has three parts:

1. **Core syntax and semantics**, owned in Lean, small enough to reimplement in a page.
2. **A total lowering** from each checked family into the core. ⛔ **Not achieved (§10).** The implementation began *after* expansion, filtering, relevance and cell observation, so the promise in this line is the precise claim the experiment failed to meet.
3. **A preservation theorem** per family, equating core evaluation with that family's existing executable clause.

```lean
def lowerValueListQuantifier : ValueListQuantifier → CoreTerm

theorem lowerValueListQuantifier_preserves (quantifier : ValueListQuantifier)
    (fields values : List (ResolvedValueListSide kind)) :
    CoreTerm.eval fields values (lowerValueListQuantifier quantifier)
      = .verdict (quantifier.evalOrdered fields values)
```

### What the theorem buys, including the part that is easy to miss

Preservation is universal over all inputs, so every existing law transports by rewriting rather than reproof. Totality of the lowering — a plain function on the checked type, no `Option` or `Except` — makes "every admitted surface form is covered" a type-checked fact, which no prose handover can guarantee. Prose always has silent gaps and no mechanism to reveal which.

The part that is easy to miss: **the theorem is also the adequacy guard on the core's design.** A core that flattened computation poison into UNKNOWN, or let a read yield a `Value` instead of a cell observation, would make preservation *unprovable* — the proof gets stuck at exactly the erased distinction. So the question "is the core expressive enough?" is answered at proof time in this repository, rather than at integration time in someone else's Rust. It also gives the experiment an honest failure mode.

### Assurance boundary, stated exactly

The IL does **not** remove the unproved gap. It shrinks and concentrates it.

| Link | Covered by | Strength |
|---|---|---|
| checked surface → core | preservation theorem | proof, universal over inputs |
| core → existing family laws | rewriting from preservation | proof, no new effort |
| core in Lean → core in a target language | *nothing* | hand-written, reviewable, exhaustively testable because small |
| Lean → kernel | retained evidence | empirical, unchanged ceiling |

The third row is the honest claim: not "proved correct", but **"the unproved part is now small enough that exhaustive testing over a bounded domain is a complete argument"** — which it never is for a whole language. ⛔ **Overstated (§10):** it is a complete argument only for that exact finite bound, and the core as built carried unbounded rationals, strings, lists and slot indices, so no bounded suite universally establishes a hand-written target implementation of it. The fourth row is untouched by this proposal; [two links, one ceiling](PROJECT-DESIGN.md#why-derive--the-animating-principle-and-its-assurance-classes) still governs, and no amount of internal proof raises a derived product's claim above the retained evidence beneath it.

### What a consumer implements

Per target, a page rather than a language:

```rust
enum Core { Side(Side), Collect(Collect, Box<Core>),
            Fold(Fold, Box<Core>, Box<Core>), GuardPresent(Box<Core>, Box<Core>) }

fn eval(t: &Core, fields: &[Operand], values: &[Operand]) -> CoreValue { /* ~15 arms */ }
```

Plus generated core terms for the shipped fragment, plus **one conformance suite for the core** rather than one per family. That last consequence changes Qualify economics as much as Execute: today each family needs its own separating matrix downstream, whereas with a core the separating matrices stay upstream where the proofs are.

### The defect class this removes

`LF72` was mitigated with a prose warning telling implementers not to delete a load-bearing guard. Under a core IL that warning is unnecessary, because **the consumer never chooses the decomposition.** It implements the fold; the ordering is a structural property of the generated term. The defect class behind both of this session's authored errors — a statement true about the engine, misread as licence for an implementation — is structurally absent, because prose is not in the path.

### Design constraints inherited from the representation invariants

The core is worthless if it erases what `CLAUDE.md` requires preserved. These are acceptance constraints, not guidance:

- a read yields a **cell observation**, never a `Value`, so absence, present-empty, and formal invalidity survive to an explicit classification step;
- computation poison, validation UNKNOWN, and structural failure remain **three** channels;
- arithmetic carries an explicit rounding stage, making the exact-decimal invariant a syntactic property of core terms rather than a warning;
- the ordered scan carries the captured-outer/candidate-inner environment split.

### Why the core precedes the choice of first consumer

The core is the shared substrate for all eight proof-carrying categories, not an Execute optimization. Emitting SMT-LIB from a small core is one translation to get right instead of one per operator family; a refactoring tool checks equivalence on core terms; Compile *is* the generator; Analyze, Verify, and Synthesize all want the same small object. Building it per consumer is the path to three mutually incompatible semantics — the outcome [`SMT-SOLVER-SUPPORT-PROPOSAL.md`](SMT-SOLVER-SUPPORT-PROPOSAL.md) already warns about for its own boundary.

## 5. Scope

**Required for the first slice (E1).** Core constructs sufficient for the value-list quantifier family; a total lowering for its three operators; the preservation theorem; at least two existing laws re-derived through the core by rewriting; registration of the new theorem roots in the trust audit.

**Optional, deferred.** A second family lowering as a generality stressor (E2). Emission of core terms to any target language. Machine-readable core export. Any consumer-facing shipment change.

**Excluded.** No generator, schema, executable, registry, or protocol change. No `spec/` change — the core is a Lean representation decision, not a behavioural correction, so it creates **no ledger entry**. No claim that any consumer is derived until a target implementation exists and is qualified.

**Excluded by design, not by deferral.** SG4 computation scheduling. Ordered activation, poison propagation, and the locus-dependent clearing canonized in [`09-computations.md`](../spec/09-computations.md) do not lower into an expression core — that clearing keys on coordinates *coarser than the instance being cleared*, which an expression IL cannot express. Success on the validation surface must not create pressure to force computation execution into it; that needs either a separate small core or stays on the current path. The model-zone calendar profile is likewise data, not core constructs.

## 6. Experiments

**E1 — value-list core and preservation.** Lower the three quantifiers into a core fragment and prove preservation. Chosen because the family is closed, law-rich, and has a maintained separating matrix, so the experiment runs entirely against existing green material.

**E2 — generality stressor (next, only if E1 succeeded).** Lower the addressed numeric rule route, which brings ordered arithmetic, explicit rounding stages, and scoped iteration. Two independent families is this repository's own bar for generalizing a mechanism, so **the core may not be called shared until E2 passes.**

### Success criteria, fixed before the work

> ⛔ **All four passed, and all four were insufficient (§10).** They measured constructor count, theorem greenness, universality and transport-by-rewriting. None asked whether the core sat at the boundary §3 claimed, whether a helper duplicated an existing owner, or whether a cited theorem existed. Written by the agent later graded against them; see [`LF76`](LEAN-FINDINGS.md).

E1 succeeds only if all four hold:

1. preservation proved for all three operators, with no `sorry` and no new axiom;
2. the core is **strictly smaller** than the surface it replaces — fewer independent decision procedures, not merely different names;
3. **no existing separating conformance case requires a new core construct**;
4. at least two existing laws re-derived through the core by rewriting rather than reproof.

E1 **fails**, and is to be reported as a negative result with the experimental code removed, if the core needs one construct per surface operator — that is a renaming carrying extra proof obligations rather than a reduction.

## 7. Result — E1 succeeded *(as a family-local normalization result only — see §10)*

All four criteria met. Gates: `lake build` 471 jobs, trust audit **1327 theorem roots; 27614 declarations in 252 modules**, `lake test` 51/51, `checkReferenceProcess` 51/51.

**Criterion 1.** `lowerValueListQuantifier_preserves` (in the since-deleted `Proofs/CoreIL.lean`; recoverable at commit `f3c086a`) is proved for all three operators, universal over operand shapes. Eleven theorems total, zero `sorry`, and the trust audit's axiom check passes, so no escape hatch was used.

**Criterion 2 — the core is strictly smaller, and the prediction held.** The family carries two collection functions, **three** operator-specific fields scans, a presence predicate, and an empty-member guard. The core carries two collection policies, **two** folds, and one guard:

| Surface | Core |
|---|---|
| `AtLeastOne` scan | `findWitness .inside` |
| `NotAll` scan | `findWitness .outside` |
| `No` scan | `scanUntilMatch` |

Three scans collapse to two folds, with membership direction becoming a *parameter* rather than a procedure. The remaining split is semantically real — `scanUntilMatch` is cell-granular, unavailability-sensitive, and inverted, which is precisely the `No`-versus-`NotAll` asymmetry `spec/06` §B.3 already documents. This was the prediction recorded before the work, and it is what happened.

**Criterion 3.** No construct was added to accommodate a case. More strongly: because preservation is universal, *every* existing separating case is covered by the theorem rather than by enumeration.

**Criterion 4.** `core_valueListNo_unknownMember_before_fields` and `core_valueListNo_filtered_nonmatch` are each discharged by a single `rw` citing the family law they inherit from, adding no reasoning of their own.

### Findings the experiment produced

**A second short-circuit, and this one is genuinely redundant.** `AtLeastOne`'s empty-member guard was proved unnecessary: with no members the shared fold already exhausts to non-firing, so the guard is an optimization. That is the *opposite* of `NotAll`'s presence guard, which `LF72` establishes as load-bearing. The family therefore carries two structurally similar short-circuits with opposite status, and **only proof distinguishes them** — recorded as [`LF73`](LEAN-FINDINGS.md). Under prose handover both look like the same kind of implementation note.

**Incidental variation surfaced as proof friction.** The family's two firing scans order their polarity disjunction differently, so the shared core formula matches each only up to commutativity. Harmless, but it is evidence the surface carried variation with no semantic content — exactly what a core normalizes away.

### Costs incurred, recorded rather than absorbed

**Encapsulation.** Seven collection and scan helpers in `Semantics/ValueList.lean` were `private`; the preservation proof must state induction lemmas about them from its own module, so they are now exposed, with a comment recording why. No semantics changed and `evalOrdered` remains the only intended entry, but the family's public surface is genuinely wider than before. Any future family lowered into the core should expect the same pressure; if it recurs often, the right answer is a reviewed convention rather than repeated ad-hoc exposure.

**Line budget exceeded.** 327 new nonblank Lean lines against a Tier 1 target of 250 — 162 in `Semantics/CoreIL.lean` and 165 in `Proofs/CoreIL.lean`, of which 51 are documentation. Already split by semantic responsibility (core and lowering; proofs and transport), so the target's decomposition signal has been acted on. The residue is proof content required by the criteria: eleven theorems at roughly thirteen lines each. Reaching 250 would mean dropping supporting agreements the preservation proof needs, or the transports criterion 4 requires. Recorded as an overage rather than resolved by compressing readable code, which the rule explicitly disallows.

## 7a. Result — E2 partially succeeded, with one real negative

**Verdict: the parameter discipline generalized; the environment did not. The core may not yet be called shared.**

Gates after E2: `lake build` 471 jobs, trust audit **1330 theorem roots; 27694 declarations in 252 modules**, `lake test` 51/51, `checkReferenceProcess` 51/51.

**Scope actually covered, stated before the findings.** E2 as specified was the *addressed numeric rule route* — ordered arithmetic, explicit rounding stages, and scoped iteration. What was run covers a **fragment**: three existing family primitives lowered and preserved (`NumericComparisonOp.eval`, `NumericArithmeticOp.eval` under `roundDecimal`, and unknown domination through a lowered comparison). **Scoped iteration was not lowered and remains untested.** E2 is therefore partially discharged, and the shared-substrate claim stays open.

**What generalized — the central discipline held.** The numeric route added five constructs, and in every one the operator enters as **term data** rather than as a construct: `NumericArithmeticOp`, `DecimalRoundingMode`, `RoundingPlaces`, and `NumericComparisonOp` are all parameters. Six comparison operators and three arithmetic operators cost zero constructs, exactly as membership direction did in E1. The subtraction test therefore passes on a second, deliberately different family — which is the one thing E2 most needed to establish.

The rounding stage also became syntactic as intended: `numRound` carries mode and places in the term, so the exact-decimal invariant is a property of core terms rather than a convention a reader must honour.

**The negative — E1's environment was family-specific and did not survive contact.** `eval` took two positional operand *streams*. The numeric fragment reads already-*classified* numeric operands, which are neither stream, so `eval` grew a third explicit parameter and now carries a union of per-family environments rather than an abstraction over them. The same pressure appeared in the result domain: `CoreValue` gained `numeric` and `amount` alongside `stream`, `members`, `poisoned`, and `verdict`.

That is a genuine design defect, not a cosmetic one. A core whose environment and result type accumulate one constructor per family scales exactly as badly as the prose it replaces. **The fix is the `read`-against-a-document design this proposal's §4 sketch originally had and E1 did not need** — a single addressed read yielding a cell observation, with per-family classification expressed as core terms rather than as environment slots. Until that lands, "shared core" overstates what exists: what exists is one core syntax with two families' environments bolted alongside each other.

**Cost.** The two modules are now 394 nonblank Lean lines (203 semantics, 191 proofs), against the 250 Tier 1 target already exceeded by E1. E2's own increment was 67 lines for five constructs and three theorems, which is proportionate; the aggregate overage is recorded rather than resolved by compression, and the environment redesign above is the change that would justify revisiting the file boundary.

**What E2 changes about sequencing.** Fixing the environment is now a precondition for a third family rather than an optional refinement, because each family added before the fix widens the union that has to be unpicked. The next unit on this track is therefore the addressed `read`, not a third lowering.

## 7b. Result — the addressed read closed E2's negative ⛔ *REJECTED (§10)*

> ⛔ **This section's conclusion is withdrawn.** The addressed read did not abstract over the per-family union; it relocated it into an untyped `List CoreValue` indexed by a bare `Nat`, so every family still contributed its own layout and builder while `read` could return any constructor. The *signature* stabilized; the semantic ABI stayed open. The promised read — cell observations against a document, with structural failure distinct from semantic UNKNOWN — was never built, and neither was the `WellFormed` boundary [`ARCHITECTURE.md`](ARCHITECTURE.md) requires of an extrinsic AST.

E2's negative was that `eval` carried a union of per-family environments. That is fixed. Gates: `lake build` 471 jobs, trust audit **1330 theorem roots; 27677 declarations in 252 modules**, `lake test` 51/51, `checkReferenceProcess` 51/51 — the same theorem count, so nothing was traded away.

**The change.** `eval` went from three positional per-family arguments to one `CoreEnv`, a single addressed slot space read by a single `read` node. `CoreSide` and `numSlot` both disappeared into `read`, so the core lost a construct while gaining a family: **nine constructs became eight.** Slot layouts are named (`ofValueList`, `ofNumericPair`, `empty`) rather than left as bare indices at call sites, so the layout a lowering assumes is stated once and pinned by that family's preservation theorem.

**The test that it is an abstraction rather than a rename** is what happened to the theorem statements. Before, the numeric preservation theorems had to carry `(fields values : List (ResolvedValueListSide kind))` binders they never used, because `eval` demanded them. Those binders are now gone, and every preservation theorem in both families has the same shape:

```lean
CoreTerm.eval <env> (lower … ) = <family result>
```

A third family contributes a lowering and a layout. It does not change `eval`'s signature, and it cannot force unrelated families' theorems to mention its state. That was the property E2 showed was missing.

**Residual, stated rather than glossed.** `CoreValue` still carries six constructors — `stream`, `members`, `poisoned`, `verdict`, `numeric`, `amount` — and the first two are value-list-shaped while the last two are numeric-shaped. The environment no longer grows per family; the *result domain* still might. The honest position is that this is bounded by result domains rather than by families — a third family with an ordered scan should reuse `stream` and `members` rather than add its own — but that is a prediction, and only a third family can test it. It is recorded as the next open question rather than claimed as settled.

**Consequence for the shared-substrate claim.** Two families now lower into one core with a stable interface, which was the bar. What remains untested from E2's original specification is **scoped iteration**, so the claim is still narrower than "the core is shared": it is "two families of expression-shaped semantics share one core, and the interface no longer grows with them."

## 8. Recommendations recorded but not selected here

Out of scope for this proposal, recorded so a later reader need not rediscover them.

- **Ship a proof-carrying consumer before the interpreter.** Synthesize is cheapest — a witness generator whose output a small Lean checker validates. It would demonstrate the derivation thesis with genuine inherited proof at spike scale, which the interpreter structurally cannot do however well the IL works.
- **Adopt Route A incrementally rather than as a project.** When a future capsule lands a decision table, record it as data with a proved-equivalent lookup instead of burying it in `match` arms. No generator, no new infrastructure — just stop putting new semantics where a generator cannot reach. After two or three capsules there is enough tabulated material to judge whether a generator is worth building, on evidence rather than on a bet.
- **The core has a second payoff that is not derivation economics.** A reduced construct set with a proved lowering is itself a *simplified language variant* — a deliverable for consumers who cannot afford the full surface — and the preservation theorem is what makes it a proved image rather than a summary. Recorded as a cross-category use case in [`USE-CASES.md`](USE-CASES.md#cross-category-use-case-a-derived-simplified-language-variant). It changes nothing here: no new scope, no process change, and the variant's reach is a consequence of how far lowering has progressed. It does supply a concrete candidate for the consumer probe, and it means the core's value does not rest on the derivation argument alone.
- ⛔ **Withdrawn (§10).** **Fix the `Translate` omission** in the certificate row of [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#why-derive--the-animating-principle-and-its-assurance-classes) when that table is next edited.

## 9. What would falsify the approach

> ⛔ **Two of these fired (§10).** *"E2 needs constructs that do not generalize"* — the numeric constructs were unusable by the value-list family, which this section names as the E2 falsifier. And the boundary defect means the per-family cost was never measured against the real elaboration surface. Recorded here because predeclaring falsifiers only works if they are checked afterwards, which is what an external review had to do.

Stated so the proposal can be abandoned on evidence rather than defended.

- **E2 needs constructs that do not generalize.** If the addressed numeric rule route forces constructs the value-list family cannot use, the core is a per-family encoding and the shared-substrate argument fails.
- **The per-family cost does not amortize.** One lowering plus one theorem per family, eventually of the order of the 50 elaborators. This is affordable only because it composes with the capsule discipline — each future capsule lands its clause, its laws, *and* its lowering together. A stop-and-convert migration of the back catalogue is explicitly not proposed, and if the only way to finish were such a migration, the approach has failed at the intended scale.
- **A consumer needs a distinction the core dropped.** Preservation guards against losing kernel-observable distinctions, not against pitching the core below what a *task* needs. The consumer-adequacy rule still applies, and the first real target implementation is the test.

## 10. Closed — the universal shared-core claim is rejected, 2026-07-25

**Status: closed with a negative architectural result. Route B is not the project's derivation architecture. The `U1 → U2 → U6 → U5 → U4 → U3` sequence is cancelled and the Lean estate is retired.** This is a successful experiment reaching a negative conclusion, not a failed undertaking — the criteria did their job once they were pointed at the right question.

### What the experiments actually established

| | claim | verdict |
|---|---|---|
| E1 | three quantifier scans reduce to two folds; preservation provable over resolved operands | **holds**, as a family-local normalization result |
| E1 | `AtLeastOne`'s empty-member guard is redundant, `NotAll`'s is load-bearing | **holds**, retained as `scanAtLeastOne_nil_members` and [`LF73`](LEAN-FINDINGS.md) |
| E2 | the numeric route needs no constructs of a new character | **holds only at a post-classification boundary** |
| §7b | the addressed read closed E2's negative | **rejected** — see below |
| §1–§4 | the core is the shared substrate replacing prose handover for ~50 families | **rejected** |

### Why the substrate claim fails

**The boundary is not the one the proposal promised.** §3 promises lowering "from each checked family"; the implementation begins after expansion, filtering, relevance and cell observation — stated in `ValueList.lean`'s own module docstring, and in `ofNumericPair`'s "two already-classified comparison operands". A consumer would still implement model checking, addressing, topology, filtering, classification and scope: precisely the elaboration decisions §1 says the core eliminates. E1 is a valuable *post-resolution normalization*, not checked-surface-to-core derivation.

**§7b did not close E2's negative.** The promised fix was a read yielding cell observations against a document. What landed was a positional `Nat` index into an untyped slot list returning any `CoreValue`. The per-family union was moved inside an untyped array rather than eliminated; every family still contributed its own layout and builder. The function signature stabilized; the semantic ABI did not.

**Three of the four core helpers re-expressed existing family algorithms.** `runScanUntilMatch`, `collectPresentOnly` and `collectPoisoning` each carry an agreement theorem against `scanValueListNoFields`, `collectAtLeastOneValueListMembers` and `collectPoisoningValueListMembers` respectively — the last by explicit result correspondence rather than literal equality, since the result domains differ. Agreement alone is not redundancy: every legitimate lowering should have an equivalence theorem. Redundancy follows here from the combination of an identical post-resolution boundary, mirrored recursion and decisions, no independent consumer, and no unique invariant enforced by the second implementation. At that boundary and with no consumer, the agreement theorems show these helpers re-express algorithms the family already owns rather than supplying an independently used abstraction.

**`runFindWitness` was the sole genuine abstraction E1 found:** the two firing scans share the same recursion and `Verdict` domain, with membership direction as the only semantic parameter. They do not compute the same result on the same inputs — they instantiate the same mechanism under opposite predicates. It was retired anyway, because retaining it beside both established scans was net duplication; the relationship is held by [`LF73`](LEAN-FINDINGS.md).

**Two defects the criteria never tested.** A docstring cited `lowerValueListQuantifier_wellFormed`, a theorem that was never written — no `WellFormed` boundary existed at all, though [`ARCHITECTURE.md`](ARCHITECTURE.md) requires one for an extrinsic AST. And `.poisoned` carried two meanings: `collectPoisoning` returned it for a *semantic* poison while `eval` returned it for a *malformed shape*, so `fold`'s `.poisoned → .verdict .unknown` let an out-of-range slot read masquerade as semantic UNKNOWN, violating "structural failure outside semantic UNKNOWN".

### Why the criteria passed a proposal this far off its own boundary

The four criteria in §6 measured constructor count, theorem greenness, universality, and transport-by-rewriting. Every one passed. None asked whether the core sat at the boundary §3 claimed, whether a helper duplicated an existing owner, or whether a cited theorem existed. **The criteria were written by the same agent that then graded against them**, so they converged on that agent's framing; a checklist run by the author confirms the author. Each defect was checkable against text in the same repository — often the same file. The durable lesson is [`LF76`](LEAN-FINDINGS.md), and the one mechanizable part is now a gate: `check-lean-trust.sh` rejects a backticked citation with no referent.

### What is retained

`scanAtLeastOne_nil_members` in [`Proofs/ValueList.lean`](../A12Kernel/Proofs/ValueList.lean) — the one new family theorem worth keeping in Lean source. Everything else lives in this record, [`LF73`](LEAN-FINDINGS.md), [`LF74`](LEAN-FINDINGS.md), [`LF76`](LEAN-FINDINGS.md), and Git. `Semantics/CoreIL.lean` and `Proofs/CoreIL.lean` are deleted; the six `ValueList.lean` helpers de-privatized for them are private again.

### Route A is the incremental default

Use the normalized boundaries that already exist — `ConditionTree`, `AuthoredNumericExpr → LoweredNumericExpr`, operator enums and decision tables, checked source and address plans, resolved value-list structures. When a future capsule adds a genuine decision table, keep it exportable and prove its evaluator agreement. Do not build a universal generator or schema.

### Reopening trigger for a checked-plan IL

A checked-plan IL may eventually be right, and it would **not** pull model checking or topology into the IL evaluator: the shape is `surface model → existing checked elaboration → checked CoreProgram referencing canonical document/SG2 reads → small evaluator`, with model checking staying in elaboration. Reconsider only when **all** of these hold:

1. A named consumer — SMT, refactoring, compilation, or a simplified-language shipment — cannot be closed from the existing normalized representations without duplicating semantics.
2. The precise consumer artifact and assurance claim are fixed.
3. SG2 supplies its stable checked document and addressed-stream boundary.
4. An inventory identifies which existing ASTs are reused, consolidated, or replaced.
5. One end-to-end preservation theorem is stated before implementation.
6. The user explicitly approves the resulting infrastructure unit.

### Corrections to this document's own claims

- §2's "**eight of ten** categories can carry genuine inherited assurance" is **not supported by its table**, which has six `yes`, one `no`, one `partial`, and two `n/a`. Nor is a static artifact automatically proof-carrying: Translate needs source and target semantics plus a checked relation, Compile needs a compiler-correctness theorem, Synthesize validates a witness rather than generator completeness, and Explain needs a checked trace relation the extensional theorem does not supply. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) lists certificate checking for Analyze, Transform, Verify and Synthesize only, and is the more careful account.
- The §8 recommendation to "fix the `Translate` omission" in that table is **withdrawn**: its certificate contract would have to be specified first.
- §3's claim that bounded exhaustive testing becomes "a complete argument" holds only for that exact finite bound. The core carried unbounded rationals, strings, lists and slot indices.
