# Archived A12 Lean computation execution semantics decision

## Status

Accepted on 2026-07-22 as the binding architectural decision for the future computation-scheduling and document-transition boundary of the A12 Lean mechanized semantics, then archived after its live obligations were promoted to their permanent owners.

Kernel-observable behavior is owned by [`spec/01`](../../spec/01-data-model.md) and [`spec/09`](../../spec/09-computations.md). The binding Lean representation constraints are owned by [`ARCHITECTURE.md`](../ARCHITECTURE.md#whole-model-computation-execution-keeps-definition-activation-result-application-and-validation-separate), and the open prerequisites, source-audit categories, and completion gate are owned by [`SG4`](../SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition). This archived record preserves the accepted rationale, rejected alternatives, detailed audit questions, and adoption point; it is not a live implementation-status or sequencing owner.

Adoption does not authorize immediate implementation, change the currently active semantic unit, or introduce a dependency, harness, protocol, or public product. At adoption, SG4 remains unselected: general repeatable addressing and checked-document construction are still open, the complete processing-context boundary is not yet represented, and the bounded source-audit gate in §17 is not closed.

## Decision summary

Adopt an A12-specific operational semantics for computation execution with the following six distinct layers:

1. A checked whole-model computation plan containing immutable declarations, resolved targets and scopes, dependency and schedule facts, and generated-validation ownership.
2. A checked immutable input document derived coherently from the model.
3. An explicit processing context representing every semantically relevant input supplied through the Kernel's `DocumentProcessingConfig` rather than consulting ambient host state.
4. An internal computation activation containing the formal-operand-validation snapshot, stripped input view, pending and completed computation instances, rich typed outcome overlay, and semantic execution trace.
5. A completed rich result with a Kernel-compatible observable projection: successful non-clearing computations, their changed subset, erroneous computed instances, cleared previously filled instances, formal operand errors, and the derived error predicate.
6. Placement-sensitive application to a caller-supplied compatible document, followed separately by validation when the caller chooses the usual `compute → apply → validate` composition.

Define both an executable scheduler and an independently meaningful operational relation or trace semantics. Prove the executable scheduler sound and complete against that account and deterministic for a fixed checked model, document, processing context, and kernel-defined schedule.

Do not model computation as successive mutations of the input document. Do not expose internal trace or list order as public result order without separate Kernel evidence. Do not adopt fUML or PSSM runtime classes, event queues, nondeterministic scheduling, or a generic state-machine framework. The relevant lesson from fUML/PSSM is the strict separation of immutable semantic definition, mutable execution activation, stable result, and observable trace.

## 1. Context and goal

The project’s primary goal is eventual complete semantic conformance with A12 kernel 30.8.1 across the observable validation-and-computation language and required static legality. Lean serves as the versioned executable semantics-of-record and proof environment. The real kernel remains the behavioral authority; Lean proofs establish consequences of the chosen formal account, while retained differentials and source-grounded observations establish empirical correspondence.

The current theory has already closed many local computation mechanisms:

- phase-sensitive cell observation;
- clean emptiness versus formal invalidity;
- read-driven computation poison;
- ordered condition evaluation and first-match alternative selection;
- String and Number expression, store, target, delta, and exact single-target application boundaries;
- one explicit String producer-to-consumer dependency edge;
- checked numeric and String computation fragments;
- common preconditions and generated-validation fragments;
- placement-sensitive absent, present-empty, and present-value target states.

These are intentionally narrow capsules. They do not yet define the general dependency graph, scheduler, working computation view, multi-target rich result, repeatable target instances, missing-ancestor creation, or complete `compute → apply → validate` composition.

The open scheduler boundary is unusually high-risk because it composes several distinctions that are already known to be observable:

- calculated inputs are stripped before the calculation run, so a not-yet-computed target reads as empty rather than exposing stale stored data;
- a completed clean no-value result cascades as empty, while a completed invalid result poisons a later computation only when that target is actually read;
- read order matters because short-circuiting and stop-at-deciding-cell scans can leave an invalid cell unread;
- one computation table selects the first holding alternative, while several separate computations targeting the same field use a different first-non-empty rule in document order;
- accepted values, clean no-value, target rejection, calculation-local invalidity, and inherited poison have different downstream meanings even when their change delta or applied cell state is equal;
- `compute` returns a stable result and does not mutate a V2 document;
- that result exposes several overlapping public projections rather than one three-way result partition: all successful non-clearing computed instances, their changed subset, erroneous computed instances, cleared previously filled instances, and formal operand errors;
- `applyTo(DocumentV2)` is a later placement-sensitive operation over a caller-supplied destination document and returns a new document;
- `validate` is separate and does not compute first;
- generated computation validation retains all holding alternatives rather than reusing computation’s first-match selector.

The architecture must preserve these distinctions through the whole execution path without inventing a universal state representation too early.

## 2. Why fUML and PSSM are relevant

[fUML](https://www.omg.org/spec/FUML/1.5) defines an executable UML subset and an abstract execution model. [PSSM](https://www.omg.org/spec/PSSM/1.0) extends that foundation with precise operational semantics for UML behavior state machines. Their domain is different from A12, but several architectural lessons transfer.

### 2.1 Transferable lessons

The useful transferable lessons are:

- Separate the immutable model definition from each runtime execution instance.
- Represent runtime state explicitly rather than hiding it in ambient mutation.
- Distinguish transient execution state from stable externally meaningful configurations or results.
- Resolve global selection conflicts at the semantic owner rather than allowing local components to race or overwrite one another accidentally.
- State operational behavior as a relation or trace model when individual steps carry causal information.
- Prove a deterministic implementation against the semantic relation rather than treating one implementation order as self-justifying.
- Define the observable trace contract explicitly; do not confuse a normative semantic trace with an implementation log.
- Pin the exact language and runtime version and state supported fragments honestly.

### 2.2 Lessons that do not transfer

PSSM permits nondeterministic legal executions and partially ordered behavior across orthogonal regions. A12 kernel 30.8.1 instead exposes substantial deterministic order: declaration order, alternative order, operand order, repetition order, scan order, poison encounter, computation order, and target precedence. Therefore the A12 semantics should not become a set of permitted schedules merely because PSSM requires that representation.

PSSM’s semantic visitors, loci, object activations, event pools, event accepters, completion events, and run-to-completion machinery are implementation concepts for its domain. They are not appropriate A12 abstractions and must not be imported into this project.

The transfer is therefore architectural, not terminological or technical: A12 needs a checked plan, an execution activation, an operational account, and a stable outcome boundary, but it does not need a state-machine runtime.

## 3. Required semantic layering

The required semantic flow is:

```text
expanded A12 model
        │
        ▼
checked whole model and computation plan
        │
        ├──────────────┐
        │              │
        ▼              ▼
checked input       processing context
document            locale, date, custom semantics
        │              │
        └──────┬───────┘
               ▼
      computation activation
      - immutable input
      - stripped computed-field view
      - pending/completed instances
      - typed outcome overlay
      - semantic trace
               │
               ▼
       completed rich result
       + Kernel-compatible projections
               │
               ▼
     apply to caller-supplied
       compatible document
               │
               ▼
        updated document
               │
               ▼
       full/partial validation
```

No arrow in this diagram may be collapsed merely for implementation convenience. In particular, the computation activation is not an incrementally mutated `Document`, and application is not part of expression evaluation or dependency scheduling. The ordinary destination for application is the document used for computation, but the current V2 Kernel API accepts the destination document as a separate argument; the semantic result must therefore not be structurally usable only with one captured source object.

## 4. Static checked computation plan

### 4.1 Responsibility

The static plan owns facts determined from the expanded model before document evaluation:

- stable identities for computations, alternatives, generated validations, and computed targets;
- exact authored order and any separately derived schedule order;
- resolved target field and target kind;
- resolved target repetition scope and computation-instance construction rule;
- checked common and alternative preconditions;
- checked operation expressions;
- every referenced field and computed-field dependency;
- same-target computation grouping and its source-defined precedence rule;
- target policy, result shape, and static assignment legality;
- generated-validation ownership and its complete all-alternatives lowering;
- direct self-reference rejection;
- indirect cycle disposition according to kernel 30.8.1;
- a proof or checked certificate that the schedule is coherent with the admitted dependency account.

It does not own:

- a document;
- prior target values;
- computed outcomes;
- runtime repetition instances;
- poison state;
- change deltas;
- custom callback results;
- resolved dates, locale-dependent outputs, custom semantic responses, or other processing-context values.

### 4.2 Proposed shape

The exact names are illustrative. The public contract is the separation of responsibilities, not these field names.

```lean
abbrev ComputationId := Nat
abbrev ComputationInstanceId := Nat

structure CheckedComputationPlan where
  modelIdentity : ModelIdentity
  computations : List CheckedComputation
  schedule : List ComputationId
  -- checked target, scope, dependency, cycle, and generated-rule facts
```

The plan should be a separate finite aggregate rather than an expansion of the current narrow field-resolution model. Existing checked leaf and expression artifacts should be embedded or referenced; their logic must not be cloned into a whole-model parser or second expression tree.

### 4.3 Global selection ownership

The plan must keep three order mechanisms separate:

1. Alternative selection inside one computation table: first holding alternative wins; selected-operation no-value does not reopen the suffix.
2. Several computation declarations targeting the same field: the source-defined first-non-empty rule in document order.
3. Dependency scheduling between computed fields: the source-defined order that ensures later consumers observe the correct producer state.

Application must not resolve any of these mechanisms by receiving duplicate target writes and folding them in list order. Computation execution must produce one resolved effective result per target cell before application.

## 5. Checked document boundary

The raw `Document` remains the external in-memory document representation. It preserves instantiated rows independently of raw cells and distinguishes physical absence from present-empty placement.

A model-owned checked document route must derive coherent semantic views from that raw document. It may be represented as a wrapper or as checked construction functions, but it must establish:

- every raw placement belongs to the model at the claimed field kind and repetition path;
- instantiated row identities and order are coherent with model ancestry and repeatability;
- present-empty placement is retained independently of evaluation emptiness;
- formal checking and phase observation use the same model-owned cell classification;
- custom field validation is sampled according to its exact call contract and reused coherently;
- wrong IDs, wrong kinds, wrong scopes, malformed paths, and impossible placements fail closed;
- generated formal findings are available to both validation and computation observation without conflating validation-only requiredness with computation poison.

The computation scheduler consumes this checked boundary. It must not accept a collection of independently forged field readers and assume they describe one document.

## 6. Explicit processing context

The current V2 computation entry point receives `DocumentProcessingConfig`. For full 30.8.1 semantic compatibility, Lean's `World` cannot mean only a clock or an unspecified bag of host oracles. It must explicitly account for every configuration input that can change an observable result:

- the locale used for formal error messages;
- custom-condition semantics supplied by the custom condition factory;
- custom-field parsing and validation semantics supplied by the custom field type factory;
- deprecated additional information while compatibility with that 30.8.1 surface is claimed;
- the date used by `Today`, including the test override and the resolved actual date when no override is supplied.

The Lean core should represent their semantic effects, not Java factory objects. An illustrative boundary is:

```lean
structure ProcessingContext where
  errorLocale : ErrorLocale
  currentDate : PlainDate
  customConditions : CustomConditionSemantics
  customFieldTypes : CustomFieldTypeSemantics
  legacyAdditionalInformation : LegacyCustomContext
```

The exact types remain family-owned. A custom capability may be represented by a checked finite interpretation, a total pure callback interface, or an explicit oracle response map, provided its input and output contract is stated and no ambient mutable registry is consulted by the executable semantics.

Determinism is claimed only for a fixed processing context and under any explicit purity or extensionality assumptions placed on custom semantics. Resolving the actual current date belongs at the host adapter boundary; the semantic computation receives the resolved date. If a capability is unsupported by an admitted interpreter shipment, preparation must reject it or return an explicit unsupported result rather than silently substitute built-in behavior.

`World` may remain the Lean type name, but its compatibility contract must be this complete processing context for the fragment claimed, not merely time.

## 7. Computation activation

### 7.1 Responsibility

One call to `compute` creates a transient computation activation. This is the A12 analogue of a runtime execution instance: it refers to the immutable checked plan and checked input but owns the evolving internal scheduling state.

Conceptually:

```lean
structure ComputeActivation where
  input : CheckedDocument
  formalErrorsInOperands : List FormalMessage
  pending : List ComputationInstanceId
  completed : OutcomeOverlay
  trace : ComputeTrace
```

The actual representation may carry a separate `WellFormed` proposition or checked wrapper rather than proof fields directly. The important requirement is that the invariants be stated and preserved.

### 7.2 Input document remains immutable

The activation must retain the original checked input document unchanged. Computation does not successively apply target writes to that document.

The semantic decomposition corresponding to the current V2 call surface is:

```lean
def compute : CheckedComputationPlan → ProcessingContext → CheckedDocument → ComputeResult
def apply : ComputeResult → CompatibleDocument → Document
def validateFull : CheckedModel → ProcessingContext → CheckedDocument → List Message
```

The exact argument order and checked wrappers are illustrative. The required observable facts are that V2 computation returns a stable result, V2 application receives its destination document explicitly and returns a new document, and validation is a separate call. The ordinary composition applies the result to its source document, but the result must not capture that source so tightly that application to another model-compatible destination is impossible.

### 7.3 Formal operand validation before scheduling

Before computations run, the V2 contract formally validates non-computed fields that are operands of computations and retains the resulting messages in `formalErrorsInOperands`. Invalid values are reported; empty required fields are not reported as omission errors for this computation prepass; empty or non-unique index fields are reported. Computation processing continues despite collected operand errors, while computations affected by invalid operands fail to produce a value according to the exact dependency and cascade rules.

This establishes two independent facts that must not be collapsed:

- formal operand error collection is an eager result-building phase over the source-defined operand set;
- invalidity affects a computation only through the source-defined dependency, scheduling, and evaluation semantics, not merely because a message exists somewhere in the result.

Consequently, an operand error can be present in the public result even when an unrelated or semantically unblocked computation succeeds. Conversely, the existence of `formalErrorsInOperands` cannot be implemented as a global abort or as an eager poison value injected into every computation.

The checked plan owns the operand set; the checked document and processing context own coherent formal checking; the activation retains the resulting snapshot unchanged while scheduling. The exact treatment of guarded, filtered, repeatable, index, and indirect operands remains part of the bounded source audit.

### 7.4 Stripped input and completed-outcome overlay

The activation’s computation read must obey this logical rule:

```text
ordinary input field
    → read from the checked input document

computed field whose effective result is complete
    → read the dependency projection of that completed result

computed field not yet complete
    → read clean empty, regardless of stale stored input
```

The stripped view and the completed overlay are different mechanisms:

- pre-stripping prevents stale calculated values from being consumed before their current result exists;
- the overlay exposes accepted stored form, clean emptiness, or poison from a completed producer;
- poison is thrown only when that overlay entry is reached by a consuming read;
- short-circuited or unvisited entries do not poison merely because they exist in the overlay.

### 7.5 Typed outcome overlay

The current semantic families do not yet justify one universal dependency-cell representation. String can project an outcome to a synthetic checked cell with an exact cause in its admitted fragment. Number currently exposes a cause-free dependency observation and deliberately does not invent a `FormalCause`.

The general activation must therefore preserve target-family meaning rather than forcing every outcome through `CheckedCell`. A plausible outer shape is a closed sum of established family outcomes:

```lean
inductive ResolvedTargetOutcome where
  | number (outcome : NumericTargetOutcome)
  | string (outcome : StringTargetOutcome)
  | date (outcome : DateTargetOutcome)
  | other (...)
```

Each family supplies its own dependency projection into the expression or condition consumer that reads it. A shared poison carrier may be extracted only after source evidence establishes it and at least two completed consumers demonstrate the same meaning and result domain.

### 7.6 Activation invariants

At minimum, a well-formed activation must guarantee:

- the plan and checked input have the same model identity;
- pending and completed computation instances are disjoint;
- every instance belongs to the checked plan and has a valid target address;
- every completed overlay entry came from an admitted target computation;
- no unresolved calculated field exposes its stale stored input;
- formal operand messages are the exact initial prepass projection and remain separate from computed-target errors;
- completed results preserve all information required by downstream reads, delta projection, application, findings, and explanation;
- a result is not projected to a lossy delta or applied cell state before dependency consumers have finished;
- any same-target selection has one explicit owner and is not repeated by application;
- the trace corresponds to the activation transition that produced it.

## 8. Rich result and Kernel-compatible public projections

The project has already discovered that one computation result needs several views. The general scheduler must preserve these boundaries, and its public compatibility projection must match the actual 30.8.1 V2 API rather than reducing the result to an address/outcome list or a three-way `VALUE | CLEARED | ERRORED` partition.

### 8.1 Rich semantic target outcome

The internal target outcome retains the distinctions needed by later computations and target semantics. Depending on the target family, this includes:

- clean no-result;
- accepted exact stored value;
- target rejection with attempted stored value and cause;
- calculation-local invalidity without an attempted stored value;
- inherited poison from a reached dependency.

This is the scheduler and dependency domain.

### 8.2 Kernel-facing computed instance

A Kernel-facing computed field instance carries at least:

- its document pointer;
- its typed V2 value, which may be absent;
- its string representation when available;
- an optional formal error message for an invalid computed value.

The Lean core may retain richer typed family outcomes, but it must be possible to project the admitted fragment to this observable instance shape without inventing or losing pointer, value, or error distinctions.

### 8.3 Kernel-compatible result view

The V2 `IDocumentComputationResult` contract exposes these projections:

1. `computedFieldInstancesWithoutErrors`: every non-clearing field instance computed successfully, including a successful value equal to the source document's value.
2. `computedFieldInstancesWithChanges`: the subset of the first collection whose value differs from the source document used for computation.
3. `computedFieldInstancesWithErrors`: computed instances whose computed value has a formal error.
4. `clearedFieldInstances`: computed fields that were filled in the source document but are to be understood as unfilled after computation, including explicit clearing and failure to compute because guards did not apply, an error cascaded, or operands had formal errors.
5. `formalErrorsInOperands`: formal errors collected by the pre-computation formal validation of non-computed operands.
6. `noErrorOccurred`: true exactly when both `computedFieldInstancesWithErrors` and `formalErrorsInOperands` are empty.

These projections are not a disjoint exhaustive enumeration of internal target outcomes:

- `computedFieldInstancesWithChanges` is a subset of `computedFieldInstancesWithoutErrors`;
- a successful unchanged value remains in `computedFieldInstancesWithoutErrors` but not in `computedFieldInstancesWithChanges`;
- clearing is reported separately and is not a member of the successful collection;
- a clean empty outcome for a target that was already absent or empty need not appear in any field-instance projection;
- clearing alone does not make `noErrorOccurred` false;
- formal operand errors are not field-computation errors and must remain a separate message channel.

An illustrative Lean contract is:

```lean
structure KernelComputationView where
  withoutErrors : List ComputedInstance
  withChanges : List ComputedInstance
  withErrors : List ComputedInstance
  cleared : List ComputedInstance
  formalErrorsInOperands : List FormalMessage

def KernelComputationView.noErrorOccurred (view : KernelComputationView) : Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty
```

The lists are an implementation representation of finite API collections, not an ordering promise. Their required laws include address uniqueness within each field-instance collection, `withChanges ⊆ withoutErrors`, value/error coherence for each collection, the exact `noErrorOccurred` equation, and extensional compatibility independent of list order.

The rich internal result should own this projection rather than store only these lossy collections:

```lean
structure ComputeResult where
  effectiveOutcomes : OutcomeOverlay
  kernelView : KernelComputationView
  -- proof or checked invariant that the public view is the exact projection
```

Whether the view is cached or derived is an implementation choice. Its semantic content and bridge laws are required.

### 8.4 Change delta

The existing local `VALUE | CLEARED | ERRORED`-style change delta remains a useful later lossy projection for target-family laws:

- accepted values report VALUE only when typed stored-form equality detects a change;
- clean no-value is silent over an empty prior and CLEARED over a filled prior;
- target rejection reports ERRORED unconditionally;
- some calculation invalidity and inherited-poison outcomes can share the same silence/CLEARED delta as clean no-value even though dependents must distinguish them.

It is not the complete Kernel result contract. In particular, it cannot represent the successful-but-unchanged membership requirement or the separate formal-operand-error collection.

### 8.5 Applied target state

Application is another later projection:

- accepted output stores the exact target representation;
- an outcome with no applied value empties a present target in place;
- an absent target remains absent for clearing and error outcomes;
- a VALUE may create a missing target and the required missing ancestor rows;
- untouched cells preserve placement and raw stored bytes.

This is the document-transition domain.

Neither delta, public collection membership, nor applied state can reconstruct the rich semantic outcome. The scheduler must never use any of these lossy projections as the dependency overlay.

### 8.6 Public equivalence and collection order

The V2 API types these projections as `Collection`, and field instances created during application are documented as being added in no specific order. The proposal therefore defines public result equality extensionally by pointer and payload, with the changed-subset relation stated extensionally as well. Internal schedule order and semantic trace order must not leak into the compatibility theorem merely because one Kernel implementation currently accumulates an `ArrayList`.

If exact iteration order is later shown to be an observable 30.8.1 requirement for a selected compatibility shipment, it must be added as a separately sourced and calibrated projection. Until then, list equality is an implementation theorem, not the public semantic compatibility relation.

## 9. Operational semantics and executable scheduler

### 9.1 Why a relation is required here

For many scalar clauses, a second relation would merely restate a pure evaluator and add no information. Scheduling is different. Intermediate steps expose semantically meaningful facts:

- which computation instance became eligible;
- which target and repetition instance it owns;
- which calculated inputs were unresolved or already completed;
- which reads were reached and in what order;
- which alternative or same-target computation was selected;
- which poison was encountered first;
- which rich outcome entered the overlay;
- why later computations became eligible.

An operational relation or trace model is therefore justified as an independent specification and refinement target.

### 9.2 Proposed relation

The exact atomic step must be established by the scheduler source audit. It must not be guessed to mean one authored declaration, one operation, or one target cell.

Illustratively:

```lean
inductive ComputeStep (plan : CheckedComputationPlan) (context : ProcessingContext) :
    ComputeActivation → StepObservation → ComputeActivation → Prop

inductive Computes (plan : CheckedComputationPlan) (context : ProcessingContext) :
    CheckedDocument → ComputeTrace → ComputeResult → Prop
```

`Computes` may be defined from the reflexive-transitive closure of `ComputeStep` once the step boundary is source-grounded. A direct big-step judgment is also acceptable if it independently presents scheduling, reads, and result construction without reducing to `result = compute ...`.

### 9.3 Executable function

The canonical executable function remains pure and total over its admitted checked domain:

```lean
def compute
    (plan : CheckedComputationPlan)
    (context : ProcessingContext)
    (input : CheckedDocument) : ComputeResult
```

Illegal model shapes belong to checked preparation. Unsupported host capabilities must fail closed through an explicit result or earlier product boundary. Ambient clocks, mutable registries, host exceptions, and IO do not enter the semantic function.

### 9.4 Required bridge properties

The proof spine must include:

```lean
theorem compute_sound :
  compute plan context input = result →
  ∃ trace, Computes plan context input trace result

theorem compute_complete :
  Computes plan context input trace result →
  compute plan context input = result

theorem computes_deterministic :
  Computes plan context input trace₁ result₁ →
  Computes plan context input trace₂ result₂ →
  result₁ = result₂
```

Trace equality is not required merely because results are equal. If the kernel defines the complete schedule trace deterministically, a stronger trace theorem may be stated. Otherwise the theorem must identify the exact trace projection whose uniqueness is claimed.

## 10. Semantic trace contract

### 10.1 Three distinct trace notions

The project must distinguish:

1. The normative call result: Kernel-compatible result projections, an applied document when requested, and separate validation messages.
2. A semantic computation trace: causally meaningful events needed by proofs and named Analyze or Explain consumers.
3. Implementation diagnostics: logs, caches, internal object identities, timings, and optimization details with no semantic status.

Only the second belongs in the logical semantics, and only after its observables or proof purpose are named.

### 10.2 Minimum useful semantic information

The source-grounded trace should be able to establish:

- scheduled computation and target-instance identity;
- ordered reached reads and their semantic observations;
- alternative selection, no-match, or poison termination;
- same-target computation resolution where applicable;
- rich target outcome before delta and application projections;
- completed dependency exposure;
- final rich-outcome insertion and Kernel-view projection;
- first poison and unread suffix boundaries.

The trace should not automatically include:

- source implementation class or method names;
- cache operations;
- physical thread or process identity;
- unobserved speculative reads;
- raw kernel implementation objects;
- timing or memory behavior;
- a fabricated global order where only a derived independence theorem exists.

### 10.3 Public exposure

The semantic trace is initially an internal theorem and consumer-analysis artifact. Public protocol exposure is optional and requires a separately adopted capability. A useful internal trace does not by itself commit the project to a trace file format, schema, CLI, or compatibility promise.

## 11. Application semantics

### 11.1 Separate total operation

Application consumes the resolved computation result and a caller-supplied compatible destination document:

```lean
def apply : ComputeResult → CompatibleDocument → Document
```

The usual destination is the source document used for computation, but this is a client convention rather than a structural restriction on the result. Application executes the source-relative action classification already stored or derived in the result. It does not evaluate expressions, schedule computations, resolve dependencies, select alternatives, recompute changes relative to the destination, or perform generated validation.

### 11.2 Required application laws

Application must prove:

- determinism for a fixed result and destination document;
- exact storage of successful instances in `withChanges`;
- successful instances that are only in `withoutErrors` are not applied;
- `withChanges` remains classified relative to the computation source even when the destination differs;
- clearing preserves target placement when the target exists;
- both `withErrors` and `cleared` clear their represented destination targets;
- clearing and error do not create an absent destination target;
- VALUE creates the target and source-confirmed missing ancestors when required;
- untouched cells retain exact raw stored content;
- only admitted target cells and necessary ancestor rows change;
- each effective application address has one coherent action after accounting for the public projection invariants;
- distinct-address application order is irrelevant only under explicit conditions that account for shared missing ancestors and row order;
- equal applied states do not imply equal semantic outcomes or deltas;
- equal deltas do not imply equal applied placement states.

The existing one-target Number and String application functions and relations are specializations of this later whole-document boundary. They should be reused rather than replaced.

## 12. Validation remains a separate phase

Validation does not compute first. The consumer composes the phases explicitly:

```lean
let result := compute plan context checkedInput
let updated := apply result checkedInput.raw
let messages := validateFull checkedModel context updated
```

Generated computation validation belongs to the validation phase. It preserves every alternative’s guarded mismatch clause and optional tolerance operator. It does not reuse computation’s first-match selector.

Agreement between the selected computation and its generated validation may be proved only under explicit sufficient assumptions, such as mutually exclusive holding alternatives or equal results for every simultaneously holding alternative.

The computation activation must not enqueue or invoke generated validation as a scheduler callback. Doing so would collapse the call surface and make time-dependent expressions, applied stored form, and overlapping alternatives semantically incorrect.

## 13. Determinism, independence, and optimization

### 13.1 Canonical semantics is ordered and deterministic

For a fixed checked model, document, processing context, and kernel-defined schedule, computation should produce one result. Declaration order, alternative order, repetition order, expression order, scan order, target precedence, and poison encounter remain explicit wherever the kernel makes them observable.

The semantics must not replace this with nondeterministic schedule choice or unordered sets.

### 13.2 Independence is a theorem, not a scheduler assumption

Some computations may be independent. The project may later define a precise relation such as:

```lean
def IndependentInstances
    (plan : CheckedComputationPlan)
    (left right : ComputationInstanceId) : Prop := ...
```

A useful theorem would show that two adjacent independent transitions commute and preserve the final result and relevant trace projection. The relation must account for:

- read and write addresses;
- calculated-field dependencies;
- same-target precedence;
- shared repetition or index construction;
- missing-ancestor creation;
- host oracles and time-dependent expressions;
- formal invalidity and poison reads;
- generated findings.

Only such a theorem can justify parallel execution, schedule reordering, caching, or compiled dependency plans. A dependency graph alone is not proof of semantic independence.

### 13.3 Partial-order traces are optional and derived

Unlike PSSM orthogonal regions, A12 does not currently require a partial-order trace as its normative meaning. A partial order may later summarize a proved commutation class for analysis or compilation, but the canonical executable trace remains ordered unless kernel evidence establishes otherwise.

## 14. Termination and cycles

Indirect cycles between computed fields are possible at the model level, and the kernel exposes cycle-checking behavior. The exact accepted/rejected boundary, cycle path identity, and runtime consequences must be established before the checked plan or termination theorem is fixed.

The design must not assume either of these unsupported accounts:

- every accepted plan is automatically acyclic;
- cycles are handled by arbitrary evaluator fuel.

If accepted checked plans are acyclic, termination should follow from the finite checked schedule and a decreasing pending-instance measure. If some cycles remain legal, their exact kernel 30.8.1 behavior must be represented explicitly.

Fuel may be used internally only if exhaustion remains an explicit nonsemantic result and sufficient-fuel soundness/completeness is proved. Fuel exhaustion must never be mapped to VALUE, CLEARED, ERRORED, clean empty, or poison.

## 15. Required proof obligations

The future scheduler and application boundary is complete only when the following classes of claims are closed for its admitted fragment.

### 15.1 Checked construction

- Checked plan construction rejects illegal target, path, kind, scale, scope, self-reference, and cycle shapes according to the admitted source boundary.
- Every checked computation and generated validation belongs to the same model identity.
- Every scheduled computation instance resolves to a valid target address and repetition environment.
- Static dependency and same-target precedence facts are coherent with the checked expressions and target declarations.

### 15.2 Activation preservation

- Initial activation construction implements computed-input stripping exactly.
- Initial activation construction performs the source-defined non-computed-operand validation pass and retains its messages independently of scheduling outcomes.
- Every operational step preserves activation well-formedness.
- Pending and completed instances remain a coherent partition of the admitted execution state.
- Completed overlays contain only source-grounded rich outcomes.
- The input document remains unchanged throughout computation.

### 15.3 Evaluation and causality

- The executable scheduler is sound and complete against the independent operational account.
- Result semantics is deterministic under fixed inputs and schedule.
- Formal operand errors do not globally abort otherwise admissible computations.
- Formal operand error reporting and dependency poison or skipping remain separate, with each following its own exact source-defined scope.
- Poison can arise only from a reached poisoned dependency or a source-defined local calculation invalidity.
- An invalid cell outside the reached read trace cannot poison the computation.
- Short-circuit, scan stop, first-filled stop, and left-to-right numeric evaluation preserve unread suffix irrelevance.
- Clean unresolved dependencies read empty after stripping, independent of stale stored target values.
- Completed dependencies expose the exact target-family projection of their rich outcome.

### 15.4 Result construction

- The effective result contains no duplicate target cell.
- Same-target first-non-empty resolution is separate from table alternative selection.
- Rich outcome, Kernel-facing computed instance, public collection membership, delta, dependency projection, and application agree at their explicitly proved one-way bridges.
- `withChanges` is an address-and-payload subset of `withoutErrors`.
- a successful unchanged non-clearing computation is retained in `withoutErrors` and excluded from `withChanges`.
- clears, computed-value errors, and formal operand errors project through their distinct channels.
- `noErrorOccurred` is true exactly when computed-value errors and formal operand errors are both empty.
- public computed-instance equality is extensional by pointer and payload and does not depend on internal trace order.
- Lossy projections are accompanied by checked non-laws showing what they cannot reconstruct.

### 15.5 Application and phase composition

- Whole-document application specializes to the existing one-target application laws.
- Application accepts a caller-supplied compatible destination and preserves the source-relative result classification.
- Application acts on `withChanges`, `withErrors`, and `cleared`, but not on successful unchanged instances.
- Application preserves untouched raw content and row topology except source-confirmed VALUE ancestor creation.
- Generated validation is evaluated on the applied document, not the input or activation overlay.
- `compute → apply → validate` composition preserves the public call-surface semantics without fusing the operations.

## 16. Required counterexamples and separating cases

At minimum, the conformance and proof boundary should retain cases that reject these attractive but false accounts:

- a stale computed target is visible before its current computation completes;
- every clear cascades as clean empty;
- every clear cascades as poison;
- eager evaluation may poison on an unread suffix;
- same-target computation selection is the same mechanism as alternative selection;
- selected-operation no-value permits a later alternative to run;
- applying duplicate target writes is an acceptable substitute for compute-time same-target resolution;
- a change delta contains enough information for dependent reads;
- reporting only changed values is equivalent to the Kernel computation result;
- successful unchanged computed values may be omitted from `withoutErrors`;
- formal operand errors may be folded into computed-field errors;
- a formally invalid operand that is not reached during one expression path can therefore be omitted from the eager operand-error result;
- any formal operand error may globally abort all computations;
- clearing makes `noErrorOccurred` false;
- an applied empty cell identifies whether the producer was clean, rejected, locally invalid, or poisoned;
- `compute` may mutate the input document without changing semantics;
- `applyTo` must be tied to the exact source document object;
- `withChanges` may be recomputed relative to the application destination;
- internal schedule order is automatically part of public collection equality;
- generated validation may reuse the first selected alternative;
- a dependency graph alone permits schedule reordering;
- an absent target and a present-empty target are interchangeable during application;
- ERRORED may create an absent target as present-empty;
- an arbitrary fuel bound may be interpreted as a semantic computation result.

## 17. Source-audit gate before implementation

The architectural decision can be reviewed and adopted without answering every internal scheduler question. The V2 API shape and result projections recorded in Sections 6, 8, 11, and 18 are already established constraints. Scheduler implementation must not begin until one bounded source audit establishes the remaining exact facts for kernel 30.8.1:

1. Dependency and formal-prevalidation operand extraction across common guards, alternative guards, operations, filters, groups, stars, semantic indices, and generated forms, including which operand errors are collected even when a runtime expression path is not reached.
2. Schedule construction and the relationship among authored order, dependency order, and target order.
3. Indirect cycle detection, rejection timing, cycle-path reporting, and any accepted residual cycle behavior.
4. Runtime computation-instance construction for nonrepeatable, repeatable, nested, and parallel-join scopes.
5. Several computations targeting one field: exact first-non-empty definition, poison/error behavior, and final no-result behavior.
6. Exact calculated-input stripping and the moment a completed producer becomes visible to dependents.
7. The source-grounded common carrier, if any, for target invalidity, calculation invalidity, and inherited poison across target kinds.
8. The internal origin and address-uniqueness rules for each established public result projection, plus generated-finding ownership and any independently meaningful message ordering.
9. Whether any exact computed-instance iteration order beyond the API's extensional `Collection` contract must be retained for an explicitly selected implementation-compatibility claim.
10. Multi-target application order, shared missing-ancestor creation, row insertion order, and collision behavior.
11. Timing and input document for generated validation relative to compute and apply.

Unknowns that can change result types, activation invariants, or trace events block the implementation. Unknowns that affect only later unsupported families may remain explicit fragment exclusions.

## 18. A12 Kernel API and compatibility contract

### 18.1 Established V2 surface

The current 30.8.1 document runtime exposes the following relevant shape:

```text
compute(DocumentV2, DocumentProcessingConfig)
    → IDocumentComputationResult

IDocumentComputationResult.applyTo(DocumentV2)
    → DocumentV2

validateFull(DocumentV2, DocumentProcessingConfig)
    → IDocumentValidationResult
```

`DocumentV2` is immutable at this surface: computation returns a result, and application returns an updated document while leaving the supplied destination unchanged. Validation remains a separate operation. This agrees with the proposal's core phase separation.

### 18.2 Source-relative result, destination-relative application

The result's `withChanges` and `cleared` classifications are determined relative to the source document used for computation. Later, `applyTo` accepts a caller-supplied destination document. Application must therefore execute the already determined source-relative action plan against that destination; it must not recompute change classification relative to the destination.

For the admitted compatible-document domain, the V2 application projection is:

- apply successful computed instances in `withChanges`;
- clear addresses represented by `withErrors`;
- clear addresses represented by `cleared`;
- do not apply successful instances that are present only in `withoutErrors`, because they were unchanged relative to the computation source;
- retain the other destination content except for source-confirmed ancestor creation and placement effects.

The normal client flow supplies the computation source as the application destination, but the Lean result must support the more general caller-supplied destination behavior. A checked `CompatibleDocument` domain may require matching model identity, pointer legality, and target kinds. The Java method documents only a non-null `DocumentV2`, so failure behavior for an incompatible destination must not be invented as ordinary semantics: either audit and model it for an API-adapter claim or state model-compatible destinations as the admitted fragment.

### 18.3 Semantic compatibility versus Java API compatibility

Two claims must remain separate:

1. **Semantic compatibility:** the Lean evaluator, public result projection, application, and validation correspond extensionally to the observable 30.8.1 behavior for the admitted checked fragment and processing context.
2. **Java API compatibility:** an adapter exposes Java-shaped methods, object types, exceptions, deprecations, collection behavior, and lifecycle or aliasing details.

The project requires the first. It does not need Java classes in the Lean semantic core. The second is an optional shipment or adapter claim and must be stated separately.

An illustrative clean-room compatibility relation is:

```lean
def ResultCompatible
    (lean : ComputeResult)
    (observed : KernelResultObservation) : Prop :=
  sameInstancesByPointer lean.kernelView.withoutErrors observed.withoutErrors ∧
  sameInstancesByPointer lean.kernelView.withChanges observed.withChanges ∧
  sameInstancesByPointer lean.kernelView.withErrors observed.withErrors ∧
  sameInstancesByPointer lean.kernelView.cleared observed.cleared ∧
  sameMessages lean.kernelView.formalErrorsInOperands observed.formalErrorsInOperands ∧
  lean.kernelView.noErrorOccurred = observed.noErrorOccurred
```

This relation consumes retained observations or separately permitted source-grounded evidence; it never links to or calls the Kernel from the Lean project.

### 18.4 Deprecated V1 surface

Deprecated V1 result methods retain a reference to the original mutable `IDocument`, and deprecated application methods can mutate that document in place. Those object-identity, aliasing, and mutation behaviors conflict with neither the semantic core nor the ability to derive a current V2-compatible interpreter: they belong to a legacy adapter boundary.

The initial scheduler must not reproduce V1 mutation internally. If a future shipment claims drop-in V1 API compatibility, it needs an explicit stateful wrapper whose refinement target is the pure Lean result and application semantics. Without that wrapper, the project must claim semantic and V2 behavioral compatibility, not deprecated V1 object-lifecycle compatibility.

### 18.5 Compatibility conclusion

With the result, application, ordering, and processing-context corrections in this revision, the proposal does not conflict with the A12 Kernel V2 APIs and does not compromise the goal of deriving compatible interpreters. It strengthens that goal by making the compatibility projection explicit and provable.

Compatibility would be compromised if an implementation:

- exposed only changed values and dropped successful unchanged instances from `withoutErrors`;
- treated `withChanges`, `withoutErrors`, errors, and clears as one disjoint enumeration;
- omitted `formalErrorsInOperands` or folded it into computed-field errors;
- defined `noErrorOccurred` using clears or changes rather than exactly the two error channels;
- rebound `withChanges` to the application destination instead of the computation source;
- allowed application only to a captured original document;
- used public collection order as internal schedule order without a separately established contract;
- omitted a `DocumentProcessingConfig` observable from the explicit processing context;
- reused the lossy public view, change delta, or applied document as the dependency overlay;
- claimed deprecated V1 drop-in compatibility while providing only immutable V2 behavior.

## 19. Scope

### 19.1 Required

The adopted design requires:

- a separate checked whole-model computation plan;
- a model-coherent checked document input;
- an explicit processing context covering every admitted `DocumentProcessingConfig` observable;
- a transient computation activation distinct from the document;
- a source-defined formal-operand-validation snapshot collected before scheduling and kept separate from dependency poison;
- computed-input stripping plus a typed completed-outcome overlay;
- distinct rich outcome, Kernel-compatible result view, delta, applied-state, and dependency projections;
- the exact successful, changed, erroneous, cleared, formal-operand-error, and `noErrorOccurred` result laws;
- pointer-extensional public collection equivalence separate from ordered internal trace semantics;
- one owner for same-target result selection before application;
- an independently meaningful operational relation or trace account;
- a pure executable scheduler proved against that account;
- deterministic semantics under fixed inputs and schedule;
- separate placement-sensitive application to a caller-supplied compatible destination using source-relative classifications;
- separate post-application validation;
- invariant-preservation, causality, locality, and non-law proofs;
- honest supported-fragment and external-evidence status.

### 19.2 Optional after the required boundary closes

The following are optional later capabilities:

- a derived partial-order view of proved-independent transitions;
- an optimized compiled dependency plan with a refinement theorem;
- parallel execution justified by commutation and host-oracle assumptions;
- a public explanation trace or certificate;
- a public protocol or semantic shipment exposing the scheduler fragment;
- model-level dependency, overlap, reachability, or change-impact analyses;
- a separate proof target with additional theorem-library dependencies if concrete graph or finite-map proof needs justify it.

None of these is part of the initial scheduler contract.

### 19.3 Explicitly excluded

The proposal excludes:

- fUML, PSSM, UML, or state-machine code in this repository;
- a generic language workbench or abstract-machine framework;
- semantic visitors, loci, event pools, event accepters, or run-to-completion classes;
- nondeterministic legal schedule sets without kernel evidence;
- a universal synthetic `CheckedCell` dependency overlay invented for code reuse;
- mutation of the input document during `compute`;
- generated validation inside the scheduler;
- a trace schema, registry, packet, generator, qualification runner, or new evidence harness;
- a new Lake package or runtime dependency;
- refactoring completed narrow capsules merely to reserve future abstractions;
- deprecated V1 object aliasing and in-place mutation in the initial pure scheduler core;
- protocol expansion or public compatibility claims before the semantic family is closed and calibrated.

## 20. Relationship to current code

No current module needs immediate refactoring to adopt this proposal.

The existing String direct cascade remains a narrow, explicit two-step witness. Its embedded prior-target value is runtime test input for that capsule and must not be treated as the future static computation declaration shape.

The existing Number dependency projection remains cause-free until a source-grounded consumer proves a richer carrier is required. It must not be coerced into the String synthetic-cell representation.

The existing Number and String exact application relations remain the owning local laws. Whole-document application should compose and specialize them.

The existing Number and String change deltas remain useful local projections, but they are not the future whole-document `IDocumentComputationResult` analogue. No immediate refactor is required; the later shared result must derive those deltas while also retaining successful unchanged instances and formal operand errors.

The existing checked expressions, conditions, alternative selector, generated-validation lowering, addressing, and repetition topology remain reusable components. The whole-model plan aggregates their certificates rather than cloning their evaluators.

The currently active shared condition work should finish before this proposal affects implementation. General operand construction and checked document construction remain prerequisites to the scheduler.

## 21. Recommended semantic sequence

Adopt the architectural constraints now, as a reviewed decision, without implementing them in the current active capsule. Implementation can wait through the current shared-expression/condition work, repeatable addressing, and checked-document construction. It must not wait beyond the point where the general checked-document/public-result shape is frozen, and it is a hard prerequisite before any general scheduler, dependency graph, shared outcome overlay, or whole-document application is introduced.

The recommended implementation order is:

1. Finish the shared checked condition and expression boundary.
2. Finish general repeatable addressing and operand construction.
3. Finish the general model-owned checked document construction route without baking scheduler state into it.
4. Fix the admitted `ProcessingContext` boundary for the first computation fragment.
5. Perform the bounded scheduler source audit listed above.
6. Define the checked whole-model computation plan and its legality invariants.
7. Define initial activation construction, including calculated-input stripping.
8. Close one source-grounded nonrepeatable scheduling slice with rich outcome overlay, operational relation, executable scheduler, Kernel-compatible result projection, proofs, and counterexamples.
9. Add same-target computation resolution and prove effective result uniqueness before whole-document application.
10. Compose exact application to a caller-supplied compatible destination without fusing it into computation.
11. Extend through repeatable instances, joins, missing ancestors, and target families only through the shared owners.
12. Close generated validation over the applied document.
13. Batch external calibration after a coherent scheduling family exists.

This sequence does not authorize new infrastructure or broad operator work. Each implementation unit remains an ordinary semantic capsule or bounded risk spike under the project’s existing limits.

## 22. Alternatives considered

### 22.1 One monolithic `computeAndApplyAndValidate`

Rejected. It contradicts the observed call surface, hides calculated-input stripping, makes stale versus completed dependency reads ambiguous, and makes it impossible to state application and generated-validation preservation independently.

### 22.2 Mutate a working `Document` after every computation

Rejected. The Kernel-facing semantic account says `compute` returns a stable result and `applyTo` is separate. Incremental document mutation risks exposing stale or prematurely applied values, losing rich poison provenance, and confusing target placement with dependency observation.

### 22.3 Reuse change deltas as scheduler state

Rejected. Deltas deliberately collapse clean no-value, some invalidity, and poison cases that downstream computations distinguish. They also collapse absent and present-empty prior placement.

### 22.4 Reuse applied target state as scheduler state

Rejected. Equal final empty states do not identify clean no-value, target rejection, calculation invalidity, or inherited poison. Application is too lossy to drive dependency reads.

### 22.5 Convert every completed result into `CheckedCell`

Rejected at the current boundary. String and Number do not yet share the required cause representation. A universal cell would either invent a cause, erase a distinction, or become a generic tagged wrapper with no shared consumer law.

### 22.6 Define only an executable scheduler

Rejected. Scheduling, read causality, and state preservation are precisely the boundary where an independent operational account adds semantic information and provides a refinement target.

### 22.7 Define only a relational scheduler

Rejected. The project requires an executable reference oracle, compact conformance cases, and downstream consumer value. A relation without a total executable path would not meet that goal.

### 22.8 Adopt PSSM or a generic state-machine runtime

Rejected. PSSM is a useful precedent for semantic layering, but its event-driven hierarchical concurrency machinery does not describe A12 computation. Importing it would add a large unrelated abstraction and obscure the deterministic A12 mechanisms.

### 22.9 Treat independent computations as unordered

Rejected as canonical semantics. Independence and commutation must be proved against the ordered reference semantics. They cannot be assumed from distinct targets or a dependency graph alone.

## 23. Feasibility risks

### 23.1 Missing shared poison carrier

The current String and Number dependency paths are intentionally different. This may require a type-indexed overlay or family-specific read adapters. That is acceptable. The risk becomes a blocker only if the checked plan or scheduler tries to erase those differences.

### 23.2 Document representation and missing ancestors

The current document preserves row order and raw cell placement but is not yet a general checked mutable tree. Whole-document application must create missing ancestors without corrupting row identity or raw untouched bytes. The checked document and addressing work must close before this boundary is generalized.

### 23.3 Cycles and termination

The exact cycle rule may affect the checked plan type and termination proof. This is a required source-audit result, not a reason to add fuel or speculative cycle states now.

### 23.4 Trace overcommitment

A rich trace can accidentally turn kernel implementation details into public semantics. Every retained event must have an observable or proof consumer. Public trace compatibility is excluded from the initial work.

### 23.5 Premature generalization

The scheduler is a genuine shared mechanism, but its target outcomes and dependency projections remain typed. Generalize only the plan, activation, scheduling, and trace structure whose meaning is demonstrated by multiple completed target families. Do not generalize every result payload.

### 23.6 Public collection order versus internal order

The public V2 surface promises collections, not schedule-aligned lists, while the current implementation necessarily has an iteration order. Accidentally using list equality in the main compatibility theorem would overfit an implementation detail; discarding all order inside the activation would lose genuine scheduling semantics. The design therefore keeps an ordered internal trace and uses pointer-extensional equality for public computed-instance projections. Any later exact iteration-order claim requires separate evidence and a narrower compatibility theorem.

### 23.7 Custom semantics and determinism

Custom conditions and custom field types can make a vague `World` unsound: an evaluator could appear pure while consulting mutable Java factories or registries behind the boundary. The admitted Lean context must instead expose a fixed semantic interpretation or explicit oracle observations, and determinism theorems must state any required extensionality assumptions. Unsupported custom capabilities fail closed rather than disappearing from the compatibility claim.

### 23.8 Compatibility-scope drift

Semantic compatibility, current V2 behavioral compatibility, and deprecated V1 object-lifecycle compatibility are different deliverables. Combining them would either pollute the pure semantics with mutation or create a false drop-in claim. Every shipment must name which layer it provides; V1 aliasing remains an optional adapter concern.

## 24. Acceptance criteria

The architecture is accepted when reviewers agree to all of the following decisions:

1. `compute`, `apply`, and `validate` remain separate semantic operations.
2. General computation uses a separate checked plan rather than extending a narrow field model into a universal runtime object.
3. Computation executes through a transient activation over an immutable checked input document.
4. Not-yet-computed calculated targets read empty through stripping; completed targets read through a rich typed outcome overlay.
5. The processing context accounts explicitly for every admitted `DocumentProcessingConfig` observable and freezes actual-date and custom-semantic effects at the pure boundary.
6. Rich target outcome, dependency observation, Kernel-compatible result view, delta, and applied cell state remain distinct.
7. The public result preserves all successful non-clearing instances, their changed subset, computed-value errors, cleared previously filled instances, eagerly collected formal operand errors, and the exact `noErrorOccurred` law.
8. Public computed-instance collection compatibility is pointer-extensional and is not identified with internal schedule or trace order.
9. Formal operand errors are collected by the source-defined prepass, remain separate from computed-target errors, and do not become a global computation abort.
10. Same-target computation resolution occurs before application and is not conflated with table alternative selection.
11. Application accepts a caller-supplied compatible destination, retains source-relative change classification, and acts only through the result's established application projections.
12. Scheduling receives an independently meaningful relation or trace semantics plus a pure executable evaluator.
13. The executable evaluator is proved sound, complete, deterministic, and invariant-preserving for its admitted fragment.
14. A12’s ordered deterministic semantics remains canonical; independence and partial orders are derived only by proof.
15. Semantic compatibility and Java API compatibility are separate claims; deprecated V1 mutation requires an optional adapter and is not part of the pure core.
16. No fUML/PSSM runtime machinery, generic transition framework, dependency, protocol, or harness is added.
17. Existing narrow computation capsules remain intact until the shared scheduler supplies a real second consumer and exact common law.
18. The decision is adopted now, implementation waits for the bounded source-audit gate and checked model, operand, and document prerequisites, and no SG4 scheduler work begins without this boundary.

## 25. Final recommendation

Adopt this corrected architecture now as the design constraint for the future computation-scheduling and state-transition semantic unit, without changing the current active implementation. Implementation can wait for the checked expression, addressing, operand, and document prerequisites, but the decision cannot safely be deferred into SG4 scheduler construction.

The main benefit is not reuse of state-machine concepts. It is prevention of a specific architectural error: collapsing a computation’s immutable input, transient dependency state, rich target outcomes, change report, applied document, and subsequent validation into one evaluator or document mutation loop.

The proposed checked plan, complete processing context, computation activation, rich result, Kernel-compatible projection, and destination-parameterized application give Lean the right objects for executable semantics, causal traces, invariant-preservation proofs, compatible interpreter derivation, consumer explanations, and later verified optimizations. At the same time, the design preserves the project’s existing strengths: small total functions, typed semantic distinctions, checked elaboration, deterministic order, independent evidence, and generalization only after multiple real semantic users establish a shared mechanism.
