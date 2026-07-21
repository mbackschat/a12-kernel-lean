# Codex model selection for agent profiles

**Status:** current operational mapping, reviewed 2026-07-21.

This document maps the stable BEST, REGULAR, and SIMPLE capability profiles in [`CLAUDE.md`](../CLAUDE.md#stable-capability-profiles) to current GPT-5.6 model and reasoning selections. The profiles describe enduring responsibilities; this file owns the deliberately replaceable product-name mapping. Review it when the Codex model family or picker semantics change, not during every semantic capsule.

Explicit selection is safer than naming only a profile because it removes ambiguity for the person or orchestrator starting an agent. It is not enforcement: prompt text cannot switch its own model. The model must be selected in the Codex surface or agent configuration before execution. If a subagent interface cannot enforce a requested model or reasoning level, the root must say so and must not claim that the requested selection ran.

## Current GPT-5.6 mapping

| Abstract profile | Work shape | Requested model | Requested reasoning |
|---|---|---|---|
| BEST | Long-lived root for unresolved, high-risk, or foundational semantics | GPT-5.6 Sol (`gpt-5.6-sol`) | Medium |
| BEST | One isolated exceptionally difficult decision or adversarial review | GPT-5.6 Sol (`gpt-5.6-sol`) | High or Extra High |
| REGULAR | Bounded implementation, proof, synthesis, or ordinary audit | GPT-5.6 Terra (`gpt-5.6-terra`) | Medium |
| REGULAR | Demanding source/Lean audit or deliberately cold consumer probe | GPT-5.6 Terra (`gpt-5.6-terra`) | High |
| SIMPLE | Small exact mechanical extraction, classification, or check | GPT-5.6 Luna (`gpt-5.6-luna`) | Low |
| SIMPLE | Larger mechanical transformation with a closed output contract | GPT-5.6 Luna (`gpt-5.6-luna`) | Medium |

The current Codex guidance describes Sol as the choice for complex open-ended work, Terra as the pragmatic everyday workhorse, and Luna as the choice for clear repeatable work. It identifies Medium as the balanced reasoning level and states that the Power setting currently uses GPT-5.6 Sol with Medium reasoning. See the official [Codex model guidance](https://learn.chatgpt.com/docs/models) and [subagent guidance](https://learn.chatgpt.com/docs/agent-configuration/subagents.md).

Do not select maximum reasoning for a whole feature set by default. Escalate one identified hard decision, then return to the warm root's established selection. Do not select Ultra by default: this repository deliberately controls whether and how subagents are spawned, while Ultra may delegate proactively. An explicit owner request may still choose either setting for a concrete reason.

## Mandatory prompt header

Every minted root or subagent prompt must name both the abstract profile and the current concrete selection. Use this header before the objective:

```text
Agent role: <long-lived root | bounded subagent>
Agent profile: <BEST | REGULAR | SIMPLE>
Requested model: <explicit current model from this document>
Requested reasoning: <explicit current reasoning from this document>
Selection enforcement: <selected by user/configuration | enforced by spawning surface | advisory only; spawning surface cannot select>
```

Do not write `Selection enforcement: enforced` unless the active surface actually exposes and applies the requested model and reasoning choice. If the requested concrete selection is unavailable, surface that before starting rather than silently substituting another profile.

## Long-lived root example

```text
Agent role: long-lived root
Agent profile: BEST
Requested model: GPT-5.6 Sol
Requested reasoning: Medium
Selection enforcement: selected by user before starting this session

Read CLAUDE.md completely, then docs/PLAN.md. Act as the sole writer and integrator for the active semantic feature set. Execute work items sequentially in the shared checkout without worktrees and preserve this root session across commits until the documented feature-set boundary.
```

The user selects GPT-5.6 Sol with Medium reasoning before sending this prompt. In a UI that exposes the current Power preset with the documented mapping, selecting Power is equivalent; an explicit Sol/Medium selection is clearer when Advanced controls are available.

## Demanding cold-probe example

```text
Agent role: bounded subagent
Agent profile: REGULAR
Requested model: GPT-5.6 Terra
Requested reasoning: High
Selection enforcement: <state the actual spawning capability>
Mode: read-only
Context: deliberately cold
Worktree: shared checkout; do not create a worktree
Writes: prohibited

Objective:
<one bounded consumer question>

Allowed sources:
- <exact files>

Forbidden:
- every unlisted source
- prior semantic conversation
- repository writes
- new semantic assumptions

Return:
1. the reconstructed decision procedure or relation;
2. factual findings with exact supplied-source references;
3. every point requiring semantic guessing;
4. contradictions and unresolved questions;
5. whether the consumer can proceed without additional research.
```

A cold consumer probe normally uses REGULAR/Terra/High rather than BEST/Sol because exceptional inference can conceal an unclear shipment. SIMPLE/Luna may later stress-test an already successful handover, but it is not the initial qualification reader.

## Selection and reporting rule

Before starting an agent:

1. Choose the abstract profile under [`CLAUDE.md`](../CLAUDE.md#token-conscious-dispatch-rule).
2. Resolve that profile and work shape through the table above.
3. Put the explicit requested model and reasoning in the prompt header.
4. Select them in the UI/configuration or through the spawning surface when supported.
5. Record whether enforcement was real or advisory.
6. After execution, report any mismatch between the requested and known actual selection.

The abstract profile remains authoritative if this current mapping becomes stale. Refresh this document from official Codex guidance before minting further concrete selections; do not scatter replacement model names through semantic plans or findings.
