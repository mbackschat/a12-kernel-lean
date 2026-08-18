# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `revision`: `a2f44f1fe344f3af8a486d9c6220eea3c1d04f6b`
- `gate`: Tier 1 passed for the resolved filled DateRange construction-equality capsule; the a12-dmkits sibling remains clean at `89aa03957034de620562eb23a095d878f6547dca`.
- `capability`: [temporal comparison and aggregates](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates).

<a id="active-unit"></a>
## Selected work

- `state`: ready for route discovery.
- `gap`: none selected.
- `objective`: select the smallest open semantic unit whose source discriminator and implementation route can be verified before red/green.
- `oracle`: start from one exact open record in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md); any selected external evidence must resolve through one keyed checkpoint in [`SOURCES.md`](SOURCES.md).
- `next`: inventory open gap records against current capability owners and in-progress peer work, reject overlaps, then select one exact red/green/proof slice.
- `stop`: do not edit semantics until the selected route, discriminator, exclusions, and owner are verified.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive; evaluate only when the selected work reaches a reusable family, major addressing or computation boundary, or public compatibility claim.
- `resume`: `rg -n '^<a id="gap-|^### (SG|SQ)' docs/SEMANTICS-GAPS.md`
