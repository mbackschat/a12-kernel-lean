You are checking a rewrite of one chapter of `spec/`. Another agent rewrote it to be mechanism-first. The rewrite must preserve every normative rule except the changes its notes declare. A lost or silently altered rule would ship to an implementer as a defect, so try hard to find one.

Inputs:
- Old chapter: `spec/{CHAPTER}` in the repository (unchanged).
- New chapter: `{OUT}`.
- The rewriter's notes: `{NOTES}`.
- The finding list it worked from: the `spec/{NN}` section of `reviews/2026-10-26-spec-audit.md` plus {EXTRA_ROWS}.

Hard limits: read-only everywhere; never open sibling repositories; run no builds; never reproduce Kernel message sentences.

Method:
1. Walk the old chapter paragraph by paragraph, table row by table row. For every normative statement (a result, an order, a class, a scope, a condition, a measured limit), find where the new chapter states it. Give one row per statement: old line, new line(s), verdict `kept`, `generalised-ok` (new general rule gives the same result on every case the old text decided; name the cases you checked), `declared-change` (listed in the notes' behavioural decisions), `lost`, or `altered` (the new text gives a different result on some case, with the case).
2. For each behavioural decision in the notes, open the named Lean def and confirm it implements the side taken. Verdict `lean-confirmed` or `lean-contradicts`.
3. For each finding id, check the notes' disposition against the new text: `fixed` really fixes it, `deferred` has a valid reason.
4. Check the hard rules: no Kernel message sentences, no Lean names or status in the new spec text, no unmeasured negative existentials, no links inside rule sentences, every linked anchor still resolves (grep `docs/`, `spec/`, `A12Kernel/` for links into this chapter).

Output: first a summary (counts per verdict), then a table of every `lost`, `altered`, `lean-contradicts` and failed-finding row with evidence, then the full statement table. Be precise; a false `lost` costs a review round, a missed one ships a defect.
