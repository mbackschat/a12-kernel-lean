You are rewriting one chapter of the language-neutral semantics in `spec/`. The spec describes the A12 kernel 30.8.1 validation and computation semantics and is the only semantic input a cold implementer receives. It grew by appending one measured finding at a time; a verified audit found overrides, enumerations without rules and process narrative. Your rewrite makes the chapter mechanism-first without losing or changing any rule except where this brief says so.

## Your chapter and inputs

- Chapter: `spec/{CHAPTER}` (read it completely first).
- The rewrite contract: the `spec-rewrite-plan` section of `docs/PLAN.md`.
- The verified findings for this chapter: the `spec/{NN}` section of `reviews/2026-10-26-spec-audit.md`, plus these rows from other sections that cite this chapter: {EXTRA_ROWS}.
- Implementer feedback: the U01 worker's debrief at `{FEEDBACK}`; use every row that names this chapter. A row is a reader-confusion signal and a capture pointer, not a rule.
- Edits earlier chapter rewrites owe this chapter: the `## Other chapters` sections of `reviews/spec-rewrite/*-notes.md` that name this chapter. Apply each that is within this chapter.
- `spec/14-operator-reference.md` owns operator membership facts (which class an operator takes per column). Point to it instead of restating a list it holds. A per-operator list this chapter owns becomes a spec/14 column or cells: write the revised spec/14 in full as one of `{EXTRA_OUT}`, keep the class definitions and measured scope in this chapter, and follow spec/14's cell policy (`n/a` only where a chapter states the refusal, otherwise `not stated`).
- You may read other `spec/` chapters, `A12Kernel/` Lean sources and `docs/` as needed. Never open `../a12-kernel/`, `../a12-rulekit/` or any sibling repository.

## Hard rules

1. Write only `{OUT}` (the new chapter), `{NOTES}` (your change notes) and the full revised chapters named in `{EXTRA_OUT}`, which carry the moves this run owes other chapters. Edit no repository file. Run no builds. Never use `rm` with a glob.
2. Preserve every normative rule. A rule may be reworded, moved within the chapter, merged with a duplicate or generalised only when the general statement yields the same result on every case the old text decides. If you cannot keep a rule, list it in the notes; never drop one silently.
3. Do not decide a behavioural change yourself. Where a finding requires choosing between two statements, write the side that current Lean implements (open the def and name it in the notes), and list the choice under "behavioural decisions" in the notes with both old texts and the Lean evidence. If Lean does not decide it, keep the old text, mark it in the notes as unresolved, and do not invent a rule. Before listing a decision, grep the other `spec/` chapters for a sentence that already decides it; if one does, cite it instead. A rule taken from Lean is marked unmeasured in the spec text unless a `docs/sources/` checkpoint measures it; search checkpoint bodies, not only headings.
4. Keep every `§n` number and every heading anchor that other files link to (grep `docs/`, `spec/` and `A12Kernel/` for `{CHAPTER}#` to see which anchors are used). You may add sections; do not rename linked headings.
5. No rendered Kernel message sentences; name message codes only. No absolute paths, user names or hostnames. No Lean implementation status, Lean def names or "the reference account" in the spec text (they belong in the notes). No negative existentials ("unreachable", "no legal model", "never authorable") unless the old text cites a measurement for it; otherwise write "no witness known".
6. Provenance: remove checkpoint, inbound and a12-dmkits links from inside rule sentences. Keep them, deduplicated, as one line per section starting `Sources:`, after the section's rules. Delete measurement narrative, history ("an earlier version said"), reader warnings and confidence chatter, but keep any confidence limit that bounds a rule, stated as a scope ("measured on X; other Y unmeasured").
7. Non-normative implementation notes: any normative content found only inside one moves into the rules; the note keeps only implementation advice, or is deleted.
8. Structure: lead each section with its general rule, then its exceptions as bounded cases, then closed tables for operator- or carrier-specific facts. A list given by example becomes a closed list when the chapter or Lean closes it; otherwise state it as "measured members: …; others unmeasured".
9. Markdown: one paragraph per line, no hard wrapping; tables for case lists. English.
10. Fix every finding in your list whose remedy is within this chapter. A remedy that edits another chapter goes into the notes under "other chapters", not into your output.

## Notes file format (`{NOTES}`)

1. `## Findings`: one line per finding id: fixed (where), deferred (why), or not applicable (why).
2. `## Behavioural decisions`: each choice per rule 3, with both old texts quoted (≤150 characters each), the side taken and the Lean def name and file.
3. `## Unresolved`: each kept-as-is conflict.
4. `## Rules not kept`: should be empty; otherwise each with the reason.
5. `## Other chapters`: edits other chapters need.
6. `## Anchors`: every linked anchor and where it now lives.

Before returning, list in the notes under "Rules not kept" every old sentence you removed or reworded that carries a scope or closing word (only, never, every, all, no, measured, unmeasured, no witness), each with where its content now lives; a sentence with no new home is a lost rule and must be restored.

When corrections arrive after the preservation check, change only what the correction list names; any other cut needs the same check, so list it instead of making it.

Return a five-line summary as your final message: output size in bytes and lines, counts for each notes section.
