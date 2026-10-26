#!/usr/bin/env bash
# Fail if any Kernel message-catalog sentence appears verbatim in this repository's tracked source.
#
# WHY THIS IS A GATE AND NOT A CONVENTION. This project is MIT; the A12 Kernel is EUPL-1.2 OR
# commercial. The clean-room rule permits learning behaviour from Kernel source and forbids copying its
# expression, and a message catalog is the most expression-like artifact the Kernel has — authored
# English prose whose only purpose is to be read. Copying one of its sentences into an MIT file is a
# licence violation in a way that copying an identifier is not: `zahlZuLang` is the functional name a
# conforming consumer must compute, while the sentence beside it is a localisation resource that
# consumer takes from the Kernel's own bundle.
#
# The distinction this gate enforces is therefore KEY versus TEXT. Naming a class, code, or parameter
# is required of us; reproducing its rendered sentence is forbidden. An audit on 2026-09-07 found six
# Kernel sentences that had reached `spec/` and `docs/sources/` this way, none of them deliberate and
# all of them in prose describing a probe's outcome — which is exactly how it happens, so prose alone
# was never going to hold the line.
#
# RETAINED EVIDENCE IS IN SCOPE, and it is where the bulk of the exposure was. The rule covers an
# archived receipt as much as a Lean file, but this gate originally searched only `.lean`, `.md` and
# `.sh`, so a probe artifact that verbatim records what the Kernel printed went unseen. On 2026-09-08
# that gap held 1,586 sentences across 124 tracked JSON files in 77 capture directories. They were
# redacted in place at the `message` and `summary` keys, textually rather than through a JSON
# round-trip, so the diff is one line per sentence and every other byte is unchanged; the affected
# SHA-256 values were re-recorded in their checkpoints in the same change. The retained `code`,
# `field`, `severity` and `type` are untouched, so nothing a checkpoint cites was lost, and the
# sentence stays one re-run away from the retained model and request.
#
#   ./scripts/check-no-kernel-prose.sh
#
# Exits nonzero and names every offending sentence and file.
set -euo pipefail

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repository_root"
export LC_ALL=C

kernel_root="../a12-kernel"
if [[ ! -d "$kernel_root" ]]; then
  echo "kernel prose guard skipped: ${kernel_root} is not checked out" >&2
  exit 0
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

find "$kernel_root/kernel-tool" "$kernel_root/kernel-rt" \
  \( -name build -o -name .git \) -prune -o \
  -name 'error_messages*.properties' -print 2>/dev/null | sort > "$work/catalogs"

if [[ ! -s "$work/catalogs" ]]; then
  echo "kernel prose guard found no message catalogs; the Kernel layout has changed" >&2
  exit 1
fi

# A catalog entry becomes one pattern: its literal words are escaped and each interpolation point —
# the `<named>` placeholders and the printf-style `%s` / `%1$s` / `%d` the Kernel also uses — becomes a
# bounded wildcard. That is what catches a RENDERED message, which is how the copies actually arrive:
# our prose quotes a diagnostic with the value already substituted, so it matches no catalog line
# verbatim even though every word of it is the Kernel's.
#
# Checking every short fragment unconditionally was tried on 2026-09-07 and rejected. It fires on a
# two-word unit phrase or on a four-word opening before a quoted group name — ordinary English plus an
# identifier, which no one authored and no licence reaches — and acting on those findings would strip
# real documentation to satisfy a gate. A short fragment is therefore checked only where our prose
# quotes it.
#
# The catalogs are ISO-8859-1, the Java properties default, and decoding them as UTF-8 does not fail
# loudly — it drops more than half the files and mangles every umlaut in the rest, which leaves the
# gate passing over prose it never actually read. Measured 2026-09-07: UTF-8 yields 491 entries
# against latin-1's full set.
python3 - "$work/catalogs" "$work/checks" "$work/literals" <<'PYTHON'
import re, sys

INTERPOLATION = re.compile(r'<[a-zA-Z0-9]+>|%[0-9]*\$?[a-zA-Z]')
# Separators are dropped on both sides of the comparison (see the corpus pass), because a copy that adds
# or drops a comma is still the sentence.
SEPARATORS = re.compile(r'\s*[,;:]+\s*')

def bare(text):
    return ' '.join(SEPARATORS.sub(' ', text).split())

# Each check is (kind, required literal, exact regex). The literal is a piece every match must contain,
# which is what lets the corpus pass below stay a fixed-string search.
checks = set()

def add(kind, pieces, frame=''):
    literal = max(pieces, key=len)
    body = '.{0,80}'.join(re.escape(piece) for piece in pieces)
    checks.add((kind, literal, f'{frame}{body}{frame}'))

for path in open(sys.argv[1]):
    try:
        lines = open(path.strip(), encoding='latin-1').read().splitlines()
    except OSError:
        continue
    for line in lines:
        matched = re.match(r'^[A-Za-z_][A-Za-z0-9_.]*\s*=\s*(.+)$', line)
        if not matched:
            continue
        body = matched.group(1).strip()
        # A run is trimmed of the quotes, colon and full stop that frame its neighbouring placeholder
        # before it is compared, because a quote drops that framing together with the placeholder:
        # `At '%s': There must be ...` leaves the run `': There must be ...`, which no prose quoting
        # the sentence alone ever contains. Untrimmed, eight catalog sentences in eighteen places
        # passed this gate on 2026-09-23.
        # Runs are also split at sentence ends, because a quote of the first sentence of a two-sentence
        # entry otherwise matches no run: a rendered date-type refusal quoted that way passed on
        # 2026-09-23.
        runs = [bare(sentence.strip().strip("'\":,;.()[] "))
                for run in INTERPOLATION.split(body)
                for sentence in re.split(r'(?<=[.!?])\s+', run)]
        for run in runs:
            # A partial quote of a long sentence escapes the whole-entry check, because that check
            # requires the sentence to end where the catalog ends, so each run of 40+ characters is a
            # check of its own. Forty is above the noise floor measured on 2026-09-07. Below forty a run
            # of four or more words counts only where our prose quotes it, which is how all eleven short
            # copies found on 2026-09-23 sat, while the coincidences at that length were unquoted.
            if len(run) >= 40:
                add('long', [run])
            elif len(run) >= 15 and len(run.split()) >= 4:
                add('quoted', [run])
        pieces = [bare(piece) for piece in INTERPOLATION.split(body) if bare(piece)]
        # The 25-character floor counts an entry's LITERAL words only, so a template that is mostly
        # placeholders is judged on the words it actually contributes.
        if len(INTERPOLATION.sub('', body).strip()) >= 25:
            add('long', pieces)
        # In retained JSON every string is quoted, so quoting says nothing there; what marks a copy is a
        # string value that renders a whole entry. That catches the short entries below the floor: a
        # 23-character required-field sentence survived in two artifacts until 2026-09-23.
        if pieces and len(INTERPOLATION.sub('', body).split()) >= 3:
            add('json', pieces, frame='"')

with open(sys.argv[2], 'w', encoding='utf-8') as out:
    out.writelines(f'{kind}\t{literal}\t{pattern}\n' for kind, literal, pattern in sorted(checks))
with open(sys.argv[3], 'w', encoding='utf-8') as out:
    out.writelines(literal + '\n' for literal in sorted({literal for _, literal, _ in checks}))
PYTHON

# ONE FIXED-STRING PASS, THEN EXACT CHECKS ON THE CANDIDATE LINES. Every check carries a literal that any
# match must contain, so a fixed-string search over those literals finds every candidate line. Only
# those lines are then tried against each check's full pattern, which cannot span a line either.
# Feeding the full patterns to ripgrep instead costs regex compilation per pattern: 1,878 of them used
# more than 60 CPU-seconds per run on 2026-09-23, where the 2026-09-07 comment here had measured under
# 2s for 1,096. A context prefix on each short pattern then left ripgrep no literal to anchor on at all,
# and the search ran unbounded at full CPU.
#
# SEPARATORS ARE IGNORED THROUGHOUT. The corpus is searched through a mirror whose commas, semicolons and
# colons are blanked line by line, as the catalog runs above are, so line numbers survive. spec/11 carried
# the index-field refusal's sentence with one added comma, which the exact gate passed until the
# 2026-10-26 spec audit found it.
#
# CASE IS IGNORED THROUGHOUT. A quote that starts mid-sentence or lowercases the catalog's capital still
# copies the sentence: spec/05 carried the date-type refusal's sentence with a lowercase first word,
# which the case-sensitive gate passed until the 2026-10-26 spec audit found it.
#
# ripgrep when it is available, BSD grep otherwise. Measured 2026-09-07 on this repository: 1096
# fixed strings cost about 98s through BSD `grep -F -f` and under 2s through `rg -Ff`, because ripgrep
# builds one Aho-Corasick automaton where BSD grep rescans per pattern. The fallback is kept so the gate
# still runs where ripgrep is absent, just slowly.

git ls-files --cached --others --exclude-standard -- A12Kernel spec docs scripts evidence \
  | grep -E '\.(lean|md|sh|json)$' > "$work/files"
python3 - "$work/files" "$work/corpus" <<'PYTHON'
import os, re, sys
SEPARATORS = re.compile(r'[ \t]*[,;:]+[ \t]*')
for path in open(sys.argv[1], encoding='utf-8').read().splitlines():
    if not os.path.isfile(path):
        continue
    text = open(path, encoding='utf-8', errors='replace').read()
    target = os.path.join(sys.argv[2], path)
    os.makedirs(os.path.dirname(target), exist_ok=True)
    with open(target, 'w', encoding='utf-8') as out:
        out.write(re.sub(r'[ \t]+', ' ', SEPARATORS.sub(' ', text)))
PYTHON

# Both tools exit 1 for "no match" and 2 for an error, and only the first means a clean tree. The gate
# once discarded that difference, so a pattern set too large to compile read as a pass on 2026-09-23.
search_status=0
if command -v rg >/dev/null 2>&1; then
  (cd "$work/corpus" && rg --fixed-strings --ignore-case --no-heading --with-filename --line-number \
    --no-ignore --file "$work/literals" A12Kernel spec docs scripts evidence) > "$work/candidates" \
    || search_status=$?
else
  (cd "$work/corpus" && grep -rniF -f "$work/literals" A12Kernel spec docs scripts evidence) \
    > "$work/candidates" || search_status=$?
fi
if (( search_status > 1 )); then
  echo "kernel prose guard could not search the corpus (exit ${search_status}); refusing to pass" >&2
  exit 1
fi

python3 - "$work/checks" "$work/candidates" > "$work/found" <<'PYTHON'
import re, sys

checks = []
for row in open(sys.argv[1], encoding='utf-8'):
    kind, literal, pattern = row.rstrip('\n').split('\t')
    checks.append((kind, literal.lower(), re.compile(pattern, re.IGNORECASE)))

CODE_SPAN = re.compile(r'`[^`]*`')
# An italic opens on a `*` that follows no word character and precedes a non-space, and closes on one
# that follows a non-space and precedes no word character. A star operand such as `Rows*` is neither
# an opener nor, inside prose, a reason to read what follows as quoted.
ITALIC_OPEN = re.compile(r'(?<![\w*/])\*(?=[^\s*])')
ITALIC_CLOSE = re.compile(r'(?<=[^\s*])\*(?![\w*])')

def quoted(text, at):
    # Code spans quote syntax rather than prose, and a `**` pair is emphasis in our own voice.
    before = CODE_SPAN.sub(lambda span: ' ' * len(span.group(0)), text[:at]).replace('**', '  ')
    if before.count('"') % 2 == 1 or before.rfind('\u201c') > before.rfind('\u201d'):
        return True
    openers = [match.start() for match in ITALIC_OPEN.finditer(before)]
    closers = [match.start() for match in ITALIC_CLOSE.finditer(before)]
    return bool(openers) and (not closers or openers[-1] > closers[-1])

for hit in open(sys.argv[2], encoding='utf-8', errors='replace'):
    path, _, rest = hit.rstrip('\n').partition(':')
    number, _, text = rest.partition(':')
    is_json = path.endswith('.json')
    for kind, literal, pattern in checks:
        if literal not in text.lower() or (kind == 'json') != is_json and kind != 'long':
            continue
        for match in pattern.finditer(text):
            if kind in ('long', 'json') or quoted(text, match.start()):
                print(f'{match.group(0)}\t{path}:{number}')
                break
PYTHON

violations="$(wc -l < "$work/found" | tr -d ' ')"
while IFS=$'\t' read -r sentence location; do
  echo "EUPL message prose copied into MIT source:" >&2
  echo "  text: ${sentence}" >&2
  echo "  file: ${location}" >&2
done < "$work/found"

if (( violations > 0 )); then
  echo >&2
  echo "${violations} Kernel sentence(s) reproduced verbatim. Replace each with the class key plus your" >&2
  echo "own description of what it says. Naming the key is required; copying the sentence is not." >&2
  exit 1
fi

echo "kernel prose guard passed: $(wc -l < "$work/checks" | tr -d ' ') catalog checks, none reproduced"
