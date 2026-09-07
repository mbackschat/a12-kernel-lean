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

# A catalog entry becomes ONE regex: its literal words are escaped and each interpolation point —
# the `<named>` placeholders and the printf-style `%s` / `%1$s` / `%d` the Kernel also uses — becomes a
# bounded wildcard. That is what catches a RENDERED message, which is how the copies actually arrive:
# our prose quotes a diagnostic with the value already substituted, so it matches no catalog line
# verbatim even though every word of it is the Kernel's.
#
# Splitting entries into fragments instead was tried on 2026-09-07 and rejected. It fires on things
# like "decimal places." or "The index for group '" — ordinary English plus a quoted identifier, which
# no one authored and no licence reaches — and acting on those findings would strip real documentation
# to satisfy a gate. The unit of protectable expression is the sentence, so the sentence is the unit
# compared.
#
# The catalogs are ISO-8859-1, the Java properties default, and decoding them as UTF-8 does not fail
# loudly — it drops more than half the files and mangles every umlaut in the rest, which leaves the
# gate passing over prose it never actually read. Measured 2026-09-07: UTF-8 yields 491 entries
# against latin-1's full set.
#
# The 25-character floor counts an entry's LITERAL words only, so a template that is mostly
# placeholders is judged on the words it actually contributes.
python3 - "$work/catalogs" > "$work/texts" <<'PYTHON'
import re, sys

INTERPOLATION = re.compile(r'<[a-zA-Z0-9]+>|%[0-9]*\$?[a-zA-Z]')

patterns = set()
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
        literal = INTERPOLATION.sub('', body)
        if len(literal.strip()) < 25:
            continue
        pattern = ''.join(
            '.{0,80}' if INTERPOLATION.fullmatch(piece) else re.escape(piece)
            for piece in INTERPOLATION.split(body)
            if piece != ''
        ) if INTERPOLATION.search(body) else re.escape(body)
        # re.split drops the separators, so rebuild with them retained.
        pieces = INTERPOLATION.split(body)
        separators = INTERPOLATION.findall(body)
        rebuilt = []
        for index, piece in enumerate(pieces):
            if piece:
                rebuilt.append(re.escape(piece))
            if index < len(separators):
                rebuilt.append('.{0,80}')
        pattern = ''.join(rebuilt)
        if pattern:
            patterns.add(pattern)
        # A partial quote of a long sentence escapes the whole-entry pattern, because that pattern
        # requires the sentence to end where the catalog ends. So each interpolation-free run of 40+
        # characters is also a pattern in its own right. Forty is above the noise floor measured on
        # 2026-09-07: at 15 the run set fires on "decimal places." and "The index for group '", which
        # are ordinary English plus a quoted identifier, while at 40 every hit is a clause someone
        # actually composed.
        for run in INTERPOLATION.split(body):
            run = run.strip()
            if len(run) >= 40:
                patterns.add(re.escape(run))
for pattern in sorted(patterns):
    print(pattern)
PYTHON

# One multi-pattern pass over the corpus, not one pass per sentence. The per-sentence loop is the
# obvious shape and takes minutes against this one's seconds, because it rescans the whole repository
# a thousand times; the per-file lookup below runs only for a sentence already known to be present, so
# on a clean tree it never runs at all.
#
# ripgrep when it is available, BSD grep otherwise. Measured 2026-09-07 on this repository: 1096
# patterns over the four content roots cost about 98s through BSD `grep -F -f` and under 2s through
# `rg -Ff`, because ripgrep builds one Aho-Corasick automaton where BSD grep rescans per pattern. The
# fallback is kept so the gate still runs where ripgrep is absent, just slowly.
if command -v rg >/dev/null 2>&1; then
  rg --no-filename --only-matching --file "$work/texts" \
    --glob '*.lean' --glob '*.md' --glob '*.sh' \
    A12Kernel spec docs scripts 2>/dev/null \
    | sort -u > "$work/found" || : > "$work/found"
else
  grep -rhoE -f "$work/texts" A12Kernel spec docs scripts \
    --include='*.lean' --include='*.md' --include='*.sh' 2>/dev/null \
    | sort -u > "$work/found" || : > "$work/found"
fi

violations="$(wc -l < "$work/found" | tr -d ' ')"
if [[ "$violations" -gt 0 ]]; then
  while IFS= read -r sentence; do
    echo "EUPL message prose copied into MIT source:" >&2
    echo "  text: ${sentence}" >&2
    grep -rlF "$sentence" A12Kernel spec docs scripts \
      --include='*.lean' --include='*.md' --include='*.sh' 2>/dev/null \
      | while IFS= read -r file; do echo "  file: ${file}" >&2; done
  done < "$work/found"
fi

if [[ "$violations" -gt 0 ]]; then
  echo >&2
  echo "${violations} Kernel sentence(s) reproduced verbatim. Replace each with the class key plus your" >&2
  echo "own description of what it says. Naming the key is required; copying the sentence is not." >&2
  exit 1
fi

echo "kernel prose guard passed: $(wc -l < "$work/texts" | tr -d ' ') catalog sentences, none reproduced"
