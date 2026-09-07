#!/usr/bin/env bash
# Emit a `dmtool batch` ops.json for `rule check` rows from a declarative spec, so a probe matrix is
# generated rather than hand-typed.
#
# Why this exists, measured: a 140-row session was typed row by row, 11 of those rows were lost to
# typos in a repeated condition, and every literal control character or emoji in a message had to be
# smuggled past the shell. All three are authoring costs, not instrument costs — the kernel answers a
# row in about 0.12 seconds.
#
# Scope is `rule check` only, because it is the verb whose whole probe varies in argv. `computation
# add --dry-run` batches just as well but takes a spec *file* per row, so its matrix is a directory of
# specs rather than the argv template this generator emits.
#
#   ./scripts/make-probe-ops.sh <spec> <out.json>
#
# Spec grammar, one directive per line, `#` comments and blank lines ignored:
#
#   field <alias> <absolute field path>
#   cond  <alias> <condition text>
#   msg   <alias> <message text>
#   group <alias> <absolute group path>
#   row   <id> <field alias> <cond alias> <msg alias> [group alias]
#   cross <id prefix> <field aliases> <cond aliases> <msg aliases>    (comma-separated, no spaces)
#
# A `row`'s optional fifth token names a rule group, which is what lets the error field sit INSIDE a
# repeatable group. Without it every reference into a repeatable group needs an explicit star, and the
# missing-star refusal fires before whatever gate the row was actually aimed at — measured 2026-09-07,
# where it swallowed twelve of twenty rows.
#
# `cross` emits the full product with generated ids `<prefix>00`, `<prefix>01`, … in field-major then
# condition-major order. Message text may carry `\n`, `\t`, `\\` and `\u{XXXX}` for any code point,
# including the supplementary plane, which is expanded to the surrogate pair JSON requires. That is
# what keeps a control character or an emoji out of the shell command that produces the batch.
set -euo pipefail

for required_tool in awk; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    echo "probe ops generator requires ${required_tool}" >&2
    exit 1
  fi
done

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <spec> <out.json>" >&2
  exit 2
fi

spec="$1"
out="$2"

if [[ ! -f "$spec" ]]; then
  echo "spec not found: ${spec}" >&2
  exit 1
fi

awk -v out="$out" '
function fail(message) { printf("%s:%d: %s\n", FILENAME, FNR, message) > "/dev/stderr"; failed = 1 }

function hexval(s,   i, c, n, digits) {
  digits = "0123456789abcdef"; n = 0
  s = tolower(s)
  for (i = 1; i <= length(s); i++) {
    c = index(digits, substr(s, i, 1))
    if (c == 0) return -1
    n = n * 16 + (c - 1)
  }
  return n
}

# Expand the spec escapes into JSON string escapes. A code point above the BMP becomes the surrogate
# pair JSON requires; anything else passes through as \uXXXX, which the batch reader decodes.
function expand(s,   result, rest, brace, hex, cp, high, low) {
  result = ""
  while (length(s) > 0) {
    if (substr(s, 1, 3) == "\\u{") {
      rest = substr(s, 4)
      brace = index(rest, "}")
      if (brace == 0) { fail("unterminated \\u{ escape"); return result }
      hex = substr(rest, 1, brace - 1)
      cp = hexval(hex)
      if (cp < 0) { fail("bad hex in \\u{" hex "}"); return result }
      # Decimal constants deliberately: onetrueawk parses 0xD800 as 0 followed by a variable, which
      # silently produced \u0000-based garbage instead of a surrogate pair.
      if (cp >= 65536) {
        high = 55296 + int((cp - 65536) / 1024)
        low  = 56320 + ((cp - 65536) % 1024)
        result = result sprintf("\\u%04X\\u%04X", high, low)
      } else {
        result = result sprintf("\\u%04X", cp)
      }
      s = substr(rest, brace + 1)
    } else if (substr(s, 1, 2) == "\\n") { result = result "\\n"; s = substr(s, 3) }
    else if (substr(s, 1, 2) == "\\t") { result = result "\\t"; s = substr(s, 3) }
    else if (substr(s, 1, 2) == "\\\\") { result = result "\\\\"; s = substr(s, 3) }
    else {
      # A bare quote or backslash still has to survive into JSON.
      if (substr(s, 1, 1) == "\"") result = result "\\\""
      else if (substr(s, 1, 1) == "\\") result = result "\\\\"
      else result = result substr(s, 1, 1)
      s = substr(s, 2)
    }
  }
  return result
}

function emit(id, fieldAlias, condAlias, msgAlias, groupAlias,   groupArgs) {
  if (!(fieldAlias in field)) { fail("unknown field alias: " fieldAlias); return }
  if (!(condAlias in cond)) { fail("unknown cond alias: " condAlias); return }
  if (!(msgAlias in msg)) { fail("unknown msg alias: " msgAlias); return }
  if (groupAlias != "" && !(groupAlias in grp)) { fail("unknown group alias: " groupAlias); return }
  if (id in seen) { fail("duplicate row id: " id); return }
  seen[id] = 1
  # The Kernel rejects a rule code carrying anything but letters and digits.
  if (id ~ /[^A-Za-z0-9]/) { fail("row id must be alphanumeric: " id); return }
  rows++
  groupArgs = (groupAlias == "") ? "" : sprintf(", \"--group\", \"%s\"", expand(grp[groupAlias]))
  body[rows] = sprintf(" {\n  \"id\": \"%s\",\n  \"verb\": \"rule\",\n  \"args\": [\"check\", \"--code\", \"%s\", \"--field\", \"%s\"%s, \"--condition\", \"%s\", \"--message\", \"en_US=%s\"]\n }",
    id, id, expand(field[fieldAlias]), groupArgs, expand(cond[condAlias]), expand(msg[msgAlias]))
}

function split_list(text, target,   n, i, parts) {
  n = split(text, parts, ",")
  for (i = 1; i <= n; i++) target[i] = parts[i]
  return n
}

/^[[:space:]]*(#|$)/ { next }

{
  directive = $1
  if (directive == "field" || directive == "cond" || directive == "msg" || directive == "group") {
    if (NF < 3) { fail(directive " needs an alias and a value"); next }
    alias = $2
    # Strip the directive and the alias POSITIONALLY. Searching for the alias with index() is the
    # obvious shape and is wrong: a one-character alias matches inside the directive keyword itself, so
    # `msg m Hi.` yielded "g m Hi." — a silently corrupted probe row rather than an error. Found by a
    # self-test of this generator on 2026-09-07. Note the awk program is single-quoted in the shell, so
    # an apostrophe here terminates it; keep this comment apostrophe-free.
    value = $0
    sub(/^[[:space:]]*[^[:space:]]+[[:space:]]+[^[:space:]]+[[:space:]]*/, "", value)
    if (directive == "field") field[alias] = value
    else if (directive == "cond") cond[alias] = value
    else if (directive == "group") grp[alias] = value
    else msg[alias] = value
    next
  }
  if (directive == "row") {
    if (NF != 5 && NF != 6) { fail("row needs: row <id> <field> <cond> <msg> [group]"); next }
    emit($2, $3, $4, $5, (NF == 6) ? $6 : "")
    next
  }
  if (directive == "cross") {
    if (NF != 5) { fail("cross needs: cross <prefix> <fields> <conds> <msgs>"); next }
    prefix = $2
    fn = split_list($3, fs); cn = split_list($4, cs); mn = split_list($5, ms)
    counter = 0
    for (fi = 1; fi <= fn; fi++)
      for (ci = 1; ci <= cn; ci++)
        for (mi = 1; mi <= mn; mi++) {
          emit(sprintf("%s%02d", prefix, counter), fs[fi], cs[ci], ms[mi], "")
          counter++
        }
    next
  }
  fail("unknown directive: " directive)
}

END {
  if (failed) { print "no ops written" > "/dev/stderr"; exit 1 }
  if (rows == 0) { print "spec produced no rows" > "/dev/stderr"; exit 1 }
  printf("[\n") > out
  for (i = 1; i <= rows; i++) printf("%s%s\n", body[i], (i < rows ? "," : "")) > out
  printf("]\n") > out
  printf("%d rows written to %s\n", rows, out)
}
' "$spec"
