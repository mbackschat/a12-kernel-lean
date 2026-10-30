#!/usr/bin/env bash
set -uo pipefail

# Watches one implementing U-session for the maintainer: its repository's commits and report or
# plan changes, and whether its Claude Code session is working, waiting or stalled. Run it as a
# Monitor and re-arm on every expiry; the procedure is in docs/IMPLEMENTER-GUIDE.md
# (#watching-the-implementing-session).
#
#   scripts/watch-u-session.sh <worker-repo> [stall-seconds]
#
# Emits one line per change: WATCHING, SESSION, COMMIT, REPORTS-CHANGED, WORKING, WAITING,
# STALLED, TRANSCRIPT-MISSING. The current state is printed at start, so each re-arm restates a
# worker that is still waiting.
#
# Liveness is read from the last user or assistant turn of the newest transcript in the worker's
# Claude Code project directory, never from the file's modification time: idle compaction and
# reopening a session write the file without a turn, which reported a waiting U03 as active twice
# on 2026-10-30. Following the newest transcript also catches a worker restarted as a new session.

repo=$(cd "$1" && pwd) || exit 2
limit=${2:-600}
projects="$HOME/.claude/projects/$(printf %s "$repo" | sed 's/[^A-Za-z0-9]/-/g')"

read -r -d '' turn_state <<'PY'
import json, os, sys, time
from datetime import datetime

path, limit = sys.argv[1], int(sys.argv[2])
with open(path, "rb") as f:
    f.seek(max(0, os.path.getsize(path) - 4_000_000))
    lines = f.read().decode("utf-8", "replace").splitlines()[1:]
last = None
for line in reversed(lines):
    try:
        entry = json.loads(line)
    except ValueError:
        continue
    if entry.get("type") in ("user", "assistant") and "timestamp" in entry \
            and not entry.get("isMeta") and not entry.get("isCompactSummary"):
        last = entry
        break
if last is None:
    print("WORKING 0")
    sys.exit()
age = int(time.time() - datetime.fromisoformat(last["timestamp"].replace("Z", "+00:00")).timestamp())
message = last.get("message", {})
content = message.get("content")
text = content if isinstance(content, str) else " ".join(
    block.get("text", "") for block in content or [] if block.get("type") == "text")
# A turn the worker ended waits for a message; a quiet turn left open is stalled.
ended = last["type"] == "assistant" and message.get("stop_reason") == "end_turn"
state = "WAITING" if ended and age >= 60 else ("STALLED" if age >= limit else "WORKING")
print(state, age, " ".join(text.split())[:240])
PY

reports() {
  git -C "$repo" ls-tree "$1" reports/QUALIFICATION.md reports/QUESTIONS.md reports/SPEC-FEEDBACK.md PLAN.md 2>/dev/null |
    awk '{print $3}' | paste -sd, -
}
next_action() {
  git -C "$repo" show HEAD:PLAN.md 2>/dev/null |
    awk '/^## Next action/{f=1; next} f && /^## /{exit} f && NF{print; exit}' | cut -c1-240
}

seen=$(git -C "$repo" rev-parse HEAD 2>/dev/null)
blobs=$(reports "$seen")
state=none
session=none
echo "WATCHING $(basename "$repo") at ${seen:0:7}"
while true; do
  head=$(git -C "$repo" rev-parse HEAD 2>/dev/null)
  if [ -n "$head" ] && [ "$head" != "$seen" ]; then
    git -C "$repo" log --format='COMMIT %h %s' "$seen..$head" 2>&1
    seen=$head
    now_blobs=$(reports "$head")
    [ "$now_blobs" != "$blobs" ] && echo "REPORTS-CHANGED at ${head:0:7}"
    blobs=$now_blobs
  fi
  transcript=$(ls -t "$projects"/*.jsonl 2>/dev/null | head -n 1)
  if [ -z "$transcript" ]; then
    [ "$state" != missing ] && echo "TRANSCRIPT-MISSING under $projects" && state=missing
  else
    id=$(basename "$transcript" .jsonl)
    [ "$id" != "$session" ] && echo "SESSION $id" && session=$id
    read -r now age excerpt <<<"$(python3 -I -c "$turn_state" "$transcript" "$limit" 2>&1)"
    # A long build writes no turn, so a running build keeps a quiet turn WORKING.
    busy=$(lsof -a -d cwd -c lake -c lean -c z3 -c cargo -c rustc -Fn 2>/dev/null | grep -c "^n$repo")
    [ "$now" = STALLED ] && [ "$busy" -gt 0 ] && now=WORKING
    if [ "$now" != "$state" ]; then
      case $now in
        WAITING | STALLED) echo "$now for ${age}s; last turn: $excerpt | next action: $(next_action)" ;;
        *) echo "$now" ;;
      esac
      state=$now
    fi
  fi
  sleep 20
done
