import A12Kernel.Evidence.FlatProtocolBridge

/-! IO-only synchronization gate for the flat handover and qualification metadata. -/

open A12Kernel.Evidence.FlatProtocolBridge

def main (args : List String) : IO Unit := do
  match args with
  | [] | ["--check"] =>
      let count ← capability.checkArtifacts
      IO.println s!"flat handover: {count}/{count} cases bound; qualification metadata checked"
  | ["--write"] =>
      let count ← capability.writeArtifacts
      let checked ← capability.checkArtifacts
      if checked != count then
        throw (IO.userError s!"flat handover wrote {count} cases but checked {checked}")
      IO.println s!"flat handover: wrote and checked {count} evidence-bound cases plus qualification metadata"
  | _ =>
      IO.eprintln "syncFlatHandover: expected --check or --write"
      IO.Process.exit 2
