/-! # Portable SHA-256 process support

IO-only helpers for executable gates. The project already requires either `sha256sum` or macOS `shasum` for retained-evidence snapshot binding; qualification gates reuse the same dependency rather than introducing another hashing implementation.
-/

namespace A12Kernel.Process.Sha256

private def isLowerHex (character : Char) : Bool :=
  decide (character.toNat >= '0'.toNat && character.toNat <= '9'.toNat) ||
    decide (character.toNat >= 'a'.toNat && character.toNat <= 'f'.toNat)

def isDigest (value : String) : Bool :=
  value.length == 64 && value.toList.all isLowerHex

private def command? (command : String) (arguments : Array String) : IO (Option String) := do
  try
    let output ← IO.Process.output { cmd := command, args := arguments }
    if output.exitCode != 0 then
      pure none
    else
      match output.stdout.trimAscii.toString.splitOn " " |>.filter (!·.isEmpty) with
      | digest :: _ => if isDigest digest then pure (some digest) else pure none
      | [] => pure none
  catch _ => pure none

def file (path : System.FilePath) : IO String := do
  match ← command? "sha256sum" #["--", path.toString] with
  | some digest => pure digest
  | none =>
      match ← command? "shasum" #["-a", "256", "--", path.toString] with
      | some digest => pure digest
      | none =>
          throw (IO.userError
            "this gate requires either sha256sum or shasum for exact-file digest binding")

end A12Kernel.Process.Sha256
