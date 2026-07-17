import A12Kernel.Process.ArtifactTree

/-! # Generic artifact-tree IO locks -/

namespace A12Kernel.Process.ArtifactTreeTest

private def symlinkRejected (root : System.FilePath) : IO Bool := do
  try
    let _ ← ArtifactTree.collectFiles root
    pure false
  catch error =>
    pure ((toString error).contains "contains symlink")

def check : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    IO.FS.createDirAll (temporary / "a")
    IO.FS.writeFile (temporary / "a/inside.json") "{}"
    IO.FS.writeFile (temporary / "a.json") "{}"
    let actual := (← ArtifactTree.collectFiles temporary).map (·.toString)
    if actual != ["a.json", "a/inside.json"] then
      throw (IO.userError s!"artifact tree is not globally sorted: {repr actual}")
    discard <| IO.Process.run {
      cmd := "ln"
      args := #["-s", (temporary / "a.json").toString, (temporary / "alias.json").toString] }
    if !(← symlinkRejected temporary) then
      throw (IO.userError "artifact tree accepted a symlink")

end A12Kernel.Process.ArtifactTreeTest
