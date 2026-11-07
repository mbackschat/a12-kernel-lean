import A12Kernel.Elaboration.Flat.Types

/-! # Keyword quoting of authored paths

An authored path may quote a name that collides with the condition language's terminal set. Lowering checks
that every colliding name is quoted and erases the quotes into the structured field path that resolution reads;
rendering restores the canonical quotes. Resolution of the lowered path is `Model.lean`'s.
-/

namespace A12Kernel

def PathKeywordProfile.requiresQuote (profile : PathKeywordProfile)
    (name : String) : Bool :=
  profile.reserved.contains name

namespace AuthoredPathName

/-- Validate one exact-case keyword collision and erase accepted quote syntax before semantic name lookup. Unnecessary quotes are legal and become semantically transparent. -/
def lower (name : AuthoredPathName) (profile : PathKeywordProfile) :
    Except PathSyntaxError String :=
  if profile.requiresQuote name.text && !name.quoted then
    .error (.unquotedKeyword name.text)
  else
    .ok name.text

end AuthoredPathName

namespace PathKeywordProfile

/-- Canonical structured rendering quotes exactly the names that collide with the selected language's terminal set. -/
def reifyName (profile : PathKeywordProfile) (name : String) :
    AuthoredPathName :=
  { text := name, quoted := profile.requiresQuote name }

end PathKeywordProfile

namespace AuthoredFieldPath

/-- Validate quote provenance in every name-bearing position, then erase it into the sole existing structured field-path representation. -/
def lower (path : AuthoredFieldPath) (profile : PathKeywordProfile) :
    Except PathSyntaxError SurfaceFieldPath := do
  let turningPoint ← match path.turningPoint with
    | none => pure none
    | some name => pure (some (← name.lower profile))
  let groups ← path.groups.mapM (·.lower profile)
  let field ← path.field.lower profile
  pure { base := path.base, turningPoint, groups, field }

end AuthoredFieldPath

namespace SurfaceFieldPath

/-- Reintroduce canonical quote provenance without changing the semantic path identity. -/
def reifyQuotes (path : SurfaceFieldPath) (profile : PathKeywordProfile) :
    AuthoredFieldPath :=
  {
    base := path.base
    turningPoint := path.turningPoint.map profile.reifyName
    groups := path.groups.map profile.reifyName
    field := profile.reifyName path.field
  }

end SurfaceFieldPath

end A12Kernel
