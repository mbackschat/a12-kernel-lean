import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.StarAddressing

/-! # Checked general star-path lowering

This boundary resolves structured group-segment stars against one validated `FlatModel`, derives the exact outer-to-inner repeatable axes from the field declaration, and identifies the first reopened axis. Runtime rows remain owned by `StarAddressing`.
-/

namespace A12Kernel

/-- One decoded group-path segment with its authored wildcard marker. -/
structure SurfaceStarGroupSegment where
  name : String
  starred : Bool := false
  deriving Repr, DecidableEq

/-- A decoded field path whose group segments retain their individual wildcard markers. Parent navigation itself is never wildcardable. -/
structure SurfaceStarFieldPath where
  base : PathBase
  groups : List SurfaceStarGroupSegment
  field : String
  deriving Repr, DecidableEq

namespace SurfaceStarFieldPath

def toFieldPath (source : SurfaceStarFieldPath) : SurfaceFieldPath :=
  { base := source.base, groups := source.groups.map (·.name), field := source.field }

end SurfaceStarFieldPath

inductive StarPathElabError where
  | resolve (error : ResolveError)
  | wildcardOnNonrepeatable (path : GroupPath)
  | missingWildcard (path : List String)
  | iterationBelowWildcard (path : GroupPath)
  | addressing (error : StarAddressingError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One field declaration and general star plan certified against the same validated model. -/
structure CheckedStarFieldPath (model : FlatModel) where
  declaration : FlatFieldDecl
  path : StarPath
  modelWellFormed : model.validate.isOk = true
  declarationOwned : model.fields.contains declaration = true
  ancestryOwned : path.axes.map (·.level) = declaration.repeatableScope
  firstStarWithin : path.firstStar < path.axes.length
  pathValid : path.validate.isOk = true

private structure MarkedStarAxis where
  path : GroupPath
  axis : StarAxis
  starred : Bool

private def firstInvalidWildcard? (model : FlatModel) :
    GroupPath → List SurfaceStarGroupSegment → Option GroupPath
  | _, [] => none
  | pathPrefix, segment :: rest =>
      let path := pathPrefix ++ [segment.name]
      if segment.starred &&
          !model.repeatableGroups.any (fun group => group.path == path) then
        some path
      else
        firstInvalidWildcard? model path rest

private def markedAxes (model : FlatModel) :
    GroupPath → List SurfaceStarGroupSegment → List MarkedStarAxis
  | _, [] => []
  | pathPrefix, segment :: rest =>
      let path := pathPrefix ++ [segment.name]
      let tail := markedAxes model path rest
      match model.repeatableGroups.find? (fun group => group.path == path) with
      | none => tail
      | some group =>
          { path
            axis := { level := group.level, repeatability := group.repeatability }
            starred := segment.starred } :: tail

private def firstStarredAxis? : List MarkedStarAxis → Nat → Option Nat
  | [], _ => none
  | axis :: rest, index =>
      if axis.starred then some index else firstStarredAxis? rest (index + 1)

private def firstUnstarredAxis? : List MarkedStarAxis → Option GroupPath
  | [] => none
  | axis :: rest => if axis.starred then firstUnstarredAxis? rest else some axis.path

/-- Resolve a legal starred field path into the exact model-owned ancestry consumed by `StarAddressing`. A relative turning point may precede later stars; the first star and every deeper repeatable level must be explicitly starred. -/
def elaborateStarFieldPath (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarFieldPath) :
    Except StarPathElabError (CheckedStarFieldPath model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let declaration ←
        model.resolveFieldDeclarationUnchecked declaringGroup source.toFieldPath |>.mapError .resolve
      let basePath ← match source.base with
        | .absolute => pure []
        | .relative parents => GroupPath.walkUp declaringGroup parents |>.mapError .resolve
      match firstInvalidWildcard? model basePath source.groups with
      | some path => throw (.wildcardOnNonrepeatable path)
      | none => pure ()
      let baseSegments := basePath.map fun name => ({ name } : SurfaceStarGroupSegment)
      let marked := markedAxes model [] (baseSegments ++ source.groups)
      let firstStar ← match firstStarredAxis? marked 0 with
        | none => throw (.missingWildcard declaration.path)
        | some index => pure index
      match firstUnstarredAxis? (marked.drop firstStar) with
      | some path => throw (.iterationBelowWildcard path)
      | none => pure ()
      let path : StarPath := { axes := marked.map (·.axis), firstStar }
      if hFirstStar : path.firstStar < path.axes.length then
        match hPath : path.validate with
        | .error error => throw (.addressing error)
        | .ok () =>
            if hDeclaration : model.fields.contains declaration = true then
              if hAncestry : path.axes.map (·.level) = declaration.repeatableScope then
                pure {
                  declaration
                  path
                  modelWellFormed := by rw [hModel]; rfl
                  declarationOwned := hDeclaration
                  ancestryOwned := hAncestry
                  firstStarWithin := hFirstStar
                  pathValid := by rw [hPath]; rfl
                }
              else
                throw .incoherentCore
            else
              throw .incoherentCore
      else
        throw .incoherentCore

end A12Kernel
