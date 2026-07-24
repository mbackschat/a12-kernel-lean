import A12Kernel.Elaboration.Flat.Condition

/-! # Checked flat runtime context construction -/

namespace A12Kernel

structure RawFlatContext where
  read : FieldId → RawCell

def malformedCheckedCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

/-- Return the one source matcher whose meaning is already implemented without an injected host compiler. -/
def locallyExecutableStringPatternMatcher? (source : String) :
    Option (String → Bool) :=
  if source == asciiDigitsPatternSource then
    some matchesAsciiDigitsPattern
  else
    none

/-- Return the one declaration matcher whose meaning is already implemented without an injected host compiler. Every wider admitted source remains available only through the prepared pattern capability. -/
def FlatFieldDecl.executableStringPatternMatcher?
    (declaration : FlatFieldDecl) : Option (String → Bool) :=
  declaration.stringPatternSource.bind locallyExecutableStringPatternMatcher?

/-- Compile one raw cell through declaration-owned scalar, ordinary String-policy, locally executable declared-pattern, or closed-Enumeration admission. Registered custom Strings require their prepared overlay and fail closed here. -/
def FlatFieldDecl.checkRaw (declaration : FlatFieldDecl) (raw : RawCell) : CheckedCell :=
  match declaration.customType, declaration.policy.kind, declaration.enumeration with
  | some _, _, _ => malformedCheckedCell
  | none, .enumeration, some source =>
      match elaborateEnumeration source with
      | .ok checked => checked.checkRaw raw
      | .error _ => malformedCheckedCell
  | none, .enumeration, none => malformedCheckedCell
  | none, .string, none =>
      if declaration.stringValueMode == .raw then
        formalCheck declaration.policy raw
      else
        match declaration.stringPatternSource with
        | none =>
            declaration.stringPolicy.checkRawWithPattern none raw
        | some source =>
            if source.isEmpty then
              declaration.stringPolicy.checkRawWithPattern none raw
            else
              match declaration.executableStringPatternMatcher? with
              | some matcher =>
                  declaration.stringPolicy.checkRawWithPattern
                    (some matcher) raw
              | none => malformedCheckedCell
  | none, _, some _ => malformedCheckedCell
  | none, _, none => formalCheck declaration.policy raw

/-- Compile raw cells with the same unique declaration and policy used by elaboration.
    An invalid/unresolved identifier becomes malformed rather than acquiring a guessed
    default policy. -/
def FlatModel.checkContext (model : FlatModel) (raw : RawFlatContext) : FlatContext where
  read id :=
    match model.lookupUniqueId id with
    | .ok declaration => declaration.checkRaw (raw.read id)
    | .error _ => malformedCheckedCell

def elaborateAndEvalUnpreparedFull (model : FlatModel) (world : World)
    (declaringGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool) (condition : SurfaceCondition) :
    Except ElabError Verdict := do
  let checked ← elaborate model declaringGroup condition
  pure (checked.core.evalFull ((model.checkContext raw).withWorld world) hasContent)

end A12Kernel
