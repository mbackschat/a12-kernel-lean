import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.StringPattern

/-! # A12Kernel.Elaboration.StringPattern — checked two-stage pattern admission

The kernel first requires Java-pattern compilation and then applies a finite source gate. Compilation remains an injected capability that returns the whole-value matcher compiled from the exact source, so checked evaluation cannot accidentally substitute a matcher for another pattern. The source scan in `Semantics.StringPattern` is an original character walk over the canonically documented exclusion families; its escape set holds `p` and not `P`, since the one uppercase-`\P` refusal once observed was the possessive `}+` adjacency of `\P{L}+` ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections)). Passing this gate is not a JavaScript-portability claim.
-/

namespace A12Kernel

/-- The runtime pattern carried by an ordinary String declaration. The kernel accepts an authored empty source but constructs no matcher for that declared-field locus. -/
def FlatFieldDecl.effectiveStringPatternSource
    (declaration : FlatFieldDecl) : Option String :=
  match declaration.stringPatternSource with
  | none => none
  | some source => if source.isEmpty then none else some source

/-- Exact preparation failures for one model-owned ordinary String declaration. Model legality and field capability are checked before host compilation. -/
inductive DeclaredStringPatternElabError where
  | model (error : ResolveError)
  | field (error : ResolveError)
  | fieldKind (path : List String) (kind : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | preparedCustomFieldRequired (path : List String)
  | pattern (error : PatternAdmissionError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- The proof that an optional compiler-associated matcher represents exactly the declaration's effective source. -/
def DeclaredStringPatternCoherent (declaration : FlatFieldDecl)
    (pattern : Option (AdmittedStringPattern compilePattern)) : Prop :=
  match declaration.effectiveStringPatternSource, pattern with
  | none, none => True
  | some source, some admitted => admitted.source = source
  | _, _ => False

/-- One ordinary evaluated String declaration and its exact optional compiled matcher. Model-wide preparation retains the validated model separately and rechecks declaration identity at every read. -/
structure PreparedDeclaredStringField
    (compilePattern : StringPatternCompiler) where
  declaration : FlatFieldDecl
  pattern : Option (AdmittedStringPattern compilePattern)
  stringKind : declaration.policy.kind = .string
  evaluatedValue : declaration.stringValueMode = .evaluated
  ordinaryValue : declaration.customType = none
  patternCoherent :
    DeclaredStringPatternCoherent declaration pattern

/-- Prepare one already-selected ordinary String declaration. A nonempty declared source is compiled and admitted once; an absent or empty source remains the ordinary no-pattern policy. -/
def prepareDeclaredStringDeclaration (compilePattern : StringPatternCompiler)
    (declaration : FlatFieldDecl) :
    Except DeclaredStringPatternElabError
      (PreparedDeclaredStringField compilePattern) :=
  match hCustom : declaration.customType with
  | some _ =>
      .error (.preparedCustomFieldRequired declaration.path)
  | none =>
      match hValueMode : declaration.stringValueMode with
      | .raw => .error (.rawStringValue declaration.path)
      | .evaluated =>
          match hKind : declaration.policy.kind with
          | .string =>
              match hSource : declaration.effectiveStringPatternSource with
              | none =>
                  .ok {
                    declaration
                    pattern := none
                    stringKind := hKind
                    evaluatedValue := hValueMode
                    ordinaryValue := hCustom
                    patternCoherent := by
                      simp [DeclaredStringPatternCoherent, hSource]
                  }
              | some source =>
                  match admitStringPattern compilePattern source with
                  | .error error => .error (.pattern error)
                  | .ok admitted =>
                      if hExact : admitted.source = source then
                        .ok {
                          declaration
                          pattern := some admitted
                          stringKind := hKind
                          evaluatedValue := hValueMode
                          ordinaryValue := hCustom
                          patternCoherent := by
                            simp [DeclaredStringPatternCoherent, hSource, hExact]
                        }
                      else
                        .error .incoherentCore
          | kind =>
              .error (.fieldKind declaration.path kind.surfaceKind)

/-- Validate the model, resolve one exact declaration, and prepare its ordinary String format. -/
def prepareDeclaredStringField (compilePattern : StringPatternCompiler)
    (model : FlatModel) (field : FieldId) :
    Except DeclaredStringPatternElabError
      (PreparedDeclaredStringField compilePattern) :=
  match model.validate with
  | .error error => .error (.model error)
  | .ok () =>
      match model.lookupUniqueId field with
      | .error error => .error (.field error)
      | .ok declaration =>
          prepareDeclaredStringDeclaration compilePattern declaration

namespace PreparedDeclaredStringField

/-- Formally check one raw cell through the exact matcher prepared for this declaration. The optional matcher changes no other String-policy clause. -/
def checkRaw (prepared : PreparedDeclaredStringField compilePattern)
    (raw : RawCell) : CheckedCell :=
  prepared.declaration.stringPolicy.checkRawWithPattern
    (prepared.pattern.map (·.wholeValueMatches)) raw

end PreparedDeclaredStringField

/-- A validated model's declaration-ordered set of every effective ordinary declared String pattern. -/
structure PreparedFlatStringPatterns (model : FlatModel)
    (compilePattern : StringPatternCompiler) where
  fields : List (PreparedDeclaredStringField compilePattern)
  modelWellFormed : model.validate.isOk = true

namespace PreparedFlatStringPatterns

def lookup? (prepared : PreparedFlatStringPatterns model compilePattern)
    (field : FieldId) : Option (PreparedDeclaredStringField compilePattern) :=
  prepared.fields.find? fun candidate =>
    candidate.declaration.id == field

/-- Check every prepared pattern through its exact declaration and delegate declarations without an effective pattern to the existing model-owned checker. A missing required entry fails closed instead of silently using the no-pattern route. -/
def checkContext (prepared : PreparedFlatStringPatterns model compilePattern)
    (raw : RawFlatContext) : FlatContext :=
  let ordinary := model.checkContext raw
  {
    read := fun field =>
      match model.lookupUniqueId field with
      | .error _ => malformedCheckedCell
      | .ok declaration =>
          match prepared.lookup? field with
          | some preparedField =>
              if preparedField.declaration == declaration then
                preparedField.checkRaw (raw.read field)
              else
                malformedCheckedCell
          | none =>
              if declaration.effectiveStringPatternSource.isSome then
                malformedCheckedCell
              else
                ordinary.read field
  }

end PreparedFlatStringPatterns

/-- Prepare every effective ordinary declared String pattern in declaration order. Model validation has already excluded raw, custom, and non-String pattern carriers. -/
def prepareDeclaredStringPatterns (compilePattern : StringPatternCompiler) :
    List FlatFieldDecl →
      Except DeclaredStringPatternElabError
        (List (PreparedDeclaredStringField compilePattern))
  | [] => .ok []
  | declaration :: remaining =>
      match declaration.effectiveStringPatternSource with
      | none => prepareDeclaredStringPatterns compilePattern remaining
      | some _ => do
          let prepared ←
            prepareDeclaredStringDeclaration compilePattern declaration
          let preparedRemaining ←
            prepareDeclaredStringPatterns compilePattern remaining
          pure (prepared :: preparedRemaining)

/-- Validate one model once, then compile and accept all of its effective ordinary declared String patterns. -/
def prepareFlatStringPatterns (compilePattern : StringPatternCompiler)
    (model : FlatModel) :
    Except DeclaredStringPatternElabError
      (PreparedFlatStringPatterns model compilePattern) :=
  match hModel : model.validate with
  | .error error => .error (.model error)
  | .ok () =>
      match prepareDeclaredStringPatterns compilePattern model.fields with
      | .error error => .error error
      | .ok fields =>
          .ok {
            fields
            modelWellFormed := by
              rw [hModel]
              rfl
          }

/-- The parser-level pattern shape: a direct field path, one of the two dedicated operators, and a constant source. Arbitrary expressions cannot inhabit this type. -/
structure SurfaceStringPatternCondition where
  op : StringPatternOp
  field : SurfaceFieldPath
  source : String
  deriving Repr, DecidableEq

/-- Exact checked-construction failures for the ordinary nonrepeatable String fragment. Prepared custom/predefined and repeatable fields retain separate context boundaries. -/
inductive StringPatternConditionElabError where
  | model (error : ResolveError)
  | fieldReference (error : ResolveError)
  | fieldKind (path : List String) (kind : SurfaceScalarKind)
  | pattern (error : PatternAdmissionError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace StringPatternConditionElabError

/-- Project the measured pattern-source failure, the wrong-left-kind class, and the field operand's
resolver classes. The left-kind gate is **total** over the kinds a declaration can carry: DATE_RANGE
was the one the original admission matrix omitted, and it draws the same class as the other seven on
both operators ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-pattern-comparison-left-kind-gate-is-total)).
The resolver classes are the shared ones on both operators
([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)).
The surface makes the right operand a String constant structurally; remaining local refusals stay
unmapped instead of guessing an external identity. -/
def diagnostic? : StringPatternConditionElabError → Option KernelStaticDiagnostic
  -- A String left operand is admitted, so this arm is never constructed; it is kept for totality
  -- and reports nothing rather than a refusal class for a kind the gate accepts.
  | .fieldKind _ .string => none
  | .fieldKind _ .number
  | .fieldKind _ .boolean
  | .fieldKind _ .confirm
  | .fieldKind _ .enumeration
  | .fieldKind _ .dateRange
  | .fieldKind _ (.temporal .date)
  | .fieldKind _ (.temporal .time)
  | .fieldKind _ (.temporal .dateTime) =>
      some .invalidTypeForPatternComparison
  | .pattern .javaSyntax
  | .pattern .kernelRestriction => some .invalidPattern
  | .fieldReference error => error.diagnostic?
  | .model _ | .incoherentCore => none

end StringPatternConditionElabError

/-- Recheck that a field belongs to the validated model and is an evaluated String. Its optional declared pattern is supplied separately by the model-complete prepared context. -/
def FlatModel.admitsStringPatternField (model : FlatModel)
    (field : FlatStringField) : Bool :=
  match model.lookupUniqueId field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.stringValueMode == .evaluated &&
        match declaration.policy.kind with
        | .string => true
        | _ => false

/-- One authored condition whose direct field and exact compiled pattern are certified against the same model. It is a checked leaf, not a second connective tree. -/
structure CheckedStringPatternCondition (model : FlatModel)
    (compilePattern : StringPatternCompiler) where
  rowGroup : GroupPath
  op : StringPatternOp
  field : FlatStringField
  pattern : AdmittedStringPattern compilePattern
  modelWellFormed : model.validate.isOk = true
  fieldWellFormed :
    model.admitsStringPatternField field = true

/-- Resolve and certify a checked pattern condition. The written field binds row reads while lexical resolution stays at the declaring group; source admission follows the field-value gates. -/
def elaborateStringPatternCondition (compilePattern : StringPatternCompiler)
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceStringPatternCondition) (writtenGroup : GroupPath := rowGroup) :
    Except StringPatternConditionElabError
      (CheckedStringPatternCondition model compilePattern) :=
  match hModel : model.validate with
  | .error error => .error (.model error)
  | .ok () => do
      -- The pattern's field is a field-value read, whose gates answer ahead of the kind gate below
      -- ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)).
      let declaration ←
        (checkFieldValueRead (do
          let declaration ← model.resolveFieldDeclarationUnchecked rowGroup surface.field
          match model.unboundReadLevel? rowGroup writtenGroup declaration.repeatableScope
              (model.repeatableScopeForGroupPath writtenGroup) with
          | some unbound => throw (.unboundOperandLevel declaration.path unbound)
          | none => pure declaration)
          (model.ruleGroupRead rowGroup writtenGroup surface.field)).mapError .fieldReference
      let field ←
        match declaration.policy.kind with
        | .string => pure { id := declaration.id }
        | kind => throw (.fieldKind declaration.path kind.surfaceKind)
      let pattern ←
        (admitStringPattern compilePattern surface.source).mapError .pattern
      if hField : model.admitsStringPatternField field = true then
        pure {
          rowGroup
          op := surface.op
          field
          pattern
          modelWellFormed := by
            rw [hModel]
            rfl
          fieldWellFormed := hField
        }
      else
        throw .incoherentCore

namespace CheckedStringPatternCondition

/-- Truth-only projection for an already-selected row; rule execution retains faults through the admitted pattern boundary. -/
def evalSelected (checked : CheckedStringPatternCondition model compilePattern)
    (context : FlatContext) : Verdict :=
  (checked.pattern.evalResolved checked.op
    (context.resolveDirectStringComparisonOperand checked.field)).toOption.getD .unknown

/-- The direct field is the condition's only model reference. -/
def referencesField (checked : CheckedStringPatternCondition model compilePattern)
    (field : FieldId) : Bool :=
  checked.field.id == field

end CheckedStringPatternCondition

/-- A checked pattern condition together with the compiler that admitted it, so a validation leaf can
carry the exact matcher without its leaf family being indexed by a compiler. -/
structure CheckedStringPatternLeaf (model : FlatModel) where
  compilePattern : StringPatternCompiler
  condition : CheckedStringPatternCondition model compilePattern

end A12Kernel
