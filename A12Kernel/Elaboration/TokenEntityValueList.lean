import A12Kernel.Elaboration.TokenEntityList

/-! # Checked mixed String/Enumeration entity-list value lists

This boundary joins two already-certified homogeneous token entity lists to the immutable checked document. Each resolved operand retains its exact String or stored/category Enumeration declaration projection beside the shared canonical topology, addressed payload, hierarchical extent, filter provenance, and positional relevance. Quantifier truth and polarity remain exclusively with `ValueListQuantifier.evalOrdered`.
-/

namespace A12Kernel

inductive TokenEntityValueListFamily where
  | string
  | enumeration
  deriving Repr, DecidableEq

def FlatTextFieldOperand.valueListFamily :
    FlatTextFieldOperand → TokenEntityValueListFamily
  | .string _ => .string
  | .enumeration _ => .enumeration

namespace CheckedTokenEntityOperand

/-- Every base family this slot reads through. A group declares no family of its own, so it contributes one entry per expanded declaration and the whole-list fold below decides homogeneity across slots and inside a group alike. -/
def valueListFamilies (checked : CheckedTokenEntityOperand model) :
    List TokenEntityValueListFamily :=
  checked.tokenOperands.map FlatTextFieldOperand.valueListFamily

end CheckedTokenEntityOperand

namespace CheckedTokenEntitySource

/-- A field-valued token-list side is homogeneous at the kernel base-family boundary. Different Enumeration declarations and stored/category projections remain compatible members of the Enumeration family.

    `none` for an empty list is unreachable through the checked constructors — a certified group expansion is nonempty and every other slot contributes exactly one entry — and stays the conservative answer rather than a fabricated family. -/
def valueListFamily? (checked : CheckedTokenEntitySource model) :
    Option TokenEntityValueListFamily :=
  match checked.operands.flatMap CheckedTokenEntityOperand.valueListFamilies with
  | [] => none
  | family :: rest =>
      if rest.all (fun candidate => candidate == family) then some family
      else none

/-- The selected stored or category token domain of every Enumeration operand this side reads
through, in operand order. A String operand contributes nothing, so a String-family list yields the
empty list and every membership question over it is vacuously satisfied.

The `.stored` domain is read from the declaration rather than from the operand, because a resolved
stored projection carries only the selection; a `.category` one already carries its own tokens. A
declaration this model cannot resolve, or one carrying no enumeration, contributes the **empty**
domain, which refuses every literal — the closed direction, since the alternative would accept a
literal against a domain that was never read. -/
def selectedTokenDomains (checked : CheckedTokenEntitySource model) :
    List (List String) :=
  checked.operands.flatMap fun operand =>
    operand.tokenOperands.filterMap fun token =>
      match token with
      | .string _ => none
      | .enumeration source =>
          match source.projection with
          | .category mapping => some mapping.categoryTokens
          | .stored =>
              match model.lookupUniqueId source.field.id with
              | .ok declaration =>
                  some (declaration.enumeration.map (·.storedTokens) |>.getD [])
              | .error _ => some []

/-- Whether every literal belongs to every selected domain this side exposes.

Vacuously true for a String-family list, which exposes none — the measured Kernel rule constrains a
literal's *value* only where an Enumeration declaration supplies a domain to constrain it against
([checkpoint](../../docs/SOURCES.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
Requiring membership in **every** domain is this project's reading of a multi-declaration list; the
measured rows carry one domain, so a list whose operands declare *different* domains is an untested
shape and the conservative side is taken deliberately. -/
def admitsLiterals (checked : CheckedTokenEntitySource model)
    (literals : List String) : Bool :=
  checked.selectedTokenDomains.all fun domain =>
    literals.all domain.contains

end CheckedTokenEntitySource

/-- The established token entity-list syntax currently checks direct and starred stored projections. Projection-bearing checked sources can enter through `assembleTokenEntityValueListSource` without weakening their certificates. -/
structure SurfaceTokenEntityValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceTokenEntitySource
  values : SurfaceTokenEntitySource
  deriving Repr, DecidableEq

/-- A two-sided token value list whose direct and starred slots retain exact stored/category projection authoring. -/
structure SurfaceProjectedTokenEntityValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceProjectedTokenEntitySource
  values : SurfaceProjectedTokenEntitySource
  deriving Repr, DecidableEq

/-- A parser-independent plural token-entity fields side against decoded String literals. Both base
    families are admitted, the Enumeration one under the declared-token gate its checked form
    carries. -/
structure SurfaceTokenEntityStringLiteralValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceTokenEntitySource
  values : List String
  deriving Repr, DecidableEq

/-- A checked two-sided String or Enumeration value list. Both sides share one base family, and exact direct-reference uniqueness spans the complete authored operation. -/
structure CheckedTokenEntityValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  family : TokenEntityValueListFamily
  fields : CheckedTokenEntitySource model
  values : CheckedTokenEntitySource model
  fieldsFamily : fields.valueListFamily? = some family
  valuesFamily : values.valueListFamily? = some family
  uniqueDirectOperands :
    firstDuplicateDirectTokenField?
      (fields.operands ++ values.operands) = none

/-- The measured plural String-literal form after the complete fields side has been resolved,
    certified as one base family, and retained without lowering a group operand into fields.

    **Both families are admitted**, which is the measured rule rather than the narrower String-only
    one this carrier first shipped: an Enumeration field side is legal against String literals
    provided every literal is a declared token, and one that is not draws
    `MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_OR_CATEGORY`
    ([checkpoint](../../docs/SOURCES.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
    The literal certificate is stated unconditionally because a String side exposes no domain and
    satisfies it vacuously, so one field serves both families without a per-family branch. -/
structure CheckedTokenEntityStringLiteralValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  family : TokenEntityValueListFamily
  fields : CheckedTokenEntitySource model
  fieldsFamily : fields.valueListFamily? = some family
  firstValue : String
  restValues : List String
  literalsAdmitted :
    fields.admitsLiterals (firstValue :: restValues) = true

inductive TokenEntityValueListElabError where
  | fields (error : TokenEntityElabError)
  | values (error : TokenEntityElabError)
  | mixedFamily
  | duplicateOperand (field : FieldId)
  deriving Repr, DecidableEq

inductive TokenEntityStringLiteralValueListElabError where
  | shape (error : FieldEntityShapeElabError)
  | fields (error : TokenEntityElabError)
  | dateGroupAgainstStringValues (path : GroupPath)
  | unsupportedFieldsFamily (found : Option TokenEntityValueListFamily)
  /-- A literal naming no token in a selected Enumeration domain. The Kernel checks the literal's
  **value** here, which is the one place a value list's own literals are constrained statically. -/
  | literalOutsideSelectedDomain (literals : List String)
  | emptyValues
  deriving Repr, DecidableEq

private def FlatFieldDecl.isDate (declaration : FlatFieldDecl) : Bool :=
  match declaration.policy.kind with
  | .temporal .date _ => true
  | _ => false

/-- The exact measured discriminator is a homogeneous Date group. A direct Date field, a group
    merely containing a Date, and every other group certification failure stay outside it. -/
private def ResolvedFieldEntityOperand.homogeneousDateGroupPath? :
    ResolvedFieldEntityOperand model → Option GroupPath
  | operand =>
      match operand.subtreePath? with
      | none => none
      | some path =>
          let declarations := operand.expansionDeclarations
          if !declarations.isEmpty && declarations.all FlatFieldDecl.isDate then
            some path
          else
            none

private def firstHomogeneousDateGroupPath? :
    List (ResolvedFieldEntityOperand model) → Option GroupPath
  | [] => none
  | operand :: remaining =>
      match operand.homogeneousDateGroupPath? with
      | some path => some path
      | none => firstHomogeneousDateGroupPath? remaining

/-- Check the measured plural String-literal form in operator order. The Date-group class is
    projected before token certification erases the rejected expansion's kind; no shared group
    error is reclassified. -/
def elaborateTokenEntityStringLiteralValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceTokenEntityStringLiteralValueListSource) :
    Except TokenEntityStringLiteralValueListElabError
      (CheckedTokenEntityStringLiteralValueListSource model) := do
  -- **A sole unstarred field is legal here**, on all three quantifiers, where the entity-list
  -- carriers refuse one with `MVK_PARAMSIZE_INVALIDN`
  -- ([checkpoint](../../docs/SOURCES.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
  -- The rule is the carrier's, not the shared checker's: comparing fields against *literals* is a
  -- complete question with one field, where comparing them against each other is not.
  let shape ← elaborateFieldEntityShape model declaringGroup authored.fields
      .soleAllowed
    |>.mapError .shape
  let (firstValue, restValues) ←
    match authored.values with
    | [] => throw .emptyValues
    | firstValue :: restValues => pure (firstValue, restValues)
  match firstHomogeneousDateGroupPath? shape.operands with
  | some path => throw (.dateGroupAgainstStringValues path)
  | none => pure ()
  let fields ← certifyTokenEntityShape model declaringGroup shape
    |>.mapError .fields
  match hFamily : fields.valueListFamily? with
  | none => throw (.unsupportedFieldsFamily none)
  | some family =>
      -- The literal gate is the Enumeration side's alone in effect, but it is applied to both
      -- without branching: a String side exposes no domain and passes vacuously, so one call
      -- keeps the rule in one place rather than duplicating it under a family match.
      if hLiterals : fields.admitsLiterals (firstValue :: restValues) = true then
        pure {
          quantifier := authored.quantifier
          family
          fields
          fieldsFamily := hFamily
          firstValue
          restValues
          literalsAdmitted := hLiterals }
      else
        throw (.literalOutsideSelectedDomain (firstValue :: restValues))

namespace TokenEntityStringLiteralValueListElabError

/-- Project only the established operator-specific Date-group class. Shape failures keep the
    shared checker's established classes; every other local refusal remains unmapped. -/
def diagnostic? : TokenEntityStringLiteralValueListElabError →
    Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .dateGroupAgainstStringValues _ => some .onlyStringEnumNumberAllowed
  -- Delegated rather than dropped: the field side's own projection now carries the three-way kind
  -- partition this carrier's message vocabulary draws.
  | .fields error => error.diagnostic?
  | .literalOutsideSelectedDomain _ =>
      some .invalidStringConstantForEnumComparison
  -- A mixed-family list is refused here with no class: the Kernel's own mixing refusal is measured
  -- at the shape checker, and this arm is reached only when the two families disagree *within* one
  -- side, which no row covers. `emptyValues` is a surface impossibility rather than a gate.
  | .unsupportedFieldsFamily _ | .emptyValues => none

end TokenEntityStringLiteralValueListElabError

/-- Join two already-checked token sides without reconstructing declarations or erasing Enumeration projection identity. -/
def assembleTokenEntityValueListSource
    (quantifier : ValueListQuantifier)
    (fields values : CheckedTokenEntitySource model) :
    Except TokenEntityValueListElabError
      (CheckedTokenEntityValueListSource model) :=
  match hFields : fields.valueListFamily?,
      hValues : values.valueListFamily? with
  | some fieldsFamily, some valuesFamily =>
      if hFamily : fieldsFamily = valuesFamily then
        match hUnique :
            firstDuplicateDirectTokenField?
              (fields.operands ++ values.operands) with
        | some field => throw (.duplicateOperand field)
        | none =>
            pure {
              quantifier
              family := fieldsFamily
              fields
              values
              fieldsFamily := hFields
              valuesFamily := by simpa [hFamily] using hValues
              uniqueDirectOperands := hUnique
            }
      else
        throw .mixedFamily
  | _, _ => throw .mixedFamily

/-- Check both stored-projection entity-list sides, then apply the operation-wide family and exact-reference gates. -/
def elaborateTokenEntityValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceTokenEntityValueListSource) :
    Except TokenEntityValueListElabError
      (CheckedTokenEntityValueListSource model) := do
  let fields ← elaborateTokenEntitySource model declaringGroup authored.fields
    |>.mapError .fields
  let values ← elaborateTokenEntitySource model declaringGroup authored.values
    |>.mapError .values
  assembleTokenEntityValueListSource authored.quantifier fields values

/-- Check both projection-bearing token sides through the sole shared entity-list authoring boundary, then apply the operation-wide family and exact-reference gates. -/
def elaborateProjectedTokenEntityValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceProjectedTokenEntityValueListSource) :
    Except TokenEntityValueListElabError
      (CheckedTokenEntityValueListSource model) := do
  let fields ←
    elaborateProjectedTokenEntitySource model declaringGroup authored.fields
      |>.mapError .fields
  let values ←
    elaborateProjectedTokenEntitySource model declaringGroup authored.values
      |>.mapError .values
  assembleTokenEntityValueListSource authored.quantifier fields values

/-- The rich two-sided addressed token stream consumed by Execute/Transform/Explain clients. -/
structure ResolvedCheckedTokenEntityValueList (model : FlatModel) where
  quantifier : ValueListQuantifier
  family : TokenEntityValueListFamily
  fields : List (ResolvedCheckedTokenEntityOperand model)
  values : List (ResolvedCheckedTokenEntityOperand model)

namespace ResolvedCheckedTokenEntityValueList

/-- Execute through the sole encounter-ordered quantifier evaluator. -/
def evaluate (resolved : ResolvedCheckedTokenEntityValueList model) : Verdict :=
  resolved.quantifier.evalOrdered
    (resolved.fields.map (·.valueListSideAt .validation))
    (resolved.values.map (·.valueListSideAt .validation))

end ResolvedCheckedTokenEntityValueList

namespace CheckedTokenEntityValueListSource

def hasHaving (checked : CheckedTokenEntityValueListSource model) : Bool :=
  checked.fields.hasHaving || checked.values.hasHaving

private def resolveFullFields
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand document outer

private def resolveFullValues
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedValidationOperand document outer

/-- Construct both rich sides in the kernel's operator-specific side order without flattening authored operand boundaries or projection certificates. -/
def resolveFull (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedTokenEntityValueList model) := do
  let (fields, values) ← checked.quantifier.resolveSidesOrdered
    (fun () => checked.resolveFullFields document outer)
    (fun () => checked.resolveFullValues document outer)
  pure {
    quantifier := checked.quantifier
    family := checked.family
    fields
    values
  }

def evaluateFull (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError Verdict := do
  pure (← checked.resolveFull document outer).evaluate

private def resolvePartialFields
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  checked.fields.operands.mapM fun operand =>
    operand.resolveCheckedPartialValidationOperand document outer scope

private def resolvePartialValues
    (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :=
  checked.values.operands.mapM fun operand =>
    operand.resolveCheckedPartialValidationOperand document outer scope

/-- Partial validation skips a rule containing any filter before topology, relevance, or target reads; otherwise it constructs the same rich ordered operands with positional nonrelevance. -/
def evaluatePartial (checked : CheckedTokenEntityValueListSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialHavingValueListResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    let (fields, values) ← checked.quantifier.resolveSidesOrdered
      (fun () => checked.resolvePartialFields document outer scope)
      (fun () => checked.resolvePartialValues document outer scope)
    pure (.evaluated (checked.quantifier.evalOrdered
      (fields.map (·.valueListSideAt .validation))
      (values.map (·.valueListSideAt .validation))))

end CheckedTokenEntityValueListSource

end A12Kernel
