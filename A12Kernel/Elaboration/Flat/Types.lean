import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Semantics.CustomFieldType
import A12Kernel.Semantics.CheckedEnumeration
import A12Kernel.Semantics.StringFieldPolicy
import A12Kernel.Semantics.NumericTarget
import A12Kernel.Elaboration.NumericScale

/-! # A12Kernel.Elaboration.Flat — checked lowering into the flat core

This capsule starts from structured, parser-independent surface paths and conditions. It resolves absolute, parent-relative including explicit turning-point labels, and bare field references against an expanded flat model, rejects unsupported or ambiguous input, and lowers accepted conditions into the existing typed non-repeatable core. A quote-aware structured adapter retains whether each field/group name was single-quoted, validates collisions against an injected exact-language keyword profile, erases only the accepted quote syntax, and then delegates to the same resolver. Concrete EN/DE text parsing, stars, semantic indices, and repeatable evaluation remain outside this fragment.
-/

/-! This focused module owns the parser-independent surface syntax, checked model declarations, and diagnostic types. -/

namespace A12Kernel

abbrev GroupPath := List String

namespace FieldId

/-- Return the first authored field identifier whose same identifier occurs again later in the list. -/
def firstDuplicate? : List FieldId → Option FieldId
  | [] => none
  | field :: remaining =>
      if remaining.contains field then some field
      else firstDuplicate? remaining

end FieldId

inductive PathBase where
  | absolute
  | relative (parents : Nat)
  deriving Repr, DecidableEq

/-- A turning-point label belongs only to a positive relative parent walk. -/
def PathBase.allowsTurningPoint : PathBase → Option String → Bool
  | .absolute, turningPoint => turningPoint.isNone
  | .relative parents, turningPoint => parents > 0 || turningPoint.isNone

/-- A field path after concrete syntax has decoded quoting and path separators. For a
    relative path, `parents = 0`, `groups = []` is the bare-name form and therefore uses
    the documented declaring-group → flag-gated model-wide lookup order. There is no
    implicit ancestor walk; parent lookup requires an explicit `parents > 0`. -/
structure SurfaceFieldPath where
  base : PathBase
  /-- Optional authored name of the group reached by a positive parent count. It validates that turning point but never changes how many levels are crossed. -/
  turningPoint : Option String := none
  groups : List String
  field : String
  deriving Repr, DecidableEq

/-- The exact selected condition language's terminal spellings. Membership is deliberately case-sensitive; callers derive this finite profile from the language version they support. -/
structure PathKeywordProfile where
  reserved : List String
  deriving Repr, DecidableEq

/-- One already-tokenized entity name, retaining whether the author used the grammar's single-quote escape. -/
structure AuthoredPathName where
  text : String
  quoted : Bool := false
  deriving Repr, DecidableEq

/-- A structured field path before keyword-quote validation. Path separators and parent counts have already been decoded, but quote provenance remains available to the checked boundary. -/
structure AuthoredFieldPath where
  base : PathBase
  turningPoint : Option AuthoredPathName := none
  groups : List AuthoredPathName
  field : AuthoredPathName
  deriving Repr, DecidableEq

inductive PathSyntaxError where
  | unquotedKeyword (name : String)
  deriving Repr, DecidableEq

/-- A direct textual field operand or one exact Enumeration category access after concrete syntax has decoded `->`. -/
inductive SurfaceTextFieldOperand where
  | direct (field : SurfaceFieldPath)
  | category (field : SurfaceFieldPath) (name : String)
  deriving Repr, DecidableEq

inductive SurfaceComparisonOp where
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

/-- Authored operand position of a point-in-time source. `Today` and `Now` comparison syntax permit either side. -/
inductive SurfacePointInTimePosition where
  | left
  | right
  deriving Repr, DecidableEq

inductive SurfaceLiteral where
  | number (value : Rat)
  | boolean (value : Bool)
  | string (value : String)
  | date (components : TemporalComponents) (instant : Instant)
  deriving Repr, DecidableEq

inductive SurfaceScalarKind where
  | number
  | boolean
  | confirm
  | string
  | enumeration
  | temporal (kind : TemporalKind)
  | dateRange
  deriving Repr, DecidableEq

/-- Drop a declaration kind's per-kind configuration, keeping only the surface kind. Several static
gates are decided by the kind alone, so they share this projection rather than each matching the
configured form. -/
def FieldKind.surfaceKind : FieldKind → SurfaceScalarKind
  | .number _ => .number
  | .boolean => .boolean
  | .confirm => .confirm
  | .string => .string
  | .enumeration => .enumeration
  | .temporal kind _ => .temporal kind
  | .dateRange => .dateRange

/-- Whether a String declaration exposes an evaluation value. Raw Strings retain storage presence but close every checked value-reading route. -/
inductive StringValueMode where
  | evaluated
  | raw
  deriving Repr, DecidableEq

/-- The two model-owned requiredness policies. The first is absolute only without a repeatable ancestor; otherwise it is gated by the nearest repeatable ancestor. -/
inductive RequirednessMode where
  | absoluteOrNearestRepeatableAncestor
  | relativeToParent
  deriving Repr, DecidableEq

namespace SurfaceLiteral

def kind : SurfaceLiteral → SurfaceScalarKind
  | .number _ => .number
  | .boolean _ => .boolean
  | .string _ => .string
  | .date _ _ => .temporal .date

end SurfaceLiteral

inductive SurfaceCondition where
  | compare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
      (literal : SurfaceLiteral)
  | compareFields (op : SurfaceComparisonOp) (left right : SurfaceFieldPath)
  | compareTextFields (op : SurfaceComparisonOp)
      (left right : SurfaceTextFieldOperand)
  | compareToday (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
      (field : SurfaceFieldPath)
  | compareBaseYear (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
      (field : SurfaceFieldPath)
  | compareBaseYearRange (op : SurfaceComparisonOp)
      (position : SurfacePointInTimePosition) (endpoint : BaseYearRangeEndpoint)
      (field : SurfaceFieldPath)
  | compareNow (op : SurfaceComparisonOp) (position : SurfacePointInTimePosition)
      (field : SurfaceFieldPath)
  | compareEnumeration (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
      (projection : EnumerationProjectionRef) (literal : String)
  | enumerationValueList (quantifier : ValueListQuantifier)
      (fields : List SurfaceTextFieldOperand) (values : List String)
  | enumerationFieldValueList (quantifier : ValueListQuantifier)
      (fields values : List SurfaceTextFieldOperand)
  | stringValueList (quantifier : ValueListQuantifier)
      (fields : List SurfaceFieldPath) (values : List String)
  | stringFieldValueList (quantifier : ValueListQuantifier)
      (fields values : List SurfaceFieldPath)
  | stringValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List String)
  | stringFieldValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List SurfaceFieldPath)
  | numberValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List Int)
  | numberFieldValueMembership (op : ValueListMembershipOp)
      (field : SurfaceFieldPath) (values : List SurfaceFieldPath)
  | numberFieldValueList (quantifier : ValueListQuantifier)
      (fields values : List SurfaceFieldPath)
  | enumerationValueMembership (op : ValueListMembershipOp)
      (field : SurfaceTextFieldOperand) (values : List String)
  | enumerationFieldValueMembership (op : ValueListMembershipOp)
      (field : SurfaceTextFieldOperand) (values : List SurfaceTextFieldOperand)
  | lengthCompare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
      (literal : DecodedNumericLiteral)
  | literalCompareLength (literal : DecodedNumericLiteral)
      (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
  | fieldFilled (field : SurfaceFieldPath)
  | fieldNotFilled (field : SurfaceFieldPath)
  | and (left right : SurfaceCondition)
  | or (left right : SurfaceCondition)
  deriving Repr, DecidableEq

/-- One expanded field declaration. `repeatableScope` lists every repeatable ancestor;
    the current capsule accepts exactly the empty list. -/
structure FlatFieldDecl where
  id : FieldId
  groupPath : GroupPath
  name : String
  policy : FieldPolicy
  stringValueMode : StringValueMode := .evaluated
  stringPolicy : StringFieldPolicy := {}
  /-- Exact declared pattern source retained independently of condition-pattern execution. String-value consumers receive the declaration capability here and rely on their prepared or caller-checked context for pattern execution. -/
  stringPatternSource : Option String := none
  customType : Option CustomFieldTypeDeclaration := none
  enumeration : Option EnumerationDeclaration := none
  /-- A global field is auto-added with all repetition indices wildcarded to every partial-validation relevant set before rule admission or condition reads. -/
  isGlobal : Bool := false
  /-- Absence means that this field has no model-declared generated mandatory rule. -/
  requiredness : Option RequirednessMode := none
  /-- Resolved Number declaration constraints shared by stored-input checking and computed-target checking. Scale and signedness remain in `policy.kind`; leading-zero permission is input-only. -/
  numericTargetConstraints : NumericTargetConstraints :=
    NumericTargetConstraints.unconstrained
  /-- Complete resolved temporal policy for consumers that need exact stored format, partial precision, or the additional Date check. Absence keeps ordinary temporal reads available but makes such consumers explicitly insufficient. -/
  temporalTargetPolicy : Option TemporalTargetPolicy := none
  /-- Exact already-classified DateRange format and separator sources. Decoded endpoint values do not retain presentation policy. -/
  dateRangePolicy : Option DateRangeDeclarationPolicy := none
  repeatableScope : List RepeatableLevel := []
  deriving Repr, DecidableEq

namespace FlatFieldDecl

def path (declaration : FlatFieldDecl) : List String :=
  declaration.groupPath ++ [declaration.name]

/-- The exact model-owned capability used by every checked String value consumer. Presence deliberately does not use this projection. -/
def toStringValueField? (declaration : FlatFieldDecl) : Option FlatStringField :=
  match declaration.policy.kind, declaration.stringValueMode with
  | .string, .evaluated => some { id := declaration.id }
  | _, _ => none

def isRawString (declaration : FlatFieldDecl) : Bool :=
  declaration.policy.kind == .string && declaration.stringValueMode == .raw

/-- Convert one expanded declaration to the shared resolved Number-field representation. -/
def toNumberField? (declaration : FlatFieldDecl) : Option FlatNumberField :=
  match declaration.policy.kind with
  | .number info => some { id := declaration.id, info }
  | .boolean | .confirm | .string | .enumeration | .temporal _ _ | .dateRange => none

/-- Whether a Number declaration admits only nonnegative values by signedness or an explicit lower bound. Date and Time constructor fields share this exact static condition. -/
def numberDomainNonnegative (declaration : FlatFieldDecl)
    (source : FlatNumberField) : Bool :=
  if source.info.signed then
    match declaration.numericTargetConstraints.minimum with
    | some minimum => decide (0 ≤ minimum)
    | none => false
  else
    true

/-- Construct the complete computed-Number target policy from this declaration without accepting caller-supplied constraints. -/
def toNumericTargetPolicy? (declaration : FlatFieldDecl) :
    Option NumericTargetPolicy :=
  match declaration.policy.kind with
  | .number info => declaration.numericTargetConstraints.toPolicy? info
  | .boolean | .confirm | .string | .enumeration | .temporal _ _ | .dateRange => none

/-- Convert one expanded declaration to the shared resolved temporal-field representation. -/
def toTemporalField? (declaration : FlatFieldDecl) : Option FlatTemporalField :=
  match declaration.policy.kind with
  | .temporal kind components => some { id := declaration.id, kind, components }
  | .number _ | .boolean | .confirm | .string | .enumeration | .dateRange => none

/-- Recover the complete checked temporal-target policy only when it agrees with this declaration's kind and component shape. -/
def toTemporalTargetPolicy? (declaration : FlatFieldDecl) :
    Option TemporalTargetPolicy :=
  match declaration.policy.kind, declaration.temporalTargetPolicy with
  | .temporal kind components, some policy =>
      if policy.errorFor? kind components == none then some policy else none
  | _, _ => none

/-- Convert one DateRange declaration to its resolved field identity. -/
def toDateRangeField? (declaration : FlatFieldDecl) : Option FlatDateRangeField :=
  match declaration.policy.kind with
  | .dateRange => some { id := declaration.id }
  | .number _ | .boolean | .confirm | .string | .enumeration | .temporal _ _ => none

/-- Recover the exact checked DateRange declaration policy only when it belongs to this kind and satisfies the parser-independent invariants. -/
def toDateRangeDeclarationPolicy? (declaration : FlatFieldDecl) :
    Option DateRangeDeclarationPolicy :=
  match declaration.policy.kind, declaration.dateRangePolicy with
  | .dateRange, some policy =>
      if policy.error? == none then some policy else none
  | _, _ => none

def toPresenceField (declaration : FlatFieldDecl) : FlatField :=
  match declaration.policy.kind with
  | .number info => .number { id := declaration.id, info }
  | .boolean => .boolean { id := declaration.id }
  | .confirm => .confirm { id := declaration.id }
  | .string => .string { id := declaration.id }
  | .enumeration => .enumeration { id := declaration.id }
  | .temporal kind components =>
      .temporal { id := declaration.id, kind, components }
  | .dateRange => .dateRange { id := declaration.id }

/-- Resolve one exact stored/category projection from a legal Enumeration declaration for direct textual comparison. Category access is statically exempt from display-remapping compatibility. -/
def toEnumerationTextFieldComparison? (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .ok checked =>
          match checked.resolveProjection projectionRef with
          | .ok projection =>
              let profile := match projectionRef with
                | .stored => checked.directComparableField
                | .category _ => .category
              some (.enumeration {
                field := { id := declaration.id }
                projectionRef
                projection }, profile)
          | .error _ => none
      | .error _ => none
  | _, _ => none

/-- Resolve one legal direct String/Enumeration declaration to its stored-value runtime operand and independent static-comparability profile. -/
def toTextFieldComparison? (declaration : FlatFieldDecl) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  match declaration.toStringValueField?, declaration.policy.kind,
      declaration.enumeration with
  | some field, .string, none => some (.string field, .plainString)
  | none, .enumeration, some _ => declaration.toEnumerationTextFieldComparison? .stored
  | _, _, _ => none

def textComparisonProfileFor? (declaration : FlatFieldDecl)
    (operand : FlatTextFieldOperand) : Option DirectComparableField :=
  let resolved := match operand with
    | .string _ => declaration.toTextFieldComparison?
    | .enumeration operand =>
        declaration.toEnumerationTextFieldComparison? operand.projectionRef
  resolved.bind fun (checkedOperand, profile) =>
    if checkedOperand == operand then some profile else none

end FlatFieldDecl

/-- One repeatable model level with the exact group path on which `*` may be written. A field's `repeatableScope` alone cannot identify that path segment. -/
structure RepeatableGroupDecl where
  level : RepeatableLevel
  path : GroupPath
  /-- Declared maximum row count when the staged model boundary retains it.

  `none` is a **staging** absence, never an unbounded group: a Kernel-valid model always
  declares a finite maximum strictly greater than zero — `1` included — and a group declaring none
  is nonrepeatable rather than unbounded
  ([checkpoint](../../../docs/SOURCES.md#src-repeatability-domain-peer-measurement)).
  Every consumer keeping a `none` branch therefore answers a shape no authorable model reaches;
  keep those branches total and do not write a clause that depends on their unreachability. -/
  repeatability : Option Nat := none
  /-- The unique direct-child field used for semantic row selection, when declared. -/
  indexField : Option FieldId := none
  deriving Repr, DecidableEq

structure FlatModel where
  fields : List FlatFieldDecl
  repeatableGroups : List RepeatableGroupDecl := []
  fieldRefByShortNameAllowed : Bool := false
  baseYear : Option Int := none
  /-- Exact legacy zone id already admitted by the upstream model checker. Absent model configuration is normalized to UTC. -/
  timeZoneId : String := "UTC"
  deriving Repr, DecidableEq

def FlatModel.hasBaseYear (model : FlatModel) : Bool := model.baseYear.isSome

/-- The resolved gate of a model-declared required field. -/
inductive RequirednessScope where
  | absolute
  | relativeTo (groupPath : GroupPath)
  deriving Repr, DecidableEq

/-- Where the written field lies relative to the group declaring its computation or rule. The Kernel
    asks this containment question first of every read that leaves a repeatable level unstarred,
    whatever binds that level
    ([inbound](../../../docs/SOURCES.md#inbound-2026-09-24d-star-containment)). -/
inductive WrittenFieldPlacement where
  /-- At or below the declaring group. -/
  | contained
  /-- Outside it, including a declaring group beside the written field's own. -/
  | outside
  deriving Repr, DecidableEq

/-- The index gates a level beside the written field's group meets when the written field lies
    inside the declaring group and both the level's group and the written field's path declare an
    index field ([`kf371`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)). The order among
    the three refusals has no separating row: `kf371` reads it from source. -/
inductive ParallelIndexGate where
  /-- The level is not such a level. -/
  | notReached
  /-- Another keyed group lies above it on the operand's own chain, beside the written path. -/
  | multipleIndexFields
  /-- The two index fields differ in name. -/
  | differentName
  /-- They share a name and differ in a pair of kinds a row separates,
      `SurfaceScalarKind.measuredIndexTypeSplit`. -/
  | differentType
  /-- They share a name and a kind: a legal parallel iteration, which the Kernel admits. -/
  | legal
  /-- A shape no row measures: a keyed group both chains share, a second keyed group on the written
      path, one base type under two different kinds, or any other pair of differing kinds. -/
  | unmeasured
  deriving Repr, DecidableEq

/-- A repeatable level a read leaves for its evaluation to bind where the written field does not
    bind it
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
structure UnboundOperandLevel where
  level : RepeatableLevel
  placement : WrittenFieldPlacement
  /-- The level's group lies beside the written field's group, neither below it nor holding it. -/
  parallel : Bool
  /-- The level's group declares an index field. -/
  indexKeyed : Bool
  /-- A repeatable group on the written field's own path declares an index field. -/
  writtenPathKeyed : Bool := false
  /-- The index gate a parallel level meets when both chains are keyed, `notReached` for any other. -/
  parallelGate : ParallelIndexGate := .notReached
  /-- Inside the declaring group, the level's group holds the written field, so the written field
      binds the level and the Kernel admits the read
      ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)).
      A caller that evaluates at a narrower scope still cannot bind it. -/
  writtenBound : Bool := false
  deriving Repr, DecidableEq

/-- Whether the Kernel admits this level as one side of a legal parallel iteration. The walk then
    asks the next level of the same read ([`kf371`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)). -/
def UnboundOperandLevel.parallelIterable (unbound : UnboundOperandLevel) : Bool :=
  unbound.parallelGate == .legal

/-- Whether the walk asks the next level of the read after this one: a legal parallel iteration, or
    a level the written field binds. -/
def UnboundOperandLevel.passesWalk (unbound : UnboundOperandLevel) : Bool :=
  unbound.parallelIterable || unbound.writtenBound

/-- Containment when the written field lies outside the declaring group, whatever the level. Inside
    it, a level parallel to the written field's group draws the index class when it declares an index
    field and the written field's path declares none, and every other level the missing-star class,
    so an index below the written field's group moves nothing
    ([inbound](../../../docs/SOURCES.md#inbound-2026-09-24d-star-containment)). With both chains
    keyed the level meets its index gates
    ([`kf371`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf371)). A legal parallel iteration,
    a level the written field binds, and a shape no row measures claim no class: the Kernel admits
    the first two, and a route refusing them refuses a read it does not evaluate. The written path's
    index is asked before the level's own chain, the reverse of `kf371`'s source-read order; the
    outermost-first walk reaches no measured row where the two orders differ. -/
def UnboundOperandLevel.diagnostic? (unbound : UnboundOperandLevel) :
    Option KernelStaticDiagnostic :=
  match unbound.placement with
  | .outside => some .fieldNotInRuleGroup
  | .contained =>
      if unbound.writtenBound then none
      else if unbound.parallel && unbound.indexKeyed then
        if unbound.writtenPathKeyed then
          match unbound.parallelGate with
          | .multipleIndexFields => some .multipleIndexFields
          | .differentName => some .errorFieldInvalidIndex
          | .differentType => some .errorFieldInvalidIndexType
          | .notReached | .legal | .unmeasured => none
        else some .errorFieldNoIndex
      else some .noWildcard

/-- Why a presence predicate's field slot naming a group is refused, in the Kernel's gate order: the
    repetition walk, then a root's own class, then the kind gate
    ([inbound](../../../docs/SOURCES.md#inbound-2026-09-24c-field-slot)). -/
inductive GroupFieldSlotRefusal where
  /-- The group crosses a repeatable level the reading rule does not bind. -/
  | unboundLevel (unbound : UnboundOperandLevel)
  /-- A root the walk passes: a fixed root, or a repeatable one the reading rule sits in. -/
  | root
  /-- Any other group, which the walk passes and the kind gate refuses. -/
  | group
  deriving Repr, DecidableEq

def GroupFieldSlotRefusal.diagnostic? : GroupFieldSlotRefusal → Option KernelStaticDiagnostic
  | .unboundLevel unbound => unbound.diagnostic?
  | .root => some .rootGroupReferenced
  | .group => some .noGroupsAllowed

inductive ResolveError where
  | invalidModelPath (path : List String)
  | duplicateFieldId (id : FieldId)
  | duplicateEntityPath (path : List String)
  | customTypeRequiresString (path : List String)
  | rawValueModeRequiresString (path : List String)
  | rawValueModeForbidsCustomType (path : List String)
  | stringPolicyRequiresString (path : List String)
  | stringPolicyForbidsCustomType (path : List String)
  | stringPatternRequiresString (path : List String)
  | stringPatternForbidsCustomType (path : List String)
  | numericTargetConstraintsRequireNumber (path : List String)
  | numericMinimumFractionalDigitsExceedMaximum (path : List String)
      (minimum maximum : Nat)
  -- `fieldScaleCap`: the kernel refuses a declared scale above 14 with a plain MVK-less model
  -- check. Distinct from `maxRoundingPlaces`, which bounds a rounding *argument* at the same
  -- number; `spec/04` names all seven digit quantities separately for exactly this reason.
  | numericFractionalDigitsAboveCap (path : List String) (declared cap : Nat)
  | numericMaximumIntegerDigitsZero (path : List String)
  | temporalTargetPolicyRequiresTemporal (path : List String)
  | invalidTemporalTargetPolicy (path : List String)
      (error : TemporalTargetPolicyError)
  | dateRangeDeclarationPolicyRequired (path : List String)
  | dateRangeDeclarationPolicyRequiresDateRange (path : List String)
  | invalidDateRangeDeclarationPolicy (path : List String)
      (error : DateRangeDeclarationPolicyError)
  | rawStringRequiresLineBreakPermission (path : List String)
  | rawStringForbidsMinimumLength (path : List String)
  | rawStringForbidsPattern (path : List String)
  | stringMinimumExceedsMaximum (path : List String)
  | lineBreakWithSingleCharacterMaximum (path : List String)
  | enumerationMetadataRequiresEnumeration (path : List String)
  | enumerationDeclarationRequired (path : List String)
  | invalidEnumerationDeclaration (path : List String)
      (error : EnumerationDeclarationError)
  | invalidRepeatableGroupPath (path : GroupPath)
  | duplicateRepeatableGroupPath (path : GroupPath)
  | duplicateRepeatableLevel (level : RepeatableLevel)
  | invalidIndexField (groupPath : GroupPath) (field : FieldId)
  | entityHierarchyCollision (fieldPath groupPath : GroupPath)
  | repeatableScopeMismatch (path : List String)
      (expected actual : List RepeatableLevel)
  | unknownRepeatableGroup (path : GroupPath)
  | unknownFieldId (id : FieldId)
  | invalidRuleGroup (path : GroupPath)
  | invalidReference (reference : SurfaceFieldPath)
  | aboveRoot (parents : Nat)
  | invalidEntity (reference : SurfaceFieldPath)
  -- `unknownRootGroup`: an absolute path whose first segment names no declared root is its own
  -- class, reported whatever the rest of the path says, so it is checked before the path's shape
  -- and lookup. A lone segment is included, since the Kernel reads it as a root first.
  | unknownRootGroup (reference : SurfaceFieldPath)
  | ambiguousEntity (path : List String)
  | shortNameNotUnique (name : String)
  | repeatableReference (path : List String)
  -- `unboundOperandLevel`: an operand with a repeatable level its reader does not bind, a fixed
  -- computation target or a validation rule group, carrying what selects the Kernel's class.
  | unboundOperandLevel (path : List String) (unbound : UnboundOperandLevel)
  -- `boundRepeatableReference`: a repeatable operand whose every level the reading rule already
  -- iterates, refused by a fragment that reads nonrepeatable operands only. The Kernel admits that
  -- read, so this is the fragment's boundary rather than `repeatableReference`'s missing wildcard.
  | boundRepeatableReference (path : List String)
  -- `reservedRootGroupName`: A12 reserves exactly one whole name, case-insensitively, and only on
  -- the root carrier. This is a name equality rather than an alphabet rule, which is why it sits
  -- apart from every other name check; `spec/01` §3 names the carriers.
  | reservedRootGroupName (name : String)
  -- `repeatabilityAboveCap`: the ceiling is the declaring carrier's, not one global bound. A single
  -- bound would refuse a legal nested group or accept an illegal root one.
  | repeatabilityAboveCap (path : List String) (declared cap : Nat)
  -- `groupInFieldSlot`: a presence predicate's field operand whose path names a declared group. It
  -- keeps the field miss it displaces, which the versioned public protocol still reports.
  | groupInFieldSlot (path : GroupPath) (refusal : GroupFieldSlotRefusal) (fieldMiss : ResolveError)
  deriving Repr, DecidableEq

/-- The Kernel class a resolution failure reports, projected once for every wrapping error type.
An unstarred repeatable operand read from a rule locus that does not iterate its level is the
shared missing-wildcard class. From a locus that iterates every level of it the Kernel admits the
read, so a fragment refusing it reports `boundRepeatableReference`, which carries no class
([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)).
A computation operand into a fixed target, and a validation read placed by its error field, report
`unboundOperandLevel` instead, whose class the written field's position and the outermost unbound
level select.

**This is the one projection that keeps a wildcard, deliberately.** Elsewhere a `_ => none` arm is
the anti-pattern this estate sweeps out, because it silently absorbs a form a later change adds and
hides whether the silence is a local boundary or an unmeasured Kernel refusal. Here the denominator
is 42 arms and all but a handful are **model-declaration validity** failures — a duplicate field id,
a raw String carrying a pattern, an enumeration without a declaration — reached while building the
flat model rather than while refusing a rule. A new arm is overwhelmingly one of those, so the
compile error an exhaustive list would raise is noise in the case that matters least and the list
itself would obscure the arms that do carry a class. Add an explicit arm the moment a resolution
failure is measured to report an `MVK_` class.

The three name-resolution arms were measured together on 2026-09-23 across eight condition carriers
and two computation carriers, each reporting the same class for the same failure, which is what makes
them the resolver's rather than any carrier's
([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)).
The short-name ambiguity arm was measured the same way on 2026-09-24, on five condition carriers and
a computation
([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-short-name-ambiguity-every-carrier)). -/
def ResolveError.diagnostic? : ResolveError → Option KernelStaticDiagnostic
  | .repeatableReference _ => some .noWildcard
  | .unboundOperandLevel _ unbound => unbound.diagnostic?
  | .invalidEntity _ => some .invalidEntity
  | .unknownRootGroup _ => some .invalidRootGroup
  | .aboveRoot _ => some .tooManyParentGroups
  | .shortNameNotUnique _ => some .fieldNameNotUnique
  | .numericMinimumFractionalDigitsExceedMaximum _ _ _ => some .fractDigitsInvalid
  | .groupInFieldSlot _ refusal _ => refusal.diagnostic?
  | _ => none

inductive AuthoredFieldPathError where
  | syntax (error : PathSyntaxError)
  | resolve (error : ResolveError)
  deriving Repr, DecidableEq

inductive ElabError where
  | resolve (error : ResolveError)
  | unsupportedOperator (op : SurfaceComparisonOp)
  | literalKindMismatch (path : List String) (expected actual : SurfaceScalarKind)
  | illegalConfirmLiteral (path : List String)
  | temporalOperandKindMismatch (leftPath rightPath : List String)
      (leftKind rightKind : SurfaceScalarKind)
  | temporalFormatsIncompatible (leftPath rightPath : List String)
  | temporalNowRequiresTime (path : List String)
  | baseYearNotDeclared
  | baseYearScaleMismatch (path : List String) (fieldScale : Nat)
  | temporalLiteralNeedsBaseYear (path : List String)
  | invalidTemporalLiteralComponents (path : List String)
  | rawStringValue (path : List String)
  | rawStringLength (path : List String)
  | rawStringLengthBound (path : List String)
  | lengthOperandKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | enumerationOperand (path : List String) (error : EnumerationOperandError)
  | textFieldOperandKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | emptyValueList (path : List String)
  | emptyValueListFields
  | emptyValueListValueFields
  | duplicateValueListField (path : List String)
      (projectionRef : EnumerationProjectionRef)
  | duplicateStringValueListField (path : List String)
  | duplicateNumberValueListField (path : List String)
  | enumerationComparability (leftPath rightPath : List String)
      (error : EnumerationComparabilityError)
  | incoherentCore
  deriving Repr, DecidableEq

end A12Kernel
