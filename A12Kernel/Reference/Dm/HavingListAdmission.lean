import A12Kernel.Reference.Dm.LowerHaving
import A12Kernel.Elaboration.NumericComputation.OperationTyping

namespace A12Kernel.Dm.HavingListAdmission

/-- The temporal list operators share an ordered precision/component gate, unlike scalar extrema.
Base-year supplementation belongs here, after all authored reads (CheckEntityListenUtils;
spec/05 §3, partial-date and component-set admission). -/
def checkRawTemporalList (model : FlatModel) (expected : TemporalComponents)
    (declarations : List FlatFieldDecl) : Lowering Unit := do
  for declaration in declarations do
    let .temporal _ components := declaration.policy.kind |
      refuse "Having" KernelStaticDiagnostic.dateAndNonDate.kernelCode
    let some policy := declaration.toTemporalTargetPolicy? |
      refuse "Having" "unsupported temporal list policy"
    if policy.partialMode != .full then
      refuse "Having" KernelStaticDiagnostic.partialDateNotAllowed.kernelCode
    if components.supplementedByBaseYear model.hasBaseYear !=
        expected.supplementedByBaseYear model.hasBaseYear then
      refuse "Having" KernelStaticDiagnostic.dateFormatsNotCompatible.kernelCode

/-- Distinct-count admission follows the first expanded declaration's family. Token membership
precedes the raw-string gate; temporal membership, precision and component checks interleave in
declaration order (CheckFeldListenAnzahlOpImpl; CheckEntityListenUtils; spec/05). -/
def checkRawDistinctTypes (model : FlatModel) (declarations : List FlatFieldDecl) : Lowering Unit := do
  let first :: _ := declarations | refuse "Having" "empty distinct-count expansion"
  match first.policy.kind with
  | .string | .enumeration =>
      if !declarations.all (fun declaration => match declaration.policy.kind with
          | .string | .enumeration => true | _ => false) then
        refuse "Having" KernelStaticDiagnostic.stringEnumAndNonStringEnum.kernelCode
      if declarations.any (·.isRawString) then
        refuse "Having" KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
  | .number _ =>
      if !declarations.all (fun declaration => match declaration.policy.kind with
          | .number _ => true | _ => false) then
        refuse "Having" KernelStaticDiagnostic.numberAndNonNumber.kernelCode
  | .temporal _ expected => checkRawTemporalList model expected declarations
  | _ => refuse "Having" KernelStaticDiagnostic.onlyStringEnumNumberCmpDateAllowed.kernelCode


inductive RawListKey where
  | literal (spelling : String)
  | field (id : FieldId) (captured : Bool)
  deriving BEq

/-- Static list admission retains authored identity separately from runtime selection certificates.
Literal spellings, resolved key fields and categories participate in duplicate checks; lookup
normalization does not (SemanticIndexRef.equals; EntityRef.equals; spec/08 §4). -/
structure RawListRead where
  reference : Reference
  entity : Sum FlatFieldDecl GroupPath
  key : Option RawListKey

def RawListRead.path (read : RawListRead) : GroupPath :=
  match read.entity with | .inl declaration => declaration.path | .inr path => path

def RawListRead.isMany (read : RawListRead) : Bool :=
  read.entity.isRight || read.reference.path.segments.any (·.star)

def RawListRead.declarations (read : RawListRead) (model : FlatModel) : List FlatFieldDecl :=
  match read.entity with | .inl declaration => [declaration] | .inr path => model.groupSubtreeFields path

def checkRawListDuplicates (reads : List RawListRead) : Lowering Unit := do
  let identity := fun read =>
    if read.reference.path.segments.any (·.star) then none
    else some (read.reference.path.correlated, read.path, read.key, read.reference.category)
  if (firstDuplicateInEncounterOrder? identity reads).isSome then
    refuse "Having" KernelStaticDiagnostic.duplicateParam1.kernelCode
  for left in reads do
    if reads.any (fun right => left.key == right.key &&
        left.reference.category == right.reference.category &&
        entityListPathsOverlap left.path right.path left.entity.isRight right.entity.isRight) then
      refuse "Having" KernelStaticDiagnostic.duplicateParam2.kernelCode

def checkRawListRoots (reads : List RawListRead) (allowSole : Bool := false) : Lowering Unit := do
  if reads.any (fun read => read.entity.isRight && read.path.length == 1) then
    if allowSole then
      if reads.length > 1 then refuse "Having" KernelStaticDiagnostic.rootGroupWithOtherParameters.kernelCode
    else refuse "Having" KernelStaticDiagnostic.rootGroupReferenced.kernelCode

/-- Keys and the optional scope have already completed their reads. The parent then applies
whole-list gates before choosing its reference-group branch (CheckWiederholungBedingungImpl;
spec/07 §6). The enclosing filter walk owns the later forbidden-construct check. -/
def checkRawRepetition (model : FlatModel) (group : GroupPath) (keys : List RawListRead)
    (scope : Option RawListRead) : Lowering Unit := do
  if keys.isEmpty then refuse "Having" "empty repetition keys"
  checkRawListDuplicates keys
  if keys.any (·.reference.category.isSome) then refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  if keys.any (·.entity.isRight) then refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if keys.any (fun key => key.reference.path.segments.any (·.star)) then
    refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  if keys.any (·.key.isSome) then refuse "Having" KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
  let declarations := keys.flatMap (·.declarations model)
  if declarations.any (·.isRawString) then refuse "Having" KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
  if let some scope := scope then
    if scope.entity.isLeft then refuse "Having" KernelStaticDiagnostic.noFieldsAllowed.kernelCode
    if scope.reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    if scope.key.isSome then refuse "Having" KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
  discard <| (checkRepetitionReferenceAdmission model group declarations
    (scope.map fun read => (read.path, read.entity.isLeft))).mapError fun error =>
      { construct := "Having", detail := error.diagnostic?.map (·.kernelCode) |>.getD (oneLine ((repr error).pretty 100000)) }

private def checkMembershipBase (expected : SurfaceScalarKind) (fields : List FlatFieldDecl) : Lowering Unit := do
  if !fields.all (fun field => expected.sharesValueListBaseType field.policy.kind.surfaceKind) then
    refuse "Having" KernelStaticDiagnostic.varyingTypesNotAllowed.kernelCode

private def checkMembershipDomain (kind : SurfaceScalarKind) : Lowering Unit := do
  if kind != .number && kind != .string && kind != .enumeration then
    refuse "Having" KernelStaticDiagnostic.onlyStringEnumNumberAllowed.kernelCode

private def checkMembershipRaw (fields : List FlatFieldDecl) : Lowering Unit := do
  if fields.any (·.isRawString) then refuse "Having" KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode

private def checkListDeclarations (result : Except CorrelationElabError Unit) : Lowering Unit :=
  result.mapError fun error =>
    { construct := "Having", detail := error.diagnostic?.map (·.kernelCode) |>.getD (oneLine ((repr error).pretty 100000)) }

/-- All-pairs overlap and uniqueness share list identity, root and category gates. Their
multiplicity and type policies remain distinct (CheckFeldListenBedingungImpl; spec/07 §5). -/
def checkRawListCondition (model : FlatModel) (overlap : Bool) (reads : List RawListRead) : Lowering Unit := do
  checkRawListDuplicates reads
  checkRawListRoots reads
  if reads.any (·.reference.category.isSome) then refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  if overlap && reads.any (·.entity.isRight) then refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if reads.length < 2 && !reads.any (·.isMany) then
    refuse "Having" (if overlap then KernelStaticDiagnostic.paramSizeInvalidFN else .paramSizeInvalidN).kernelCode
  let expansions := reads.map (·.declarations model)
  checkListDeclarations (if overlap then checkHavingOverlapDeclarations model expansions
    else checkHavingUniquenessDeclarations expansions.flatten)

/-- Scalar-versus-list overlap checks the subject's base and shape before the member list;
member base agreement precedes cross-list duplication. Categories receive no separate gate
(CheckFeldListeUndWerteListenBedingungImpl; spec/05 §8). -/
def checkRawOverlapMembers (model : FlatModel) (subjects : List RawListRead)
    (members : Option (List RawListRead)) : Lowering Unit := do
  checkRawListDuplicates subjects
  checkRawListRoots subjects
  let fields := subjects.flatMap (·.declarations model)
  let first :: _ := fields | refuse "Having" "empty overlap subjects"
  let kind := first.policy.kind.surfaceKind
  checkMembershipBase kind fields
  if subjects.length != 1 || subjects.any (·.isMany) then
    refuse "Having" KernelStaticDiagnostic.invalidParameterForDateRangeComparison.kernelCode
  checkMembershipRaw fields
  let some members := members | refuse "Having" KernelStaticDiagnostic.noConst.kernelCode
  checkRawListDuplicates members
  checkRawListRoots members
  let values := members.flatMap (·.declarations model)
  checkMembershipBase kind values
  checkRawListDuplicates (subjects ++ members)
  checkMembershipRaw values
  checkListDeclarations (checkHavingOverlapDeclarations model ((subjects ++ members).map (·.declarations model)))

private def checkRawMembershipSubjects (model : FlatModel) (scalar : Bool)
    (subjects : List RawListRead) : Lowering SurfaceScalarKind := do
  let fields := subjects.flatMap (·.declarations model)
  let first :: _ := fields | refuse "Having" "empty membership subjects"
  let kind := first.policy.kind.surfaceKind
  if scalar then
    if subjects.any (·.entity.isRight) then refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    if subjects.any (fun read => read.reference.path.segments.any (·.star)) then
      refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  else
    checkRawListDuplicates subjects
    checkRawListRoots subjects
    checkMembershipBase kind fields
  checkMembershipDomain kind
  checkMembershipRaw fields
  return kind

/-- Membership list gates run after all own reads. Scalar membership checks the combined list
before member types; quantified membership checks each list's type before cross-list duplication
(CheckFeldUndWerteListenBedingungImpl; CheckFeldListeUndWerteListenBedingungImpl; spec/06 §B.3). -/
def checkRawMembershipFields (model : FlatModel) (scalar : Bool)
    (subjects members : List RawListRead) : Lowering Unit := do
  let kind ← checkRawMembershipSubjects model scalar subjects
  let values := members.flatMap (·.declarations model)
  if scalar then checkRawListDuplicates (members ++ subjects)
  else
    checkRawListDuplicates members
    checkRawListRoots members
  checkMembershipBase kind values
  if !scalar then checkRawListDuplicates (subjects ++ members)
  checkMembershipRaw values

private def rawEnumerationLiteralAllowed (model : FlatModel) (declaration : FlatFieldDecl)
    (category : Option String) (value : String) : Bool :=
  let projection := category.map EnumerationProjectionRef.category |>.getD .stored
  (declaration.toEnumerationTextFieldComparison? projection).any fun (operand, _) => match operand with
    | .enumeration operand => (model.checkedEnumerationOperandIn? declaration.repeatableScope operand).any fun checked =>
        checked.declaration.literalAllowed checked.projection value
    | _ => false

/-- Literal membership uses the selected Enumeration domains, including categories, and the
quantified form uses their union (spec/06 §B.3; CheckWerteListenUtils.checkEnumValues). -/
def checkRawMembershipLiterals (model : FlatModel) (scalar : Bool) (subjects : List RawListRead)
    (values : List String) (numeric : Bool) : Lowering Unit := do
  let kind ← checkRawMembershipSubjects model scalar subjects
  if (kind == .number) != numeric then
    refuse "Having" KernelStaticDiagnostic.invalidTypesForComparison.kernelCode
  if kind != .enumeration then return
  let allows := fun value => subjects.any fun read => (read.declarations model).any fun declaration =>
    rawEnumerationLiteralAllowed model declaration read.reference.category value
  if !values.all allows then
    let diagnostic := if !scalar then KernelStaticDiagnostic.invalidStringConstantForEnumerationOrCategory
      else if subjects.any (·.reference.category.isSome) then .invalidStringConstantForEnumerationCategory
      else .invalidStringConstantForEnumeration
    refuse "Having" diagnostic.kernelCode

/-- Value counting checks duplicate/arity/root shape before its constant-selected declaration
scan. String domains precede raw-string and temporal-literal refusal; Boolean labels are the
represented default profile (CheckAnzahlWertOpImpl; CheckEntityListenUtils; spec/07 §3.5). -/
def checkRawValueCount (model : FlatModel) (reads : List RawListRead) (expected : Expr) : Lowering Unit := do
  checkRawListDuplicates reads
  if reads.length < 2 && !reads.any (·.isMany) then
    refuse "Having" KernelStaticDiagnostic.paramSizeInvalidN.kernelCode
  checkRawListRoots reads
  let declarations := reads.flatMap (·.declarations model)
  match expected with
  | .constant "True" =>
      if declarations.any (fun declaration => declaration.policy.kind != .boolean && declaration.policy.kind != .confirm) then
        refuse "Having" KernelStaticDiagnostic.noTypeYesOrYesNo.kernelCode
  | .constant "False" =>
      if declarations.any (fun declaration => declaration.policy.kind != .boolean) then
        refuse "Having" KernelStaticDiagnostic.noTypeYesNo.kernelCode
  | .number text =>
      if (decodeNumber? text).isNone then refuse "Having" KernelStaticDiagnostic.invalidConst.kernelCode
      if declarations.any (fun declaration => declaration.policy.kind.surfaceKind != .number) then
        refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
  | .string value =>
      for read in reads do
        for declaration in read.declarations model do
          match declaration.policy.kind with
          | .string => pure ()
          | .enumeration =>
              if !rawEnumerationLiteralAllowed model declaration read.reference.category value then
                refuse "Having" (if read.reference.category.isSome then
                  KernelStaticDiagnostic.invalidStringConstantForEnumerationCategory
                  else .invalidStringConstantForEnumeration).kernelCode
          | _ => refuse "Having" KernelStaticDiagnostic.noStringOrEnum.kernelCode
      checkMembershipRaw declarations
      if isTemporalConstant value then refuse "Having" KernelStaticDiagnostic.noDateConstant.kernelCode
  | _ => refuse "Having" KernelStaticDiagnostic.invalidConst.kernelCode

inductive RawGroupOperator where
  | presence
  | quantifier (op : GroupFillQuantifier)

/-- Group presence, quantifiers and counts share entity reads but have distinct ordered gates:
quantifiers permit field operands; singular presence checks stars before field-kind, while group
count checks semantic indexes first (CheckKontextListenBedingungImpl; spec/07 §5). -/
def checkRawGroupBody (operator : RawGroupOperator) (reads : List RawListRead) : Lowering Unit := do
  checkRawListDuplicates reads
  if reads.any (·.reference.category.isSome) then
    refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  match operator with
  | .presence =>
      if reads.length != 1 then refuse "Having" KernelStaticDiagnostic.paramSizeInvalid1.kernelCode
      if reads.any (fun read => read.reference.path.segments.any (·.star)) then
        refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
      if reads.any (·.entity.isLeft) then refuse "Having" KernelStaticDiagnostic.noFieldsAllowed.kernelCode
  | .quantifier op =>
      checkRawListRoots reads (!op.requiresMultipleOperands)
      if op.requiresMultipleOperands then
        if reads.length < 2 && !reads.any (fun read => read.reference.path.segments.any (·.star)) then
          refuse "Having" KernelStaticDiagnostic.paramSizeInvalid2.kernelCode
        -- A12's ignored final index is the field slot, not its parent group
        -- (EntityRef.hasWildCardsInGroup; EntityUtils.getMax).
        if reads.any (fun read => read.reference.path.segments.any (·.star)) then
          refuse "Having" KernelStaticDiagnostic.noWildcardsGAllowed.kernelCode

inductive RawListOperator where
  | aggregate (op : NumericAggregateOp)
  | filledCount
  | groupCount
  | firstFilled
  | product
  deriving DecidableEq

def rawListOperator? : String → Option RawListOperator
  | "NumberOfFilledFields" => some .filledCount
  | "NumberOfFilledGroups" => some .groupCount
  | "FirstFilledValue" => some .firstFilled
  | "SumOfProducts" => some .product
  | id => RawListOperator.aggregate <$> aggregateOp? id

private inductive RawFirstFilledProfile where
  | number | token | boolean
  | temporal (format : String)
  | dateRange (format : String)
  deriving DecidableEq

private def rawFirstFilledProfile (declaration : FlatFieldDecl) : Lowering RawFirstFilledProfile :=
  match declaration.policy.kind with
  | .number _ => pure .number
  | .string | .enumeration => pure .token
  | .boolean => pure .boolean
  | .confirm => refuse "Having" KernelStaticDiagnostic.noBoolyAllowed.kernelCode
  | .temporal .. => do
      let some policy := declaration.toTemporalTargetPolicy? | refuse "Having" "unsupported selector temporal policy"
      pure (.temporal policy.format)
  | .dateRange => do
      let some policy := declaration.toDateRangeDeclarationPolicy? | refuse "Having" "unsupported selector range policy"
      pure (.dateRange policy.format)

/-- First-filled compares operation families and declared formats, not distinct-count component
sets or precision. Confirm is rejected across the whole expansion before type agreement
(CheckFeldListenOpImpl; OperationResultType.matches; spec/05 §3). -/
def rawFirstFilledType (declarations : List FlatFieldDecl) : Lowering NumericOperandType := do
  if declarations.any (fun declaration => declaration.policy.kind == .confirm) then
    refuse "Having" KernelStaticDiagnostic.noBoolyAllowed.kernelCode
  let first :: rest := declarations | refuse "Having" "empty selector expansion"
  let profile ← rawFirstFilledProfile first
  let mut result := match first.policy.kind with
    | .enumeration => NumericOperandType.stringLike
    | _ => NumericOperandType.ofDeclaration first
  for declaration in rest do
    if (← rawFirstFilledProfile declaration) != profile then
      refuse "Having" KernelStaticDiagnostic.varyingTypesNotAllowed.kernelCode
    if let .number scale := result then
      let .number next := declaration.policy.kind | refuse "Having" "selector family mismatch"
      result := .number (scale.union (.field next.scale))
  pure result

/-- Product shape is checked after all reads and before Number typing. A filter restricts its
star; owning-group disagreement still precedes that restriction. Singleton capacities retain
star spelling independently of whether their level demands one (CheckEntityListenUtils;
spec/07 §3.8; the product operand-reach handback). -/
def rawProductType (model : FlatModel)
    (reads : List RawListRead) : Lowering NumericOperandType := do
  let fields ← reads.mapM fun read => do
    let .inl declaration := read.entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    pure (read.reference, declaration)
  let [(leftRef, left), (rightRef, right)] := fields |
    refuse "Having" KernelStaticDiagnostic.paramSizeInvalidTwo.kernelCode
  if left.groupPath != right.groupPath then
    refuse "Having" KernelStaticDiagnostic.differentGroups.kernelCode
  for (reference, declaration) in [(leftRef, left), (rightRef, right)] do
    let offset := declaration.path.length - reference.path.segments.length
    let mut foundStar := false
    for level in (model.repeatableScopeForGroupPath declaration.groupPath).reverse do
      let some group := model.repeatableGroupAtLevel? level | refuse "Having" "unresolved product level"
      let some capacity := group.repeatability | refuse "Having" "unsupported product capacity"
      let position := group.path.length - 1
      let starred := position >= offset && (reference.path.segments[position - offset]?).any (·.star)
      if !foundStar && capacity > 1 && (!starred || reference.filter.isSome) then
        refuse "Having" KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode
      if foundStar && starred then
        refuse "Having" KernelStaticDiagnostic.wildcardOnlyAtLowestLevelAllowed.kernelCode
      foundStar := foundStar || starred
    if !foundStar then refuse "Having" KernelStaticDiagnostic.repeatableLevelRequired.kernelCode
  let .number leftType := left.policy.kind | refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
  let .number rightType := right.policy.kind | refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
  pure (.number ((NumericScaleSummary.field leftType.scale).binary .multiply (.field rightType.scale)))


end A12Kernel.Dm.HavingListAdmission
