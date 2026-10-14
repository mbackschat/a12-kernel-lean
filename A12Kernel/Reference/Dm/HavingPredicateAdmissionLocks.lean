import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingPredicateAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Stamp", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy-MM-dd") },
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } },
    { id := 8, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 9, name := "Enum", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["keep", "drop"] } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def result (body : String) (row : Bool) (fixture : FlatModel := model) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") fixture row
private def validity := ["Valid", "Invalid"]
private def patterns := ["PatternMatched", "PatternViolated"]

example : model.validate.isOk = true ∧ [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let kind := KernelStaticDiagnostic.noStringOrEnumOrExtEnum.kernelCode
    let empty := KernelStaticDiagnostic.noEmpty.kernelCode
    validity.all (fun op =>
      result (op ++ "(Rows/Tag, \"Code\")") row == admitted &&
      result (op ++ "(Rows/Tag, \"\")") row == (empty, empty) &&
      result (op ++ "(Rows/Stamp, \"Code\")") row == (kind, kind) &&
      result (op ++ "(Rows/N, \"\")") row == (kind, kind))) = true := by native_decide

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let kind := KernelStaticDiagnostic.noStringOrEnumOrExtEnum.kernelCode
    let empty := KernelStaticDiagnostic.noEmpty.kernelCode
    let groups := KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    let stars := KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    validity.all (fun op =>
      result (op ++ "(Rows/Tag For \"keep\", \"Code\")") row == (indexed, indexed) &&
      result (op ++ "(Rows/Tag For \"keep\", \"\")") row == (empty, empty) &&
      result (op ++ "(Rows/Stamp For \"keep\", \"Code\")") row == (kind, kind) &&
      result (op ++ "(Rows, \"Code\")") row == (groups, groups) &&
      result (op ++ "(Rows*/Tag, \"Code\")") row == (stars, stars))) = true := by native_decide

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let kind := KernelStaticDiagnostic.invalidTypeForPatternComparison.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let constant := KernelStaticDiagnostic.missingConstantInPatternComparison.kernelCode
    patterns.all (fun op =>
      result ("[Rows/Tag] " ++ op ++ " \"[0-9]+\"") row == ("admitted", "admitted") &&
      result ("[Rows/Tag For \"keep\"] " ++ op ++ " \"[0-9]+\"") row == (indexed, indexed) &&
      result ("[Rows/N For \"keep\"] " ++ op ++ " \"[0-9]+\"") row == (kind, kind) &&
      result ("[Rows/N For \"keep\"] " ++ op ++ " [Missing]") row == (missing, missing) &&
      result ("[Rows/Tag For \"keep\"] " ++ op ++ " [Rows/Text]") row == (constant, constant) &&
      result ("[Rows/Enum For \"keep\"] " ++ op ++ " \"[0-9]+\"") row == (kind, kind))) = true := by native_decide

private def rawModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 8 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }

example : rawModel.validate.isOk = true ∧ [false, true].all (fun row =>
    let raw := KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
    let partialDate := KernelStaticDiagnostic.invalidDateType.kernelCode
    let kind := KernelStaticDiagnostic.invalidTypeForPatternComparison.kernelCode
    let constant := KernelStaticDiagnostic.missingConstantInPatternComparison.kernelCode
    let shape := KernelStaticDiagnostic.invalidParameterForPatternComparison.kernelCode
    let constants := KernelStaticDiagnostic.invalidCompareToConst.kernelCode
    validity.all (fun op =>
      result (op ++ "(Rows/Text, \"Code\")") row == ("admitted", "admitted") &&
      result (op ++ "(Rows/Text, \"\")") row rawModel == (raw, raw) &&
      result (op ++ "(Rows/Enum, \"Code\")") row == ("admitted", "admitted")) &&
    patterns.all (fun op =>
      result ("[Rows/Text] " ++ op ++ " \"[0-9]+\"") row rawModel == (raw, raw) &&
      result ("[Rows/Text] " ++ op ++ " [Missing]") row rawModel == (raw, raw) &&
      result ("[Rows/N] " ++ op ++ " [Rows/Text]") row rawModel == (raw, raw) &&
      result ("[Rows/Stamp] " ++ op ++ " \"[0-9]+\"") row == (partialDate, partialDate) &&
      result ("[Rows/Tag] " ++ op ++ " [Rows/Text]") row == (constant, constant) &&
      result ("[Rows/Tag] " ++ op ++ " 1") row == (kind, kind) &&
      result ("[Rows/Tag] " ++ op ++ " FirstFilledValue(Rows/Text, Rows/Tag)") row == (constant, constant) &&
      result ("FirstFilledValue(Rows/Text, Rows/Tag) " ++ op ++ " \"[0-9]+\"") row == (shape, shape) &&
      result ("\"x\" " ++ op ++ " \"[0-9]+\"") row == (constants, constants))) = true := by native_decide

example : [false, true].all (fun row =>
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let outer := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    validity.all (fun op =>
      result (preceding ++ op ++ "(Rows/Tag, \"Code\")") row ==
        (if row then (forbidden, forbidden) else (unbound, unbound)) &&
      result (preceding ++ op ++ "($Rows/Tag, \"Code\")") row == (outer, outer)) &&
    patterns.all (fun op =>
      result (preceding ++ "[Rows/Tag] " ++ op ++ " \"[0-9]+\"") row ==
        (if row then (forbidden, forbidden) else (unbound, unbound)) &&
      result (preceding ++ "[$Rows/Tag] " ++ op ++ " \"[0-9]+\"") row == (outer, outer))) = true := by native_decide

example : [false, true].all (fun row =>
    let kind := KernelStaticDiagnostic.invalidTypeForPatternComparison.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let stars := KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    -- The built-in compiler cannot judge Java syntax: `[` reaches compilation after every kind
    -- gate and stops at the host limit, not at the Kernel's invalid-pattern class.
    let hostLimit := (repr (CorrelationElabError.stringPattern (.pattern .hostUnsupported))).pretty 100000
    patterns.all (fun op =>
      result ("[Rows/N] " ++ op ++ " [Missing]") row == (missing, missing) &&
      result ("[Rows*/Tag Having FieldFilled(Rows/N)] " ++ op ++ " [Missing]") row == (stars, stars) &&
      result ("[Rows/Tag For \"keep\"] " ++ op ++ " \"[\"") row == (hostLimit, hostLimit) &&
      result ("[Rows/N For \"keep\"] " ++ op ++ " \"[\"") row == (kind, kind) &&
      result ("[Rows/Tag For \"keep\"] " ++ op ++ " \"01.03.2024\"") row == (kind, kind))) = true := by native_decide

private def customModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 8 then { field with customType := some { name := "Code" } } else field }

example : customModel.validate.isOk = true ∧ [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let kind := KernelStaticDiagnostic.noStringOrEnumOrExtEnum.kernelCode
    validity.all (fun op => result (op ++ "(Rows/Text For \"keep\", \"Code\")") row customModel == (kind, kind)) &&
    patterns.all (fun op => result ("[Rows/Text For \"keep\"] " ++ op ++ " \"[0-9]+\"") row customModel == (indexed, indexed))) = true := by native_decide

end A12Kernel.Dm.HavingPredicateAdmissionLocks
