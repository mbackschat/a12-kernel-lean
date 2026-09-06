import A12Kernel.Elaboration.ConstantAssignmentDiagnostic

/-! # A12Kernel.Conformance.ConstantAssignmentDiagnostic — the wrong-kind constant's class ladder

Assigning a bare constant to a target of the wrong kind is refused, and which class the Kernel
reports is decided by an **ordered ladder over the pair** rather than by either side alone. The
complete eight-constant by ten-target grid behind these rows was measured in one batch
([checkpoint](../../docs/SOURCES.md#src-constant-assignment-diagnostic-ladder)); every cell asserted
here has an observed row, and the grid is what makes the ladder legible at all.

Two readings are natural and both are wrong. "The code names the target" fails on a temporal
constant, which reports its own family's class even at a String target. "The code names the
constant" fails everywhere else, including at the one cell where the pair genuinely matters: a
Number target reports the string-like class for a string-like constant and a different class for a
Boolean one. A carrier that read its table off a measured sibling instead of measuring its own
would be wrong in exactly those cells, so the table is asserted here once and every carrier
specializes it.

`none` marks a pair the Kernel's **kind** gate does not refuse. Three of the four are outright
admissions; the fourth, a string-like constant at an Enumeration target, is gated on the literal's
membership in the declared domain instead, which this function is not given the domain to decide.
-/

namespace A12Kernel.Conformance.ConstantAssignmentDiagnostic

open A12Kernel

private def families : List ConstantAssignmentFamily :=
  [.stringLike, .number, .temporal, .booleanLike]

/-- Every `SurfaceScalarKind` value, in the grid's column order. The temporal constructor is
expanded over its three families because the ladder's second rung is precisely the claim that they
are not distinguished here, and an unexpanded column could not witness it. -/
private def kinds : List SurfaceScalarKind :=
  [.string, .enumeration, .number,
    .temporal .date, .temporal .time, .temporal .dateTime,
    .dateRange, .boolean, .confirm]

/- **The complete kind-decided table**, one row per constant family in `kinds` order. Each cell is a
   measured verdict: `none` where the batch admitted the pair or gated it on the literal instead,
   and the observed class otherwise. -/
example : families.map (fun family => kinds.map (constantAssignmentDiagnostic? family)) =
    [ -- a string-like constant
      [ none, none, some .invalidCompareToEnumOrString
      , some .invalidCompareToDate, some .invalidCompareToDate
      , some .invalidCompareToDate
      , some .invalidCompareToDateRange
      , some .invalidCompareToYesNo, some .invalidCompareToYes ]
      -- a Number constant
    , [ some .invalidCompareToEnumOrString, some .invalidCompareToEnumOrString, none
      , some .invalidCompareToDate, some .invalidCompareToDate
      , some .invalidCompareToDate
      , some .invalidCompareToDateRange
      , some .invalidCompareToYesNo, some .invalidCompareToYes ]
      -- a temporal constant of any of the three families
    , [ some .invalidCompareToDate, some .invalidCompareToDate
      , some .invalidCompareToDate
      , some .invalidCompareToDate, some .invalidCompareToDate
      , some .invalidCompareToDate
      , some .invalidCompareToDate
      , some .invalidCompareToYesNo, some .invalidCompareToYes ]
      -- a Boolean constant
    , [ some .invalidCompareToEnumOrString, some .invalidCompareToEnumOrString
      , some .inconsistentTypesCompared
      , some .invalidCompareToDate, some .invalidCompareToDate
      , some .invalidCompareToDate
      , some .invalidCompareToDateRange
      , none, none ] ] := by
  native_decide

/- **Rung 1 dominates every family.** A Boolean or Confirm target reports its own class whatever the
   constant is — the temporal constant included, which is the row that makes this a precedence
   rather than a coincidence, since that family overrides every other target. The two kinds do not
   share a class, so a consumer collapsing Boolean with Confirm reports the wrong one. -/
example : (families.filter (· != .booleanLike)).map
      (fun family =>
        (constantAssignmentDiagnostic? family .boolean,
          constantAssignmentDiagnostic? family .confirm)) =
    List.replicate 3
      (some .invalidCompareToYesNo, some .invalidCompareToYes) := by
  native_decide

/- **Rung 2 inverts the reading for a temporal constant.** At the same String, Enumeration, Number
   and DateRange targets where every other family reports the *target's* class, a temporal constant
   reports its own — and the four targets that disagree are exactly the separating witnesses. -/
example : [SurfaceScalarKind.string, .enumeration, .number, .dateRange].map
      (fun kind =>
        (constantAssignmentDiagnostic? .temporal kind,
          constantAssignmentDiagnostic? .number kind)) =
    [ (some .invalidCompareToDate, some .invalidCompareToEnumOrString)
    , (some .invalidCompareToDate, some .invalidCompareToEnumOrString)
    , (some .invalidCompareToDate, none)
    , (some .invalidCompareToDate, some .invalidCompareToDateRange) ] := by
  native_decide

/- **The one cell that discriminates the constant below rung 2.** A Number target reports the
   string-like class for a string-like constant and `inconsistentTypesCompared` for a Boolean one.
   This is the cell a per-carrier table read off a measured sibling gets wrong, and it is why the
   ladder is shared rather than copied. -/
example : (constantAssignmentDiagnostic? .stringLike .number,
    constantAssignmentDiagnostic? .booleanLike .number) =
    (some .invalidCompareToEnumOrString, some .inconsistentTypesCompared) := by
  native_decide

/- **The exact Kernel identifiers**, so the classes above are pinned to the observable strings and
   not merely to this project's constructor names. -/
example : [KernelStaticDiagnostic.invalidCompareToYesNo,
    .invalidCompareToYes, .invalidCompareToDate, .invalidCompareToDateRange,
    .invalidCompareToEnumOrString, .inconsistentTypesCompared].map
      KernelStaticDiagnostic.kernelCode =
    ["MVK_INVALID_COMPARE_TO_YESNO", "MVK_INVALID_COMPARE_TO_YES",
      "MVK_INVALID_COMPARE_TO_DATE", "MVK_INVALID_COMPARE_TO_DATE_RANGE",
      "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING",
      "MVK_INCONSISTENT_TYPES_COMPARED"] := by
  native_decide

end A12Kernel.Conformance.ConstantAssignmentDiagnostic
