import A12Kernel.Elaboration.LiteralComparisonDiagnostic

/-! # A12Kernel.Conformance.LiteralComparisonDiagnostic — the wrong-kind literal's class ladder

A literal of one family meeting a field of another kind is refused, and which class the Kernel
reports is decided by an **ordered ladder over the pair** rather than by either side alone. These
rows measure it at the constant-assignment carrier; the [filter cases](HavingFilterDiagnostic.lean)
measure the same table where nothing is a target, which is why the ladder is named for neither. The
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

namespace A12Kernel.Conformance.LiteralComparisonDiagnostic

open A12Kernel

private def families : List ComparedLiteralFamily :=
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
example : families.map (fun family => kinds.map (literalComparisonDiagnostic? family)) =
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
        (literalComparisonDiagnostic? family .boolean,
          literalComparisonDiagnostic? family .confirm)) =
    List.replicate 3
      (some .invalidCompareToYesNo, some .invalidCompareToYes) := by
  native_decide

/- **Rung 2 inverts the reading for a temporal constant.** At the same String, Enumeration, Number
   and DateRange targets where every other family reports the *target's* class, a temporal constant
   reports its own — and the four targets that disagree are exactly the separating witnesses. -/
example : [SurfaceScalarKind.string, .enumeration, .number, .dateRange].map
      (fun kind =>
        (literalComparisonDiagnostic? .temporal kind,
          literalComparisonDiagnostic? .number kind)) =
    [ (some .invalidCompareToDate, some .invalidCompareToEnumOrString)
    , (some .invalidCompareToDate, some .invalidCompareToEnumOrString)
    , (some .invalidCompareToDate, none)
    , (some .invalidCompareToDate, some .invalidCompareToDateRange) ] := by
  native_decide

/- **The one cell that discriminates the constant below rung 2.** A Number target reports the
   string-like class for a string-like constant and `inconsistentTypesCompared` for a Boolean one.
   This is the cell a per-carrier table read off a measured sibling gets wrong, and it is why the
   ladder is shared rather than copied. -/
example : (literalComparisonDiagnostic? .stringLike .number,
    literalComparisonDiagnostic? .booleanLike .number) =
    (some .invalidCompareToEnumOrString, some .inconsistentTypesCompared) := by
  native_decide

/- **A CUSTOM target has no rung of its own.** A custom declaration must carry the String kind —
   `customTypeRequiresString` — so its surface kind *is* `.string` and the ladder answers it by
   construction. This row is the model's own statement of that, beside the measurement confirming
   the Kernel agrees cell for cell; an assumption that happens to hold produces no signal, so it is
   asserted rather than left implicit. -/
example :
    ((FieldKind.string.surfaceKind, SurfaceScalarKind.string),
      families.map (literalComparisonDiagnostic? · .string)) =
    ((SurfaceScalarKind.string, SurfaceScalarKind.string),
      [ none
      , some .invalidCompareToEnumOrString
      , some .invalidCompareToDate
      , some .invalidCompareToEnumOrString ]) := by
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

/-! ## A bounded Explain probe: which side does the class name?

An Explain consumer's job at one of these refusals is to point the author at the operand that is
wrong. The class alone cannot do it, and that is not a theoretical limitation — a12-dmkits shipped a
corrective built on the assumption that it could, and withdrew it the same day.

The rows below are the probe. They establish that the **pair** is sufficient and the **class** is
not, which is a statement about the projection rather than about the representation: the error arms
retain the kind, so a consumer reading them can decide correctly, while one reading only
`literalComparisonDiagnostic?` cannot.
-/

/-- Which operand's kind the reported class actually names. -/
private inductive NamedSide where
  | theLiteral
  | theField
  | neither
  deriving Repr, DecidableEq

/-- The side each cell's class names, derived from the pair rather than from the class. Rung 1 and
rung 3 name the field; rung 2 names the literal, because a temporal literal reports its own family
at a field that is not temporal. The Number cell against a Boolean literal names neither — it
reports only that the two disagree. -/
private def namedSide (family : ComparedLiteralFamily)
    (kind : SurfaceScalarKind) : Option NamedSide :=
  match literalComparisonDiagnostic? family kind with
  | none => none
  | some _ =>
      match family, kind with
      | _, .boolean | _, .confirm => some .theField
      | .temporal, .temporal _ => some .theField
      | .temporal, _ => some .theLiteral
      | .booleanLike, .number => some .neither
      | .stringLike, .number => some .theLiteral
      | _, _ => some .theField

/- **The same class names opposite sides on two different pairs**, which is precisely what a
   class-keyed corrective gets wrong. `MVK_INVALID_COMPARE_TO_DATE` at a temporal field is about the
   field; at a String field it is about the literal. A consumer told only the class must guess, and
   whichever way it guesses it is wrong half the time. -/
example : ((literalComparisonDiagnostic? .stringLike (.temporal .date),
      namedSide .stringLike (.temporal .date)),
    (literalComparisonDiagnostic? .temporal .string, namedSide .temporal .string)) =
    ((some .invalidCompareToDate, some .theField),
      (some .invalidCompareToDate, some .theLiteral)) := by
  native_decide

/- **The pair decides it everywhere.** Every classified cell has a side, so a consumer holding the
   pair is never left without an answer — the representation is adequate for the task even though
   the class projection is not. -/
example : families.all (fun family =>
    kinds.all fun kind =>
      (literalComparisonDiagnostic? family kind).isSome == (namedSide family kind).isSome) =
    true := by
  native_decide

/- The one cell that names **neither** side is worth keeping distinct from an absent answer: a
   Boolean literal at a Number field reports that the two disagree and nothing about which is
   intended, so an Explain consumer should say exactly that rather than pick a side. -/
example : (namedSide .booleanLike .number, namedSide .stringLike .number) =
    (some .neither, some .theLiteral) := by
  native_decide

end A12Kernel.Conformance.LiteralComparisonDiagnostic
