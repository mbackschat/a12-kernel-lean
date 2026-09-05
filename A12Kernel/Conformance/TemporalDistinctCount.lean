import A12Kernel.Elaboration.TemporalDistinctCount

/-! # A12Kernel.Conformance.TemporalDistinctCount — the component-set gate, against its neighbour

`NumberOfDifferentValues` and `FieldValuesNotUnique` accept the same operand shapes and gate them
differently, so every row here is paired with the neighbour's answer on the identical list. That
pairing is the point: a gate that merely *looked* right on this operator would be indistinguishable
from the neighbour's until a pair separates them, and one such pair exists
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-distinct-count-component-set-and-locus),
nine `rule check` rows in one batch).

The fixture's component sets agree with each declaration's format, which is what any model this
project admits looks like; a declaration whose format and components contradict each other is
refused by the stored-text classifiers and its authorability is unmeasured.
-/

namespace A12Kernel.Conformance.TemporalDistinctCount

open A12Kernel

private def yearMonth : TemporalComponents :=
  { year := true, month := true, day := false
    hour := false, minute := false, second := false }

private def dateField (id : FieldId) (name format : String)
    (components : TemporalComponents := TemporalComponents.fullDate) :
    FlatFieldDecl := {
  id
  groupPath := ["Probe"]
  name
  policy := { kind := .temporal .date components }
  temporalTargetPolicy := some { format }
}

/-- Two date-only groups at the root, differing in exactly what the two operators' gates read: one
    carries a single component set in two spellings, the other two component sets. -/
private def groupField (id : FieldId) (group name format : String)
    (components : TemporalComponents := TemporalComponents.fullDate) :
    FlatFieldDecl := {
  id
  groupPath := ["Probe", group]
  name
  policy := { kind := .temporal .date components }
  temporalTargetPolicy := some { format }
}

private def model : FlatModel := {
  fields := [
    dateField 1 "FiledOn" "yyyy-MM-dd",
    dateField 2 "ClosedOn" "dd.MM.yyyy",
    dateField 3 "CoverFrom" "yyyy-MM" yearMonth,
    dateField 6 "SupersededFrom" "yyyy-MM-dd",
    { id := 4, groupPath := ["Probe"], name := "SkuText",
      policy := { kind := .string } },
    { id := 5, groupPath := ["Probe"], name := "Flag",
      policy := { kind := .boolean } },
    { id := 19, groupPath := ["Probe"], name := "Amount",
      policy := { kind := .number { scale := 0, signed := false } } },
    groupField 10 "MixBox" "IsoA" "yyyy-MM-dd",
    groupField 11 "MixBox" "DotB" "dd.MM.yyyy",
    groupField 12 "SetBox" "Full" "yyyy-MM-dd",
    groupField 13 "SetBox" "YearMonth" "yyyy-MM" yearMonth,
    { id := 14, groupPath := ["Probe", "TextBox"], name := "Note",
      policy := { kind := .string } },
    -- Two mixed expansions differing only in **declaration order**, which is what the class turns
    -- on. Nothing else about the pair varies.
    groupField 15 "DateFirstBox" "ADate" "yyyy-MM-dd",
    { id := 16, groupPath := ["Probe", "DateFirstBox"], name := "BNum",
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 17, groupPath := ["Probe", "NumFirstBox"], name := "ANum",
      policy := { kind := .number { scale := 0, signed := false } } },
    groupField 18 "NumFirstBox" "BDate" "yyyy-MM-dd"]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def pair (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

/-- This operator's verdict on one authored pair. -/
private def distinct? (first second : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalDistinctCountSource model ["Probe"] (pair first second) with
  | .ok _ => none
  | .error error => error.diagnostic?

private def distinctAdmitted (first second : String) : Bool :=
  (elaborateTemporalDistinctCountSource model ["Probe"] (pair first second)).toOption.isSome

/-- The neighbouring operator's verdict on the identical list. -/
private def unique? (first second : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalValuesNotUniqueSource model ["Probe"] (pair first second) with
  | .ok _ => none
  | .error error => error.diagnostic?

/- **The separating pair, and the reason this operator needs its own gate at all.** Two DATE fields
   naming the same components in different spellings are admitted here and refused by the neighbour.
   Adopting the neighbour's format-equality gate would have over-rejected this row — the inverse of
   the over-admission this project usually guards against, and the reason a measured neighbour is
   not a licence. -/
example :
    distinctAdmitted "FiledOn" "ClosedOn" = true ∧
      unique? "FiledOn" "ClosedOn" = some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- **A differing component set is refused, which is what keeps the gate from being vacuous.** The
   admitted row above and this one differ only in the second operand's component set, so a gate that
   admitted everything would satisfy the first and fail here. The Kernel's message names both
   formats rather than the sets, which is why the error carries formats. -/
example : distinct? "FiledOn" "CoverFrom" = some .dateFormatsNotCompatible := by
  native_decide

/- **Date-first with a non-temporal member draws the cross-family class**, not the component-set one:
   the kind gate runs before the list's own gate, so an operand that is not temporal at all never
   reaches the component comparison. -/
example : distinct? "FiledOn" "SkuText" = some .dateAndNonDate := by
  native_decide

/- **The kind-domain code is this operator's, one token from the neighbour's.** A Boolean draws
   `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED` here and the `CMP_`-less form there, on the same
   list. The two codes name different operators' gates and neither may be read off the other; this
   row exists because the names invite exactly that carry-over. -/
example :
    distinct? "Flag" "FiledOn" = some .onlyStringEnumNumberCmpDateAllowed ∧
      unique? "Flag" "FiledOn" = some .onlyStringEnumNumberDateAllowed ∧
      KernelStaticDiagnostic.onlyStringEnumNumberCmpDateAllowed.kernelCode
        = "MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED" ∧
      KernelStaticDiagnostic.onlyStringEnumNumberDateAllowed.kernelCode
        = "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED" := by
  native_decide

/- **Two distinct fields sharing one format are admitted by both operators**, which is what fixes
   the separation above as being about the *spelling* rather than about carrying two operands. It is
   also the row that dissolves the neighbour's refusal: its code names kinds, but the gate is the
   format string, and holding the format fixed while varying nothing else shows it. -/
example :
    distinctAdmitted "FiledOn" "SupersededFrom" = true ∧
      unique? "FiledOn" "SupersededFrom" = none := by
  native_decide


/-! ## A group operand, gated by **this** operator's rule

The group is admitted, and its expansion meets the component-set gate rather than the neighbour's
format-equality one. The pair below is the whole point: one group, two operators, two verdicts
([checkpoint](../../docs/SOURCES.md#src-temporal-group-operand-follows-its-own-operator)). Reusing
the neighbour's group certificate — the tempting move, since it already exists and already certifies
temporal group expansions — would have refused the admitted half. -/
private def groupOperand (group : String) : SurfaceFieldEntitySource :=
  { first := .group (.path { base := .absolute, groups := ["Probe", group] })
    rest := [] }

private def distinctGroup? (group : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalDistinctCountSource model ["Probe"] (groupOperand group) with
  | .ok _ => none
  | .error error => error.diagnostic?

private def uniqueGroup? (group : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalValuesNotUniqueSource model ["Probe"]
      (groupOperand group) with
  | .ok _ => none
  | .error error => error.diagnostic?

/- One component set in two spellings: admitted here, refused by the neighbour. -/
example :
    (elaborateTemporalDistinctCountSource model ["Probe"]
      (groupOperand "MixBox")).toOption.isSome = true ∧
      uniqueGroup? "MixBox" = some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- Two component sets: refused here, with this operator's own class. Without this row the admission
   above is equally well explained by the group slot skipping the gate entirely — which is the
   failure mode that would let a group smuggle an incompatible declaration past it. -/
example : distinctGroup? "SetBox" = some .dateFormatsNotCompatible := by
  native_decide

/- The group's component set reaches the **list** gate too, so a group and a scalar operand are
   compared against each other rather than each being checked alone. -/
example :
    (elaborateTemporalDistinctCountSource model ["Probe"]
      { first := .group (.path { base := .absolute, groups := ["Probe", "MixBox"] })
        rest := [.field (bare "CoverFrom")] }).toOption.isNone = true := by
  native_decide

/- A **non-temporal** declaration in the expansion is refused by both operators, and the refusal
   names that declaration's own path and kind rather than the group path with a fabricated one —
   which is why the offending declaration is found and re-certified rather than reported
   positionally. The duplicated certificate covers the component gate only; this arm is delegated,
   so the two operators cannot disagree about *whether* such a group is refused.

   `TextBox`'s expansion leads with the String, so this operator claims **no class** — the list is
   another overload's, exactly as a scalar list led by a non-temporal operand is. The rows below
   separate that from a merely mixed expansion. -/
example :
    (elaborateTemporalDistinctCountSource model ["Probe"]
      (groupOperand "TextBox")).toOption.isNone = true ∧
      (elaborateTemporalValuesNotUniqueSource model ["Probe"]
        (groupOperand "TextBox")).toOption.isNone = true ∧
      distinctGroup? "TextBox" = none := by
  native_decide

/-! ### Declaration order decides the class, in a group's expansion as in a scalar list

The same two kinds in the other order draw a different code, and the scalar controls agree cell for
cell ([checkpoint](../../docs/SOURCES.md#src-temporal-group-operand-follows-its-own-operator)). So
the first-operand rule reaches a group's expansion rather than stopping at the authored slots, and a
projection keyed on the *offending* kind alone would be right in one order and wrong in the other —
which is exactly what this operator shipped before the pair was measured. -/
example :
    distinctGroup? "DateFirstBox" = some .dateAndNonDate ∧
      distinct? "FiledOn" "Amount" = some .dateAndNonDate := by
  native_decide

/- A leading **Number** makes the list the other overload's, so this one refuses claiming no class
   rather than reporting the date code. The Kernel's own answer there is
   `MVK_NUMBER_AND_NON_NUMBER`, which that overload owns. -/
example :
    distinctGroup? "NumFirstBox" = none ∧
      (elaborateTemporalDistinctCountSource model ["Probe"]
        (groupOperand "NumFirstBox")).toOption.isNone = true := by
  native_decide


end A12Kernel.Conformance.TemporalDistinctCount
