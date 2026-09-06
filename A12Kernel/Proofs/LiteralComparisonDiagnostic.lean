import A12Kernel.Elaboration.LiteralComparisonDiagnostic

/-! # Laws of the constant-assignment and numeric-comparison class ladders

The executable cases lock the measured grid cell by cell. These laws state the property a consumer
actually depends on and that an enumeration of cells can only imply: **the projection is total on
refusals.** An Explain or Translate consumer reading `none` must be able to conclude that the Kernel
does not refuse the pair on kind, rather than that this project failed to record a class — and that
conclusion is what the totality law licenses.

Both are decidable over a finite product, so the proofs are one `decide` each. The value is in the
statement's quantifier: it ranges over every pair rather than over the pairs someone remembered to
list, so a new `SurfaceScalarKind` constructor breaks the law rather than silently escaping the
table.
-/

namespace A12Kernel

/-- The exact pairs the literal-comparison ladder declines to classify, and the reason each one is
there. Three are outright Kernel admissions; the fourth is gated on the literal's membership in a
declared enumeration domain, which is a value question the ladder is not given the domain to
decide. -/
def literalComparisonUnclassifiedPairs :
    List (ComparedLiteralFamily × SurfaceScalarKind) :=
  [(.booleanLike, .boolean), (.booleanLike, .confirm),
    (.number, .number), (.stringLike, .string), (.stringLike, .enumeration)]

/-- **The ladder is total on refusals.** A pair it declines to classify is one of the five above,
and every other pair carries a class. A consumer may therefore read `none` as "the Kernel's kind
gate does not refuse this", never as "unrecorded". -/
theorem literalComparisonDiagnostic_total_on_refusals
    (family : ComparedLiteralFamily) (kind : SurfaceScalarKind) :
    literalComparisonDiagnostic? family kind = none ↔
      (family, kind) ∈ literalComparisonUnclassifiedPairs := by
  cases family <;> cases kind <;>
    first
      | rfl
      | (rename_i temporalKind; cases temporalKind <;> decide)
      | decide

/-- **The numeric-comparison column is total on refusals too**, and its unclassified set is a single
kind rather than five. That asymmetry is the measured content: the literal column's admissions are
spread across two families and a value gate, where a numeric comparison admits Number alone. -/
theorem numericComparisonDiagnostic_total_on_refusals
    (kind : SurfaceScalarKind) :
    numericComparisonDiagnostic? kind = none ↔ kind = .number := by
  cases kind <;>
    first
      | rfl
      | (rename_i temporalKind; cases temporalKind <;> decide)
      | decide

/-- **A temporal constant is never unclassified.** Rung 2 makes its row total: every target kind
draws a class, including the two the other families are admitted at. This is the law a consumer
needs to know that a date-shaped literal always reports something, whatever it is assigned to. -/
theorem temporalLiteralComparison_alwaysClassified
    (kind : SurfaceScalarKind) :
    (literalComparisonDiagnostic? .temporal kind).isSome = true := by
  cases kind <;>
    first
      | rfl
      | (rename_i temporalKind; cases temporalKind <;> decide)
      | decide

end A12Kernel
