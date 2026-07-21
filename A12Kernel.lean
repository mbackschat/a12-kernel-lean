/-
Root of the `A12Kernel` library — a clean-room Lean 4 executable specification of
the A12 kernel's validation & computation semantics.

The language-neutral semantics live in `spec/` (start at `spec/SEMANTICS-MAP.md`);
the sibling repos serve as oracle (`../a12-kernel`) and knowledge source
(`../a12-rulekit`). See `CLAUDE.md` for the source-of-truth hierarchy and the
clean-room / EUPL boundary that governs how they may be used.
-/
import A12Kernel.Basic
import A12Kernel.Core
import A12Kernel.Cell
import A12Kernel.Document
import A12Kernel.Semantics.FullDate
import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Semantics.DateRangeOverlapOperators
import A12Kernel.Semantics.DateConstruction
import A12Kernel.Semantics.DateConstructionNumeric
import A12Kernel.Semantics.DateTime
import A12Kernel.Semantics.DateTimeDifference
import A12Kernel.Semantics.DateTimeDayDifference
import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.NumericStoredNumber
import A12Kernel.Semantics.NumericTarget
import A12Kernel.Semantics.NumericApplication
import A12Kernel.Semantics.NumericDependency
import A12Kernel.Semantics.ValueList
import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.StarCompleteness
import A12Kernel.Semantics.NumericAggregate
import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.RepetitionNotUnique
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.Enumeration
import A12Kernel.Semantics.SemanticIndex
import A12Kernel.Semantics.CustomCondition
import A12Kernel.Semantics.StringAlternatives
import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.EnumerationComparability
import A12Kernel.Proofs
import A12Kernel.Conformance
