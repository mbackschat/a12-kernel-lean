import A12Kernel.Elaboration.SemanticIndexAdmission

/-! # Locks on the semantic-index admission cascade

`external evidence pending`: `dmtool` has no measured route to declare a semantic index, so neither
the order nor the admitting side can be probed at this revision. These cases lock *this project's*
chosen reading so a later calibration has something exact to disagree with.

The matrix is two **descending ladders**. Each row of a ladder removes exactly one offence from the
row above and the reported class advances to the next gate, which is a stronger separator than
isolated rows: it establishes the order and every gate's reachability in one pass, and no row can be
explained by a different account that happens to agree on a single verdict.

The first ladder walks the seven gates a reference key reaches, ending in admission. The second holds
a clean key and walks the five gates that belong to the value spec and its index-group resolution,
including the three the settled walk in [`IndexGroupResolution`](../Elaboration/IndexGroupResolution.lean)
contributes. Paired defects bridge the ladders: key shape precedes nesting, and resolution precedes
agreement on both key arms. Beyond them: the constant arm's reachable set, the empty-key disjunct,
lenience swapping one class for another rather than admitting, and the public admission query.
-/

namespace A12Kernel.Conformance.SemanticIndexAdmission

open A12Kernel

/-- A key reference with each of its six gates set independently, so a ladder row differs from its
neighbour in exactly one flag. -/
private def keyRef (isField hasStar typesAgree inside noValueCheck hasCategory : Bool) :
    SemanticIndexAdmissionKeyRef where
  resolvesToField := isField
  starred := hasStar
  baseTypeMatchesIndexField := typesAgree
  containedInIndexGroup := inside
  expandsToNoValueValidation := noValueCheck
  carriesCategory := hasCategory

private def key (isField hasStar typesAgree inside noValueCheck hasCategory : Bool) :
    SemanticIndexAdmissionKey :=
  .reference (keyRef isField hasStar typesAgree inside noValueCheck hasCategory)

/-- A clean key, for the rows whose subject is the site. -/
private def cleanKey : SemanticIndexAdmissionKey := key true false true false false false

private def indexGroup : IndexDeclaringGroup := { declaredNames := 1 }
private def twoNames : IndexDeclaringGroup := { declaredNames := 2 }
private def brokenName : IndexDeclaringGroup := { declaredNames := 1, nameResolvesToField := false }
private def plainGroup : IndexDeclaringGroup := {}

/-- One index group whose name resolves, so resolution passes and the later gates are reachable. -/
private def resolving : SemanticIndexAdmissionSite :=
  { indexPath := [indexGroup], starredAtIndexLevel := true }

private def site (selfNested : Bool) (path : List IndexDeclaringGroup) : SemanticIndexAdmissionSite :=
  { valueSpecIsSemanticIndex := selfNested, indexPath := path, starredAtIndexLevel := false }

private def code? (s : SemanticIndexAdmissionSite) (k : SemanticIndexAdmissionKey) : Option String :=
  (semanticIndexAdmissionRefusal s k).map KernelStaticDiagnostic.kernelCode

/- **The reference-key ladder.** Every row removes one offence from the row above and the next gate
speaks, so the seven classes are ordered against each other rather than merely each reachable. The
last row removes the value spec's own star and the site is admitted, which is what makes the ladder a
separator and not a list: an account that reordered any two adjacent gates disagrees with this
column. -/
example :
    [ code? resolving (key false true false true true true)
    , code? resolving (key true true false true true true)
    , code? resolving (key true false false true true true)
    , code? resolving (key true false true true true true)
    , code? resolving (key true false true false true true)
    , code? resolving (key true false true false false true)
    , code? resolving (key true false true false false false)
    , code? { resolving with starredAtIndexLevel := false } cleanKey ] =
    [ some "MVK_SEMANTIC_INDEX_NO_FIELD"
    , some "MVK_SEMANTIC_INDEX_WITH_WILDCARD"
    , some "MVK_INDEX_TYPE_INCONSISTENT"
    , some "MVK_SEMANTIC_INDEX_CONTAINED_IN_INDEX"
    , some "MVK_INVALID_RAW_TYPE"
    , some "MVK_SEMANTIC_INDEX_WITH_CATEGORY"
    , some "MVK_SEMANTIC_INDEX_AND_WILDCARD"
    , none ] := by
  native_decide

/- **The site ladder**, with the key held clean throughout. The self-nesting refusal outranks the
resolution walk — the first row's path also offends the two-groups gate and reports neither of its
classes — and the walk's own three classes then appear in its order, followed by the absent-index
class and admission. The last row is the control that says a group declaring no index is invisible to
the walk rather than a second index group. -/
example :
    [ code? (site true [indexGroup, indexGroup]) cleanKey
    , code? (site false [indexGroup, indexGroup]) cleanKey
    , code? (site false [twoNames]) cleanKey
    , code? (site false [brokenName]) cleanKey
    , code? (site false [plainGroup, plainGroup]) cleanKey
    , code? (site false [plainGroup, indexGroup, plainGroup]) cleanKey ] =
    [ some "MVK_SEMANTIC_INDEX_WITH_SEMANTIC_INDEX"
    , some "MVK_MULTIPLE_INDEX_FIELDS"
    , some "MVK_MULTIPLE_INDEX_FIELDS2"
    , some "MVK_INDEX_FIELD_INVALID"
    , some "MVK_NO_INDEX_FIELD"
    , none ] := by
  native_decide

/- **A star on the key outranks a star on the value spec**, which is the pair a single "semantic index
and wildcard" rule would collapse. The same site reports the key's class with the key starred and the
value spec's class without it, so the two are ordered and distinct. -/
example :
    code? resolving (key true true true false false false) =
        some "MVK_SEMANTIC_INDEX_WITH_WILDCARD" ∧
      code? resolving cleanKey = some "MVK_SEMANTIC_INDEX_AND_WILDCARD" := by
  native_decide

/- **The constant arm reaches its own class and none of the reference arm's.** A rejected key value
and an empty key both report the constant class, an accepted one is admitted, and the value spec's
star still speaks on this arm — so the arm split removes four gates and not the whole tail. -/
example :
    [ code? (site false [indexGroup]) (.constant "k" true)
    , code? (site false [indexGroup]) (.constant "k" false)
    , code? (site false [indexGroup]) (.constant "" true)
    , code? resolving (.constant "k" true) ] =
    [ none
    , some "MVK_INDEX_VALUE_INVALID"
    , some "MVK_INDEX_VALUE_INVALID"
    , some "MVK_SEMANTIC_INDEX_AND_WILDCARD" ] := by
  native_decide

/- **The empty key is refused by its own disjunct.** The third row above pairs an empty key with an
*accepting* type, so the type test cannot be what refuses it; here that pairing is stated directly
against its non-empty twin. -/
example :
    keyAgreementRefusal (.constant "" true) = some .semanticIndexConstantInvalid ∧
      keyAgreementRefusal (.constant "k" true) = none := by
  native_decide

/- **Lenience swaps a class rather than removing one.** One reference offends both the
value-validation gate and the category gate: strict reports the first, lenient the second, and only
removing the category suffix as well admits it. So a lenient reader's vocabulary is not the strict
one minus a member. -/
example :
    [ code? (site false [indexGroup]) (key true false true false true true)
    , code? { site false [indexGroup] with lenient := true } (key true false true false true true)
    , code? { site false [indexGroup] with lenient := true }
        (key true false true false true false) ] =
    [ some "MVK_INVALID_RAW_TYPE"
    , some "MVK_SEMANTIC_INDEX_WITH_CATEGORY"
    , none ] := by
  native_decide

example :
    [ code? (site true [indexGroup]) (key false false true false false false)
    , code? (site true [indexGroup]) (key true true true false false false)
    , code? (site true [indexGroup]) cleanKey
    , code? (site false [indexGroup]) cleanKey ] =
    [ some "MVK_SEMANTIC_INDEX_NO_FIELD"
    , some "MVK_SEMANTIC_INDEX_WITH_WILDCARD"
    , some "MVK_SEMANTIC_INDEX_WITH_SEMANTIC_INDEX"
    , none ] := by
  native_decide

example :
    let mismatched := key true false false false false false
    [ code? (site false [brokenName]) mismatched
    , code? (site false []) mismatched
    , code? (site false [indexGroup]) mismatched
    , code? (site false [brokenName]) (.constant "k" false)
    , code? (site false []) (.constant "k" false)
    , code? (site false [indexGroup]) (.constant "k" false) ] =
    [ some "MVK_INDEX_FIELD_INVALID"
    , some "MVK_NO_INDEX_FIELD"
    , some "MVK_INDEX_TYPE_INCONSISTENT"
    , some "MVK_INDEX_FIELD_INVALID"
    , some "MVK_NO_INDEX_FIELD"
    , some "MVK_INDEX_VALUE_INVALID" ] := by
  native_decide

example :
    semanticIndexSiteAdmitted (site false [indexGroup]) cleanKey = true ∧
      semanticIndexSiteAdmitted resolving cleanKey = false := by
  native_decide

end A12Kernel.Conformance.SemanticIndexAdmission
