import A12Kernel.Document

namespace A12Kernel.RuleIterationDomain

/-- Full validation observes declared slots in small rule spaces and occupied coordinate
prefixes in larger ones. The threshold belongs to the complete declared space, including
the root bound before root dispatch pins it (iteration-domain grid, 2026-10-04).
Coordinates include fixed group levels; group names deliberately do not enter occupancy. -/
def optimized (bounds : List Nat) : Bool := bounds.prod > 5

/-- One axis always starts at 1. Later coordinates require occupancy only in the optimized
mode. The source's depth-wide upper-bound clamp cannot change this result: beyond the
highest occupied coordinate every candidate already fails the prefix test. The 2×3 and
1×6 grid shapes distinguish this account from a per-axis threshold. -/
def axis (sparse : Bool) (occupied : List (List Nat))
    (stem : List Nat) (capacity : Nat) : List Nat :=
  ((List.range capacity).map (· + 1)).filter fun i =>
    i == 1 || !sparse || occupied.any ((stem ++ [i]).isPrefixOf ·)

/-- Enumerate the suffix below an already dispatched root, keeping the first-coordinate
exception local to every reset rather than adding one fallback row to a global product. -/
def descend (sparse : Bool) (occupied : List (List Nat))
    (stem : List Nat) : List Nat → List (List Nat)
  | [] => [stem]
  | capacity :: rest =>
      (axis sparse occupied stem capacity).flatMap fun i =>
        descend sparse occupied (stem ++ [i]) rest

/-- Ordinary full-rule coordinates. Root instances are supplied by the root-content
dispatcher; the iterator bounds them but does not synthesize additional roots. Neither
this projection nor its implicit child coordinates create physical document topology. -/
def coordinates (bounds : List Nat) (occupied : List (List Nat))
    (roots : List Nat) : List (List Nat) :=
  match bounds with
  | [] => []
  | capacity :: rest =>
      ((List.range capacity).map (· + 1)).filterMap (fun i =>
        if roots.contains i then some i else none) |>.flatMap fun i =>
          descend (optimized bounds) occupied [i] rest

end A12Kernel.RuleIterationDomain
