import A12Kernel.Elaboration.NumericSource

namespace A12Kernel

/-- A raw fixed source returns one after its required scope projects successfully. Scope ownership
    remains with `wellFormedIn`; no ancestor coordinate is substituted for the fixed result. -/
theorem boundCurrentRepetition_fixed_coordinate
    (source : BoundCurrentRepetitionSource) (environment : Env) (coordinates : List Nat)
    (fixed : source.level = none)
    (bound : environment.pathForScope source.scope = .ok coordinates) :
    source.coordinateAt environment = .ok 1 := by
  simp [BoundCurrentRepetitionSource.coordinateAt, bound, fixed]
  rfl

/-- A raw repeatable source reads its selected level after validating its required scope. The
    selected coordinate alone is insufficient; model ownership remains with `wellFormedIn`. -/
theorem boundCurrentRepetition_repeatable_coordinate
    (source : BoundCurrentRepetitionSource) (environment : Env)
    (coordinates : List Nat) (level : RepeatableLevel) (coordinate : Nat)
    (repeatable : source.level = some level)
    (bound : environment.pathForScope source.scope = .ok coordinates)
    (selected : environment.bindingAt level = .ok coordinate) :
    source.coordinateAt environment = .ok coordinate := by
  simp [BoundCurrentRepetitionSource.coordinateAt, bound, repeatable, selected]
  rfl

end A12Kernel
