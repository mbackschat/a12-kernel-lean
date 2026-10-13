import A12Kernel.Elaboration.IndexAndSortDeclaration

/-! # Index- and sort-field declaration laws

The two roles share one cascade and differ in exactly one arm. The laws below say that precisely, so a consumer may implement the cascade once and branch on the role only where the Kernel does.
-/

namespace A12Kernel

/-- The two roles agree everywhere except on a table enumeration, which only an index field is
refused for. This is the whole difference between them, and stating it is what licenses one shared
implementation. -/
theorem rowFieldRefusal_roles_agree_off_tableEnum (role : RowFieldRole) (target : NominatedTarget)
    (h : ∀ valueValidationOff, target ≠ .field valueValidationOff true) :
    rowFieldRefusal role target =
      (rowFieldRefusal .sortField target).map (fun refusal =>
        match refusal with
        | .nameUnresolved _ => .nameUnresolved role
        | .valueValidationOff _ => .valueValidationOff role
        | .indexFieldTableEnum => .indexFieldTableEnum
        | .sortFieldDuplicate => .sortFieldDuplicate
        | .sortListCapacity => .sortListCapacity) := by
  cases target with
  | unresolved => rfl
  | group => rfl
  | field valueValidationOff tableEnumeration =>
    cases tableEnumeration
    · cases valueValidationOff <;> cases role <;> rfl
    · exact absurd rfl (h valueValidationOff)

/-- A refusal always names the role it came from, except for the table-enumeration class whose name
already carries it. So a consumer reading the class alone knows which nomination is at fault. -/
theorem rowFieldRefusal_names_its_role (role : RowFieldRole) (target : NominatedTarget)
    (refusal : RowFieldRefusal) (h : rowFieldRefusal role target = some refusal) :
    refusal = .nameUnresolved role ∨ refusal = .valueValidationOff role ∨
      (refusal = .indexFieldTableEnum ∧ role = .indexField) := by
  cases target with
  | unresolved => simp_all [rowFieldRefusal]
  | group => simp_all [rowFieldRefusal]
  | field valueValidationOff tableEnumeration =>
    cases valueValidationOff <;> cases tableEnumeration <;> cases role <;> simp_all [rowFieldRefusal]

/-- Value validation being off disqualifies a nomination in either role, whatever else the field is.
This is the arm both measured witnesses exercise, and it is the one that reaches outside this clause:
the same switch ends the stored-value pipeline in `ValueFormalCheck`. -/
theorem rowFieldRefusal_valueValidationOff (role : RowFieldRole) (tableEnumeration : Bool) :
    rowFieldRefusal role (.field true tableEnumeration) = some (.valueValidationOff role) := by
  rfl

/-- A group's two roles are independent: within the duplicate window and with distinct sort names,
the sort refusals are exactly those of its sort nominations. -/
theorem rowFieldDeclarationRefusals_sort_only (sort : List (String × NominatedTarget))
    (distinct : (sort.map (·.1)).Nodup) (short : sort.length ≤ 3) :
    rowFieldDeclarationRefusals { index := none, sort := sort } =
      sort.filterMap (rowFieldRefusal .sortField ·.2) := by
  have keep : ∀ (kept rest : List (String × NominatedTarget)),
      ((kept ++ rest).map (·.1)).Nodup → rest.foldl keepFirstName kept = kept ++ rest := by
    intro kept rest
    induction rest generalizing kept with
    | nil => simp
    | cons entry rest ih =>
      intro nodup
      have fresh : kept.any (·.1 == entry.1) = false := by
        simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at nodup
        simp only [List.any_eq_false, beq_iff_eq]
        intro other mem same
        exact nodup.2.2 other.1 (List.mem_map.mpr ⟨other, mem, rfl⟩) entry.1 (by simp) same
      simp only [List.foldl_cons, keepFirstName, fresh, Bool.false_eq_true, ↓reduceIte]
      have := ih (kept ++ [entry]) (by simpa using nodup)
      simpa using this
  have whole := keep [] sort (by simpa using distinct)
  have leading : sort.take 3 = sort := List.take_of_length_le short
  simp [rowFieldDeclarationRefusals, whole, leading, distinct, Nat.sub_eq_zero_of_le short]

end A12Kernel
