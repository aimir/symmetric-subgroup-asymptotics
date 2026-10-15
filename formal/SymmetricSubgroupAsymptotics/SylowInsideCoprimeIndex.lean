import Mathlib.GroupTheory.Sylow

/-! An actual subgroup of prime-coprime index contains an actual ambient
Sylow subgroup. Its inclusion is the original subgroup inclusion. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem exists_sylow_le_of_not_dvd_index
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) (hA : ¬ p ∣ A.index) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ A := by
  let Q : Sylow p A := Classical.choice inferInstance
  let K : Subgroup G := (Q : Subgroup A).map A.subtype
  have hK : IsPGroup p K := Q.isPGroup'.map A.subtype
  have hi : ¬ p ∣ K.index := by
    rw [Subgroup.index_map_subtype (Q : Subgroup A)]
    exact Nat.Prime.not_dvd_mul Fact.out Q.not_dvd_index hA
  exact ⟨hK.toSylow hi, Subgroup.map_subtype_le (Q : Subgroup A)⟩

end SymmetricSubgroupAsymptotics

end
