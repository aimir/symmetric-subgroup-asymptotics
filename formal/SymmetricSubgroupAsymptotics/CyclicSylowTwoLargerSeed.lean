import SymmetricSubgroupAsymptotics.CyclicSylowTwoTransitivePowerAction

/-! A cyclic binary seed inside a nonbinary faithful transitive2-power
point action lies inside a strictly larger actual binary subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
  [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem exists_larger_sylow_of_cyclic_binary_seed (H : Subgroup G)
    (hH : IsPGroup 2 H) (hcyclic : IsCyclic H)
    (hmin : (Nat.card G).minFac = 2) (d : ℕ) (hdegree : Nat.card X = 2 ^ d)
    (hnot : ¬IsPGroup 2 G) :
    ∃ P : Sylow 2 G,H ≤ P ∧ Nat.card H < Nat.card P := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨P,hHP⟩ := hH.exists_le_sylow
  refine ⟨P,hHP,?_⟩
  by_contra hn
  have heq : H = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hHP (le_of_not_gt hn)
  have hpcyclic : IsCyclic P := by
    change IsCyclic ↥(P : Subgroup G)
    rw [←heq]
    exact hcyclic
  exact hnot (isPGroup_of_cyclic_sylow_two (X := X) P hpcyclic hmin d hdegree)

end SymmetricSubgroupAsymptotics
end
