import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure

/-! Every actual local GL2(2) subgroup either has a nontrivial cubic or
fixes a nonzero binary vector. The binary alternative is proved by the
p-group fixed-point theorem, not a subgroup catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneCubicOrFixedVector
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathNormalGenerators

private theorem square_or_cube : ∀ p : Equiv.Perm (Fin 3), p^2=1 ∨ p^3=1 := by
  decide +kernel

theorem dichotomy (L : Subgroup Linear) :
    (∃ g : L, g^3=1 ∧ g≠1) ∨
      ∃ v : Plane, v≠0 ∧ ∀ g : L, (g : Linear) v=v := by
  by_cases hc : ∃ g : L, g^3=1 ∧ g≠1
  · exact Or.inl hc
  · right
    have hs : ∀ g : L, g^2=1 := by
      intro g
      rcases square_or_cube (toThree (g : Linear)) with h | h
      · apply Subtype.ext
        apply toThree_injective
        simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using h
      · have hg : g^3=1 := by
          apply Subtype.ext
          apply toThree_injective
          simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using h
        have hg1 : g=1 := by
          by_contra hn
          exact hc ⟨g,hg,hn⟩
        rw [hg1,one_pow]
    have hp : IsPGroup 2 L := fun g => ⟨1,hs g⟩
    letI : Fact (Nat.Prime 2) := ⟨by decide⟩
    letI : MulAction L Plane :=
      { smul := fun g v => (g : Linear) v
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl }
    have hcard : 2∣Nat.card Plane := by
      norm_num [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    have hz : (0 : Plane)∈MulAction.fixedPoints L Plane := by
      intro g
      exact map_zero (g : Linear)
    obtain ⟨v,hv,hvn⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point Plane hcard hz
    refine ⟨v,Ne.symm hvn,?_⟩
    intro g
    exact hv g

end SymmetricSubgroupAsymptotics.BinaryPlaneCubicOrFixedVector
