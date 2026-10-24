import SymmetricSubgroupAsymptotics.PrimitiveAffineFourOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PermutationPGroupOrdinaryGenerators
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Ordinary generators for every actual faithful action on four points.
The proof uses Lagrange's theorem, the already proved permutation p-group
bound, uniqueness of the index-two subgroup of S4, and the existing
literal two-generator proofs for A4 and S4. No subgroup catalogue or
smaller-degree generator hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators

theorem alternating_four_genRank_le_two :
    MarkedC4.genRank (alternatingGroup (Fin 4)) ≤ 2 := by
  let H := alternatingGroup (Fin 4)
  let a : H := ⟨TernaryFourBlockPermutationGenerators.a,
    TernaryFourBlockPermutationGenerators.a_even⟩
  let b : H := ⟨TernaryFourBlockPermutationGenerators.b,
    TernaryFourBlockPermutationGenerators.b_even⟩
  let S : Finset H := {a,b}
  have hgen : Subgroup.closure (S : Set H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure,← MonoidHom.range_eq_map,Subgroup.range_subtype]
    simpa only [S,Finset.coe_insert,Finset.coe_singleton,Set.image_insert_eq,
      Set.image_singleton,a,b] using
      TernaryFourBlockPermutationGenerators.alternating_generated
  have hcard : S.card ≤ 2 := by
    simpa only [S,Finset.card_singleton] using
      Finset.card_insert_le a ({b} : Finset H)
  exact (MarkedC4.genRank_le hgen).trans hcard

private theorem divisor_twenty_four_cases (k : ℕ) (hk : k ∣ 24) :
    k ≤ 7 ∨ k = 8 ∨ k = 12 ∨ k = 24 := by
  have hle : k ≤ 24 := Nat.le_of_dvd (by decide) hk
  interval_cases k <;> norm_num at hk <;> norm_num

theorem subgroup_genRank_le_two (J : Subgroup (Equiv.Perm (Fin 4))) :
    MarkedC4.genRank J ≤ 2 := by
  have hcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have hd : Nat.card J ∣ 24 := by
    rw [← hcard]
    exact J.card_subgroup_dvd_card
  rcases divisor_twenty_four_cases (Nat.card J) hd with hsmall | h8 | h12 | h24
  · by_contra h
    have hr : 3 ≤ MarkedC4.genRank J := by omega
    have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hr).trans
      ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card J).trans hsmall)
    norm_num at hp
  · have hp : IsPGroup 2 J := IsPGroup.of_card (n := 3) (by simpa using h8)
    simpa only [Nat.card_fin,Nat.reduceDiv] using
      PermutationPGroupOrdinaryGenerators.genRank_le_degree_div 2 J (Fin 4) hp
  · have hi : J.index = 2 := by
      have hh := J.index_mul_card
      rw [h12,hcard] at hh
      omega
    have hJ := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    rw [hJ]
    exact alternating_four_genRank_le_two
  · let e := MulEquiv.ofBijective J.subtype
      ((Nat.bijective_iff_injective_and_card J.subtype).mpr
        ⟨J.subtype_injective,h24.trans hcard.symm⟩)
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact PrimitiveAffineFourOrdinaryGenerators.symmetric_four_genRank_le_two

theorem genRank_le_two_of_injective_hom {G : Type} [Group G] [Finite G]
    (rho : G →* Equiv.Perm (Fin 4)) (hrho : Function.Injective rho) :
    MarkedC4.genRank G ≤ 2 := by
  let e := MonoidHom.ofInjective (f := rho) hrho
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  exact subgroup_genRank_le_two rho.range

theorem genRank_le_two {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hX : Nat.card X = 4) :
    MarkedC4.genRank G ≤ 2 := by
  let e : X ≃ Fin 4 := Finite.equivFinOfCardEq hX
  let rho := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  exact genRank_le_two_of_injective_hom rho
    (e.permCongrHom.injective.comp MulAction.toPerm_injective)

end SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators
