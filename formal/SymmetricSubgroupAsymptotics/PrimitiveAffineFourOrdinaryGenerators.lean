import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PermutationAutomorphismPuncturedAction
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators

/-! The sole four-point affine base uses the actual complement on
three nonidentity translations. Its order divides six; the large case
is the full faithful S4 action, whose two generators are already proved.
No list of subgroups or affine catalogue is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineFourOrdinaryGenerators

theorem symmetric_four_genRank_le_two : MarkedC4.genRank (Equiv.Perm (Fin 4)) ≤ 2 := by
  let S : Finset (Equiv.Perm (Fin 4)) :=
    {TernaryFourBlockPermutationGenerators.c,TernaryFourBlockPermutationGenerators.s}
  have hgen : Subgroup.closure (S:Set (Equiv.Perm (Fin 4)))=⊤ := by
    simpa only [S,Finset.coe_insert,Finset.coe_singleton] using
      TernaryFourBlockPermutationGenerators.symmetric_generated
  have hcard : S.card ≤ 2 := by
    simpa only [S,Finset.card_singleton] using
      Finset.card_insert_le TernaryFourBlockPermutationGenerators.c
        ({TernaryFourBlockPermutationGenerators.s} : Finset (Equiv.Perm (Fin 4)))
  exact (MarkedC4.genRank_le hgen).trans hcard

theorem genRank_le_two {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 4)] [FaithfulSMul G (Fin 4)]
    (P : PrimitiveAffineProfile G (Fin 4))
    (hprimitive : MulAction.IsPreprimitive G (Fin 4)) : MarkedC4.genRank G ≤ 2 := by
  let x : Fin 4 := 0
  have hd : Nat.card (P.complement x) ∣ 6 := by
    have h := PermutationAutomorphismPuncturedAction.card_dvd_punctured_factorial
      (P.complementAction x) (P.complementAction_injective x)
    simpa only [P.card_eq x,Nat.card_fin,Nat.reduceSub,
      show Nat.factorial 3=6 by decide] using h
  by_cases hsmall : Nat.card (P.complement x) ≤ 3
  · have hr : MarkedC4.genRank (P.complement x) ≤ 1 := by
      by_contra h
      have htwo : 2 ≤ MarkedC4.genRank (P.complement x) := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0<2) htwo).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card (P.complement x)).trans hsmall)
      norm_num at hp
    exact (P.genRank_le_complement_add_one hprimitive x).trans (by omega)
  · have hle := Nat.le_of_dvd (by decide : 0<6) hd
    have hcases : Nat.card (P.complement x)=4 ∨ Nat.card (P.complement x)=5 ∨
        Nat.card (P.complement x)=6 := by omega
    have hsix : Nat.card (P.complement x)=6 := by
      rcases hcases with h | h | h
      · rw [h] at hd
        norm_num at hd
      · rw [h] at hd
        norm_num at hd
      · exact h
    have hfactor : Nat.card G=Nat.card (Fin 4)*Nat.card (P.complement x) := by
      simpa only [P.card_eq x] using (P.isComplement'_complement x).card_mul.symm
    let f : G →* Equiv.Perm (Fin 4) := MulAction.toPermHom G (Fin 4)
    have hf : Function.Injective f := MulAction.toPerm_injective
    have hcard : Nat.card G=Nat.card (Equiv.Perm (Fin 4)) := by
      rw [hfactor,hsix,Nat.card_perm,Nat.card_fin]
      decide
    let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩)
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact symmetric_four_genRank_le_two

theorem exists_half_degree_generators {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 4)] [FaithfulSMul G (Fin 4)]
    (P : PrimitiveAffineProfile G (Fin 4))
    (hprimitive : MulAction.IsPreprimitive G (Fin 4)) :
    ∃ S : Finset G, Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card ≤ 4 := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  have hr := genRank_le_two P hprimitive
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineFourOrdinaryGenerators
