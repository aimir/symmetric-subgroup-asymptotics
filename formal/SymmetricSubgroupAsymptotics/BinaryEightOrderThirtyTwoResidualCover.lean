import SymmetricSubgroupAsymptotics.BinaryEightHighTopReduction

/-! The checked eight-point action registry reduces an actual order32
rank-three top without an eight-cycle to four literal actions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryEightOrderThirtyTwoResidualCover

private theorem genRank_le_tuple {G : Type} [Group G] [Finite G]
    (n : ℕ) (a : Fin n → G) (ha : Subgroup.closure (Set.range a) = ⊤) :
    MarkedC4.genRank G ≤ n := by
  let S : Finset G := Finset.univ.image a
  have hs : (S : Set G) = Set.range a := by
    ext x
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hg : Subgroup.closure (S : Set G) = ⊤ := by rw [hs]; exact ha
  exact (MarkedC4.genRank_le hg).trans (Finset.card_image_le.trans (by simp))

private theorem power_orbit_of_conjugate
    {B T : Subgroup (Equiv.Perm (Fin 8))} (c : Equiv.Perm (Fin 8))
    (hc : MulAut.conj c • B = T) (g : T)
    (hg : BinaryEightHighTopReduction.SinglePowerOrbit g.val) :
    ∃ b : B, BinaryEightHighTopReduction.SinglePowerOrbit b.val := by
  let e := actionConjugacyEquiv c hc
  let b := e.symm g
  have hbg : (MulAut.conj c) b.val = g.val := congrArg Subtype.val (e.apply_symm_apply g)
  have hb : b.val = (MulAut.conj c⁻¹) g.val := by
    rw [← hbg]
    simp only [MulAut.conj_apply]
    simp [mul_assoc]
  exact ⟨b, hb ▸ BinaryEightHighTopReduction.singlePowerOrbit_conj c⁻¹ hg⟩

private theorem cycle_fifteen : ∃ j : Fin 3,
    BinaryEightHighTopReduction.SinglePowerOrbit (BinaryMenuCayley8T15.generators j) := by
  unfold BinaryEightHighTopReduction.SinglePowerOrbit
  decide +kernel

theorem cover (B : Subgroup (Equiv.Perm (Fin 8))) (hB : IsPGroup 2 B)
    (htrans : ∀ x y : Fin 8, ∃ b : B, b.val x = y)
    (hcard : Nat.card B = 32) (hrank : 3 ≤ MarkedC4.genRank B)
    (hno : ¬ ∃ b : B, BinaryEightHighTopReduction.SinglePowerOrbit b.val) :
    ∃ c : Equiv.Perm (Fin 8),
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T18.generators) ∨
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T19.generators) ∨
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T21.generators) ∨
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) := by
  have ht : PermutationSubgroupTransitive B := by
    intro x y
    obtain ⟨b, hb⟩ := htrans x y
    exact ⟨b.val, b.property, hb⟩
  obtain ⟨i, c, hc⟩ := BinaryActionRegistry8.complete B hB ht
  fin_cases i
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T1.generators)) at hh
    rw [BinaryMenuCayley8T1.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T2.generators)) at hh
    rw [BinaryMenuCayley8T2.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)) at hh
    rw [BinaryMenuCayley8T3.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T4.generators)) at hh
    rw [BinaryMenuCayley8T4.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T5.generators)) at hh
    rw [BinaryMenuCayley8T5.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T6.generators)) at hh
    rw [BinaryMenuCayley8T6.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T7.generators)) at hh
    rw [BinaryMenuCayley8T7.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)) at hh
    rw [BinaryMenuCayley8T8.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)) at hh
    rw [BinaryMenuCayley8T9.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T10.generators)) at hh
    rw [BinaryMenuCayley8T10.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T11.generators)) at hh
    rw [BinaryMenuCayley8T11.exact_card] at hh
    omega
  · obtain ⟨j, hj⟩ := cycle_fifteen
    exact (hno (power_orbit_of_conjugate c hc
      ⟨BinaryMenuCayley8T15.generators j, Subgroup.subset_closure (Set.mem_range_self _)⟩ hj)).elim
  · let e := actionConjugacyEquiv c hc
    have hm : MarkedC4.genRank (Subgroup.closure (Set.range BinaryMenuCayley8T16.generators)) ≤ 2 :=
      genRank_le_tuple 2 (closureGenerators BinaryMenuCayley8T16.generators) (closureGenerators_full _)
    have hb := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
    change MarkedC4.genRank B ≤ MarkedC4.genRank
      (Subgroup.closure (Set.range BinaryMenuCayley8T16.generators)) at hb
    omega
  · let e := actionConjugacyEquiv c hc
    have hm : MarkedC4.genRank (Subgroup.closure (Set.range BinaryMenuCayley8T17.generators)) ≤ 2 :=
      genRank_le_tuple 2 (closureGenerators BinaryMenuCayley8T17.generators) (closureGenerators_full _)
    have hb := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
    change MarkedC4.genRank B ≤ MarkedC4.genRank
      (Subgroup.closure (Set.range BinaryMenuCayley8T17.generators)) at hb
    omega
  · exact ⟨c, Or.inl hc⟩
  · exact ⟨c, Or.inr (Or.inl hc)⟩
  · let e := actionConjugacyEquiv c hc
    have hm : MarkedC4.genRank (Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)) ≤ 2 :=
      genRank_le_tuple 2 (closureGenerators BinaryMenuCayley8T20.generators) (closureGenerators_full _)
    have hb := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
    change MarkedC4.genRank B ≤ MarkedC4.genRank
      (Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)) at hb
    omega
  · exact ⟨c, Or.inr (Or.inr (Or.inl hc))⟩
  · exact ⟨c, Or.inr (Or.inr (Or.inr hc))⟩
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T26.generators)) at hh
    rw [BinaryMenuCayley8T26.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)) at hh
    rw [BinaryMenuCayley8T27.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T28.generators)) at hh
    rw [BinaryMenuCayley8T28.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T29.generators)) at hh
    rw [BinaryMenuCayley8T29.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T30.generators)) at hh
    rw [BinaryMenuCayley8T30.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T31.generators)) at hh
    rw [BinaryMenuCayley8T31.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)) at hh
    rw [BinaryMenuCayley8T35.exact_card] at hh
    omega

end SymmetricSubgroupAsymptotics.BinaryEightOrderThirtyTwoResidualCover
