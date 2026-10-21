import SymmetricSubgroupAsymptotics.BinaryPairRankFiveResidualTop
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! The proved original26-action coverage reduces a rank-three top of
order greater than32 without an eight-cycle to the three literal actions
29/30/31. The exclusions use original generator count and actual cyclic
point orbits, retaining the actual point conjugator in the conclusion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryEightHighTopReduction

def SinglePowerOrbit (g : Equiv.Perm (Fin 8)) : Prop :=
  ∀ x y : Fin 8, ∃ k : Fin 8, (g ^ k.val) x = y

theorem singlePowerOrbit_conj (c : Equiv.Perm (Fin 8))
    {g : Equiv.Perm (Fin 8)} (hg : SinglePowerOrbit g) :
    SinglePowerOrbit ((MulAut.conj c) g) := by
  intro x y
  obtain ⟨k,hk⟩ := hg (c.symm x) (c.symm y)
  refine ⟨k,?_⟩
  rw [← map_pow]
  change c ((g ^ k.val) (c.symm x)) = y
  exact (congrArg c hk).trans (c.apply_symm_apply y)

private theorem genRank_le_tuple {G : Type} [Group G] [Finite G]
    (n : ℕ) (a : Fin n → G) (ha : Subgroup.closure (Set.range a) = ⊤) :
    MarkedC4.genRank G ≤ n := by
  let S : Finset G := Finset.univ.image a
  have hs : (S : Set G) = Set.range a := by
    ext x
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hg : Subgroup.closure (S : Set G) = ⊤ := by rw [hs]; exact ha
  exact (MarkedC4.genRank_le hg).trans (Finset.card_image_le.trans (by simp))

private theorem has_power_orbit_of_conjugate
    {B T : Subgroup (Equiv.Perm (Fin 8))} (c : Equiv.Perm (Fin 8))
    (hc : MulAut.conj c • B = T) (g : T) (hg : SinglePowerOrbit g.val) :
    ∃ b : B, SinglePowerOrbit b.val := by
  let e := actionConjugacyEquiv c hc
  let b := e.symm g
  have hbg : (MulAut.conj c) b.val = g.val := congrArg Subtype.val (e.apply_symm_apply g)
  have hb : b.val = (MulAut.conj c⁻¹) g.val := by
    rw [←hbg]
    simp only [MulAut.conj_apply]
    simp [mul_assoc]
  exact ⟨b,hb ▸ singlePowerOrbit_conj c⁻¹ hg⟩

private theorem cycle26 : SinglePowerOrbit (BinaryMenuCayley8T26.generators 0) := by
  change ∀ x y : Fin 8, ∃ k : Fin 8, ((BinaryMenuCayley8T26.generators 0) ^ k.val) x = y
  decide +kernel
private theorem cycle28 : SinglePowerOrbit (BinaryMenuCayley8T28.generators 2) := by
  change ∀ x y : Fin 8, ∃ k : Fin 8, ((BinaryMenuCayley8T28.generators 2) ^ k.val) x = y
  decide +kernel
private theorem cycle35 : SinglePowerOrbit (BinaryMenuCayley8T35.generators 0 * BinaryMenuCayley8T35.generators 2) := by
  change ∀ x y : Fin 8, ∃ k : Fin 8, ((BinaryMenuCayley8T35.generators 0 * BinaryMenuCayley8T35.generators 2) ^ k.val) x = y
  decide +kernel

theorem large_top_cover
    (B : Subgroup (Equiv.Perm (Fin 8))) (hB : IsPGroup 2 B)
    (htrans : ∀ x y : Fin 8, ∃ b : B, b.val x = y)
    (hlarge : 32 < Nat.card B) (hrank : 3 ≤ MarkedC4.genRank B)
    (hno : ¬ ∃ b : B, SinglePowerOrbit b.val) :
    ∃ c : Equiv.Perm (Fin 8),
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T29.generators) ∨
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T30.generators) ∨
      MulAut.conj c • B = Subgroup.closure (Set.range BinaryMenuCayley8T31.generators) := by
  have ht : PermutationSubgroupTransitive B := by
    intro x y
    obtain ⟨b,hb⟩ := htrans x y
    exact ⟨b.val,b.property,hb⟩
  obtain ⟨i,c,hc⟩ := BinaryActionRegistry8.complete B hB ht
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
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T15.generators)) at hh
    rw [BinaryMenuCayley8T15.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T16.generators)) at hh
    rw [BinaryMenuCayley8T16.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T17.generators)) at hh
    rw [BinaryMenuCayley8T17.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)) at hh
    rw [BinaryMenuCayley8T18.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T19.generators)) at hh
    rw [BinaryMenuCayley8T19.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)) at hh
    rw [BinaryMenuCayley8T20.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T21.generators)) at hh
    rw [BinaryMenuCayley8T21.exact_card] at hh
    omega
  · have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card B = Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) at hh
    rw [BinaryMenuCayley8T22.exact_card] at hh
    omega
  · apply (hno (has_power_orbit_of_conjugate c hc
      ⟨BinaryMenuCayley8T26.generators 0,Subgroup.subset_closure (Set.mem_range_self _)⟩
      cycle26)).elim
  · let e := actionConjugacyEquiv c hc
    have hm : MarkedC4.genRank (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)) ≤ 2 :=
      genRank_le_tuple 2 (closureGenerators BinaryMenuCayley8T27.generators)
        (closureGenerators_full _)
    have hb := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
    change MarkedC4.genRank B ≤ MarkedC4.genRank
      (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)) at hb
    omega
  · apply (hno (has_power_orbit_of_conjugate c hc
      ⟨BinaryMenuCayley8T28.generators 2,Subgroup.subset_closure (Set.mem_range_self _)⟩
      cycle28)).elim
  · exact ⟨c,Or.inl hc⟩
  · exact ⟨c,Or.inr (Or.inl hc)⟩
  · exact ⟨c,Or.inr (Or.inr hc)⟩
  · apply (hno (has_power_orbit_of_conjugate c hc
      ⟨BinaryMenuCayley8T35.generators 0 * BinaryMenuCayley8T35.generators 2,
        Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_range_self _))
          (Subgroup.subset_closure (Set.mem_range_self _))⟩
      cycle35)).elim

end SymmetricSubgroupAsymptotics.BinaryEightHighTopReduction

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)

include hact

/-- A literal top eight-cycle lifts to one cyclic orbit on the same
original pair labels. The original lift may have arbitrary offsets. -/
theorem cyclicOrbit_card_one_of_top_singlePowerOrbit (g : U)
    (hg : BinaryEightHighTopReduction.SinglePowerOrbit (F.top g)) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Fin 8)) = 1 := by
  letI highTopPower_pretransitive : MulAction.IsPretransitive (Subgroup.zpowers g) (Fin 8) := ⟨by
    intro x y
    obtain ⟨k,hk⟩ := hg x y
    refine ⟨⟨g ^ k.val,Subgroup.npow_mem_zpowers g k.val⟩,?_⟩
    change (g ^ k.val) • x = y
    rw [hact,map_pow]
    exact hk⟩
  letI highTopPower_subsingleton :
      Subsingleton (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Fin 8)) :=
    (MulAction.pretransitive_iff_subsingleton_quotient (Subgroup.zpowers g) (Fin 8)).mp
      highTopPower_pretransitive
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

/-- The source rank-five exclusion removes literal top eight-cycles
without changing the source or its actual pair action. -/
theorem no_top_singlePowerOrbit_of_rank_five (hU : IsPGroup 2 U)
    (hrank : 5 ≤ MarkedC4.genRank U) (htop : MarkedC4.genRank F.top.range ≤ 3) :
    ¬ ∃ b : F.top.range, BinaryEightHighTopReduction.SinglePowerOrbit b.val := by
  rintro ⟨b,hb⟩
  obtain ⟨g,hg⟩ := F.top.rangeRestrict_surjective b
  have hpower : BinaryEightHighTopReduction.SinglePowerOrbit (F.top g) := by
    simpa only [←hg] using hb
  exact F.no_single_cyclic_orbit_of_rank_five hact hU hrank htop
    ⟨g,F.cyclicOrbit_card_one_of_top_singlePowerOrbit hact g hpower⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
