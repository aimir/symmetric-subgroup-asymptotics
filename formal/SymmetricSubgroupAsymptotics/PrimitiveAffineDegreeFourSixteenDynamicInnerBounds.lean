import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourCentralizingTranslationPhysicalHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFixedFreeReflectionPhysicalHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourCubicCentralizerFixedFree
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourA4FixedFreeRelativeHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFourPointSocleSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonbinaryFourPointCharts
import SymmetricSubgroupAsymptotics.BinaryCoinducedSixteenPointHead

/-! Exhaustive actual four-by-four inner frame bounds. The relative and
external capacities are selected jointly from the original translation
centralizer, without imposing a uniform external eight-slot assertion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

structure DegreeFourSixteenDynamicInnerBounds (U : PreE7NonPairActionClass 16) where
  relativeSlots : ℕ
  externalSlots : ℕ
  sum_le : relativeSlots+externalSlots ≤ 10
  relative : ∀ (N : Subgroup (preE7NonPairAction 16 U)) [N.Normal],
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ relativeSlots
  external : ∀ {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer (preE7NonPairAction 16 U) x →* L),
    Function.Surjective f → ∀ rho : Representation (ZMod 2) L V,
    Nat.card L = 3 ∨ Nat.card L = 6 → Module.finrank (ZMod 2) V = 2 →
    Function.Injective rho → ∀ B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction 16 U) x).subtype (rho.comp f)),
    Module.finrank (ZMod 2) (B.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) (preE7NonPairAction 16 U) (ZMod 2))) ≤ externalSlots

variable {U : PreE7NonPairActionClass 16} {basePoint : Fin 16}
  (block : OriginalMinimalBlock (A := preE7NonPairAction 16 U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

private theorem cubicData {T : Type} [Group T]
    (e : DegreeFourComplementQuotient block P ≃* T)
    (hcard : Nat.card T=12 ∨ Nat.card T=24)
    (hr : Nat.card block.Fibre=4) (hs : Nat.card block.Points=4)
    (hD : degreeFourTernaryCore block P=⊥) :
    ∃ S : Sylow 3 (preE7NonPairAction 16 U), ∃ s : preE7NonPairAction 16 U,
      ∃ d : block.Points ≃ Fin 4,
      (S : Subgroup (preE7NonPairAction 16 U))=Subgroup.zpowers s ∧ s^3=1 ∧
      QuotientGroup.mk' (E block P) s ≠ 1 ∧
      ∀ i, d (s • i)=BinaryFourCubicNormalizerPointShapes.blockCycle (d i) := by
  obtain ⟨S,s,d,hgen,hs3,hsn,hd⟩ := degreeFourOriginalCubicBlockGauge block P e hcard hr hs hD
  have hsq : QuotientGroup.mk' (E block P) s ≠ 1 := by
    intro h
    have hsm : s ∈ (S : Subgroup (preE7NonPairAction 16 U)) := by
      rw [hgen]
      exact Subgroup.mem_zpowers s
    have he : degreeFourPhysicalCanonicalMap block P e s=1 := by
      change e (QuotientGroup.mk' (E block P) s)=1
      rw [h,map_one]
    have hx : (⟨s,hsm⟩ : S)=1 := degreeFourOriginalCubicSylow_injective block P e hr S
      (by change degreeFourPhysicalCanonicalMap block P e s=degreeFourPhysicalCanonicalMap block P e 1; rw [he,map_one])
    exact hsn (congrArg Subtype.val hx)
  exact ⟨S,s,d,hgen,hs3,hsq,hd⟩

private theorem centralizer_zero
    (S : Sylow 3 (preE7NonPairAction 16 U))
    (h : ¬ ∃ z : E block P, (z : preE7NonPairAction 16 U) ≠ 1 ∧
      (z : preE7NonPairAction 16 U) ∈ Subgroup.centralizer (S : Set (preE7NonPairAction 16 U))) :
    ∀ e : preE7NonPairAction 16 U, e ∈ E block P →
      (∀ t : preE7NonPairAction 16 U, t ∈ (S : Subgroup (preE7NonPairAction 16 U)) → e*t=t*e) → e=1 := by
  intro e he hc
  by_contra hne
  apply h
  refine ⟨⟨e,he⟩,hne,?_⟩
  intro t ht
  exact (hc t ht).symm

def degreeFourSixteenDynamicInnerBounds
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre=4) (hs : Nat.card block.Points=4)
    (hD : degreeFourTernaryCore block P=⊥) : DegreeFourSixteenDynamicInnerBounds U := by
  classical
  apply Classical.choice
  have hnon := degreeFourZeroCore_fourPoint_top_not_isPGroup block P hr hs hD
  rcases degreeFour_nonbinary_actual_pointCharts block hs hnon with hA | hA
  · obtain ⟨A⟩ := hA
    let e := DegreeFourA4OriginalPointChart.groupEquiv (block := block) (P := P) (C := A) hr hD
    obtain ⟨S,s,d,hgen,hs3,hsq,hd⟩ := cubicData block P e
      (Or.inl BinaryFourCanonicalInducedChart.complement_card) hr hs hD
    by_cases hz : ∃ z : E block P, (z : preE7NonPairAction 16 U) ≠ 1 ∧
        (z : preE7NonPairAction 16 U) ∈ Subgroup.centralizer (S : Set (preE7NonPairAction 16 U))
    · obtain ⟨z,hzne,hzc⟩ := hz
      refine ⟨{
        relativeSlots := 2
        externalSlots := 6
        sum_le := by decide
        relative := fun N _ => degreeFourZeroCore_fourPoint_binary_relative_head_le_two block P hMN hr hs hD N
        external := ?_ }⟩
      intro L V _ _ _ _ _ x f hf rho hL hdim hrho B
      exact DegreeFourA4OriginalPointChart.centralizingTranslation_physical_head block P A
        hr hD S s d hgen hs3 hsq hd z hzne hzc x f hf rho hL hdim hrho B
    · have hzero := centralizer_zero block P S hz
      have hfixed := degreeFourCubicCentralizer_fixedFree block P S s hgen hzero
      refine ⟨{
        relativeSlots := 0
        externalSlots := 10
        sum_le := by decide
        relative := ?_
        external := ?_ }⟩
      · intro N _
        exact (DegreeFourA4OriginalPointChart.original_fixedFree_relative_head_zero
          (block := block) (P := P) (C := A) hr hD s (by rw [←map_pow,hs3,map_one]) hfixed N).le
      · intro L V _ _ _ _ _ x f hf rho hL hdim hrho B
        exact BinaryCoinducedSixteenPointHead.head_le_ten_on_points x (by simp)
          f hf rho hL hdim hrho B
  · obtain ⟨A⟩ := hA
    let e := DegreeFourS4OriginalPointChart.groupEquiv (block := block) (P := P) (C := A) hr hD
    obtain ⟨S,s,d,hgen,hs3,hsq,hd⟩ := cubicData block P e
      (Or.inr BinaryFourCanonicalSymmetricInducedChart.symmetricComplement_card) hr hs hD
    by_cases hz : ∃ z : E block P, (z : preE7NonPairAction 16 U) ≠ 1 ∧
        (z : preE7NonPairAction 16 U) ∈ Subgroup.centralizer (S : Set (preE7NonPairAction 16 U))
    · obtain ⟨z,hzne,hzc⟩ := hz
      refine ⟨{
        relativeSlots := 2
        externalSlots := 6
        sum_le := by decide
        relative := fun N _ => degreeFourZeroCore_fourPoint_binary_relative_head_le_two block P hMN hr hs hD N
        external := ?_ }⟩
      intro L V _ _ _ _ _ x f hf rho hL hdim hrho B
      exact DegreeFourS4OriginalPointChart.centralizingTranslation_physical_head block P A
        hr hD S s d hgen hs3 hsq hd z hzne hzc x f hf rho hL hdim hrho B
    · refine ⟨{
        relativeSlots := 2
        externalSlots := 8
        sum_le := by decide
        relative := fun N _ => degreeFourZeroCore_fourPoint_binary_relative_head_le_two block P hMN hr hs hD N
        external := ?_ }⟩
      intro L V _ _ _ _ _ x f hf rho hL hdim hrho B
      exact DegreeFourS4OriginalPointChart.fixedFreeTranslation_physical_head block P A
        hr hD S s d hgen hs3 hsq hd (centralizer_zero block P S hz)
        x f hf rho hL hdim hrho B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
