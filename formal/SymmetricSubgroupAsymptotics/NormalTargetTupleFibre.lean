import SymmetricSubgroupAsymptotics.NormalTargetHomFibreCount
import SymmetricSubgroupAsymptotics.BinaryStructuredEpiFibre

/-! Fixed tuple fibres retain an arbitrary literal normal subgroup of the
target. The exponential base is its actual centralizer, not the center of
the whole target. All indices remain in the original source quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NormalTargetTupleFibre
open MarkedC4

variable {G Q : Type*} [Group G] [Group Q]
    {ι : Type*} (x : ι → G) (H : Subgroup G) [H.Normal]
    (F : Subgroup Q) [F.Normal]

omit [F.Normal] in
theorem centralizerPreimage_maps_to_centralizer (f : G →* Q)
    (hkill : H ≤ f.ker)
    (himage : Subgroup.closure (Set.range (f ∘ x)) = F) :
    ∀ c ∈ BinaryStructuredEpiFibre.centralizerPreimage x H,
      f c ∈ Subgroup.centralizer (F : Set Q) := by
  intro c hc
  have he : f c ∈ Subgroup.centralizer (Set.range (f ∘ x)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨i, rfl⟩
    have hi := (Subgroup.mem_centralizer_iff.mp hc)
      ((QuotientGroup.mk' H) (x i)) (Set.mem_range_self i)
    have hi' := congrArg (QuotientGroup.lift H f hkill) hi
    simpa only [map_mul, QuotientGroup.lift_mk] using hi'
  rwa [← Subgroup.centralizer_closure, himage] at he

/-- The displayed tuple's normal commutator maps to exactly [F,Q] when
its image generates the literal normal F and the full map is onto. -/
theorem normalCommutator_map (f : G →* Q) (hf : Function.Surjective f)
    (himage : Subgroup.closure (Set.range (f ∘ x)) = F) :
    (generatorNormalCommutator x).map f = ⁅F, (⊤ : Subgroup Q)⁆ := by
  rw [generatorNormalCommutator_map x f hf]
  have hn : Subgroup.normalClosure (Set.range (f ∘ x)) = F := by
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rw [← himage]
      exact Subgroup.subset_closure
    · rw [← himage]
      exact Subgroup.closure_le_normalClosure
  simp only [generatorNormalCommutator, hn]

/-- A bound on the surviving normal commutator in G/H is paid only as
a target-dependent constant; all source-rank growth has centralizer slope. -/
theorem selected_card_le [Finite G] [Finite Q] [Finite ι] :
    Nat.card {f : G →* Q // H ≤ f.ker ∧
      Subgroup.closure (Set.range (f ∘ x)) = F} ≤
      (Nat.card Q) ^ ((Nat.card ((generatorNormalCommutator x).map
        (QuotientGroup.mk' H))) ^ Nat.card ι) *
      (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G := by
  have hb := NormalTargetHomFibreCount.selected_card_le
    (BinaryStructuredEpiFibre.centralizerPreimage x H)
    (Subgroup.centralizer (F : Set Q))
    (fun f : G →* Q => H ≤ f.ker ∧
      Subgroup.closure (Set.range (f ∘ x)) = F)
    (fun f hf => centralizerPreimage_maps_to_centralizer x H F f hf.1 hf.2)
  have hQ : Nat.card (Q ⧸ Subgroup.centralizer (F : Set Q)) ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  exact hb.trans (Nat.mul_le_mul_right _
    ((Nat.pow_le_pow_left hQ _).trans
      (Nat.pow_le_pow_right (Nat.card_pos : 0 < Nat.card Q)
        (BinaryStructuredEpiFibre.centralizerPreimage_index_le x H))))

end SymmetricSubgroupAsymptotics.NormalTargetTupleFibre
