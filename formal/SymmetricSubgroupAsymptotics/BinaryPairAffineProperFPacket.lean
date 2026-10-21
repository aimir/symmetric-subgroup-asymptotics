import SymmetricSubgroupAsymptotics.BinaryPairAffineProperNormalF
import SymmetricSubgroupAsymptotics.BinaryPairProperFQuotientCentralizer
import SymmetricSubgroupAsymptotics.QuotientSubgroupImageCard
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct

/-! Install one selected proper-F packet on the SAME original pair
source and normal. A single central derived top lift suffices; arbitrary
other original affine offsets are retained. Both quotient factors use
the exact original normal cardinal and axis. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open SemidirectProduct LinearSemidirectCoprimeSocleBounds
local instance affineProperFPacket_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem affine_properF_unit_packet
    (B C : Submodule (ZMod 2) (Fin w → ZMod 2)) (z : F.top.range)
    (hB : B ≤ F.kernelSpace) (hC : C ≤ F.kernelSpace) (hCB : C ≤ B)
    (hz : z ∈ Subgroup.center F.top.range) (hzero : F.affineClass z = 0)
    (hCstable : ∀ r v, v ∈ C → F.ambientAffineLinearAction r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → F.ambientAffineLinearAction r v-v ∈ C)
    (hzdisp : ∀ v, F.ambientAffineLinearAction z v-v ∈ C)
    (N : Subgroup U) [N.Normal] (hN : N ≤ F.top.ker)
    (hAC : F.ambientAxis N ≤ C)
    (hcomm : Nat.card C ≤ Nat.card N * 16)
    (hcapacity :
      Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
        F.coordinateTopAction z v-v ∈ F.ambientAxis N} *
      Nat.card {t : F.top.range // ∀ v, v ∈ B →
        F.coordinateTopAction t v-v ∈ F.ambientAxis N} ≤ Nat.card N * 16) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let D := F.affineProperNormalF B z
  letI : D.Normal := F.affineProperNormalF_normal B C z hCB hz hCstable hBdisp hzdisp
  have hBD : F.coordinateSubgroup B ≤ D := by
    rintro _ ⟨k,hk,rfl⟩
    change F.ambientAffineEmbedding k.val ∈ properNormalF F.ambientAffineLinearAction B z
    rw [F.ambientAffineEmbedding_kernel]
    exact Subgroup.subset_closure ⟨Sum.inl (⟨F.bits k,hk⟩ : B),rfl⟩
  obtain ⟨u,hu,ha⟩ := (F.affine_graph_fibre z 0).mpr (by rw [map_zero,hzero])
  have huz : F.ambientAffineEmbedding u = (inr z : F.AmbientAffineModel) := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd ha
    · exact hu
  have huD : u ∈ D := by
    change F.ambientAffineEmbedding u ∈ properNormalF F.ambientAffineLinearAction B z
    rw [huz]
    exact Subgroup.subset_closure ⟨Sum.inr (),rfl⟩
  let q := QuotientGroup.mk' N
  let W := D.map q
  have hwN : W.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  have hcenter : Nat.card (Subgroup.centralizer (W : Set (U ⧸ N))) ≤ 16 := by
    have hc := F.properF_quotient_centralizer_card_mul_le D N B hB hBD u huD
    rw [hu] at hc
    have hp := hc.trans hcapacity
    have hn : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hNC : N ≤ F.coordinateSubgroup C := by
    rw [← inf_eq_right.mpr hN,← F.coordinateSubgroup_ambientAxis N]
    exact F.coordinateSubgroup_mono hAC
  have hm : ⁅W,(⊤ : Subgroup (U ⧸ N))⁆ ≤ (F.coordinateSubgroup C).map q := by
    dsimp only [W]
    rw [← Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N),
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono (F.affineProperNormalF_mixedCommutator_le B C z hz
      hCstable hBdisp hzdisp)
  have hcommCard : Nat.card (⁅W,(⊤ : Subgroup (U ⧸ N))⁆ : Subgroup (U ⧸ N)) ≤ 16 := by
    have hc := quotient_subgroup_image_card_mul_intersection N (F.coordinateSubgroup C)
    rw [inf_eq_left.mpr hNC,F.coordinateSubgroup_card C hC] at hc
    have hle := Subgroup.card_le_of_le hm
    have hn : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hp := normalF_unit_packet_of_actual_product_bound W 8 4
    ((Nat.mul_le_mul hcommCard hcenter).trans (by norm_num)) (hcenter.trans (by norm_num))
  exact ⟨W,hwN,hp.1,hp.2⟩
end SymmetricSubgroupAsymptotics.BinaryPairFrame
