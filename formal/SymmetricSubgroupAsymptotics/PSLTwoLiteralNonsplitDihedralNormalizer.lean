import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitQuotientNormalizer
import SymmetricSubgroupAsymptotics.CyclicInversionDihedralEquivalence

/-! Actual Mathlib PSL2 Weyl involution and dihedral normalizer. The genuine
noncentral torus element is explicit; its existence from q≥5/cardq+1 is the
remaining local cardinality bridge, not a classification assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitDihedralNormalizer
open PSLTwoLiteralNonsplitTorusCyclic PSLTwoLiteralNonsplitNormalizerStructure
open PSLTwoLiteralNonsplitQuotientNormalizer CyclicInversionDihedralEquivalence
variable {F : Type*} [Field F]
local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "PSL2" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) F

private theorem antiNS_mul_mem {ν : F} {W M : SL2} (hW : IsAntiNS ν W)
    (hM : M ∈ nonsplitSL ν) : IsAntiNS ν (W*M) := by
  obtain ⟨hW1,hW2⟩ := hW
  obtain ⟨hM1,hM2⟩ := hM
  constructor
  · rw [mul_apply_SL,mul_apply_SL,hW1,hW2,hM1,hM2]
    ring
  · rw [mul_apply_SL,mul_apply_SL,hW1,hW2,hM1,hM2]
    ring

private theorem inv_mul_mem_of_antiNS {ν : F} {W M : SL2}
    (hW : IsAntiNS ν W) (hM : IsAntiNS ν M) : W⁻¹*M ∈ nonsplitSL ν := by
  obtain ⟨hW1,hW2⟩ := hW
  obtain ⟨hM1,hM2⟩ := hM
  constructor
  · rw [mul_apply_SL,mul_apply_SL,inv_apply_00,inv_apply_01,inv_apply_10,inv_apply_11,
      hW1,hW2,hM1,hM2]
    ring
  · rw [mul_apply_SL,mul_apply_SL,inv_apply_00,inv_apply_01,inv_apply_10,inv_apply_11,
      hW1,hW2,hM1,hM2]
    ring

theorem antiNS_projective_square {ν : F} {W : SL2} (hW : IsAntiNS ν W) :
    projection W*projection W=1 := by
  obtain ⟨hW1,hW2⟩ := hW
  have hd := det_entries W
  rw [hW1,hW2] at hd
  have hsq : W*W=(-1 : SL2) := by
    apply SL_ext <;> simp [mul_apply_SL,hW1,hW2] <;>
      first | (solve | ring) | linear_combination -hd
  rw [←map_mul,hsq]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨(-1 : F),by norm_num,?_⟩
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal, hij]

theorem exists_weyl_and_normalizer [Fintype F] (hF : ringChar F ≠ 2)
    {ν : F} (hν : ¬IsSquare ν) {C : SL2} (hC : C ∈ nonsplitSL ν)
    (hy : C.val 1 0 ≠ 0) : ∃ w : PSL2,
      w ∉ nonsplitTorus ν ∧ w*w=1 ∧
      (∀ x ∈ nonsplitTorus ν,w*x*w⁻¹=x⁻¹) ∧
      Subgroup.normalizer (nonsplitTorus ν : Set PSL2)=nonsplitTorus ν ⊔ Subgroup.zpowers w := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hν0 : ν ≠ 0 := by intro hh; apply hν; exact ⟨0,by rw [hh,mul_zero]⟩
  obtain ⟨W,hW⟩ := exists_antiNS hF hν0
  let w := projection W
  have hw : w ∉ nonsplitTorus ν := by
    rw [projection_mem_torus_iff]
    exact antiNS_not_mem h2 hW hν0
  have hN (g : PSL2) : g ∈ Subgroup.normalizer (nonsplitTorus ν : Set PSL2) ↔
      g ∈ nonsplitTorus ν ∨ w⁻¹*g ∈ nonsplitTorus ν := by
    obtain ⟨M,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL2) g
    have ha : IsAntiNS ν M ↔ W⁻¹*M ∈ nonsplitSL ν := by
      constructor
      · exact inv_mul_mem_of_antiNS hW
      · intro hm
        have hh := antiNS_mul_mem hW hm
        simpa only [mul_inv_cancel_left] using hh
    change projection M ∈ Subgroup.normalizer (nonsplitTorus ν : Set PSL2) ↔
      projection M ∈ nonsplitTorus ν ∨ (projection W)⁻¹*projection M ∈ nonsplitTorus ν
    rw [projection_mem_normalizer_iff h2 hν hC hy,
      ←map_inv,←map_mul,projection_mem_torus_iff,projection_mem_torus_iff,ha]
  have hwN : w ∈ Subgroup.normalizer (nonsplitTorus ν : Set PSL2) :=
    (hN w).mpr (Or.inr (by simp))
  refine ⟨w,hw,antiNS_projective_square hW,?_,?_⟩
  · rintro x ⟨A,hA,rfl⟩
    change projection W*projection A*(projection W)⁻¹=(projection A)⁻¹
    rw [←map_inv,←map_mul,←map_mul,antiNS_conj hW hA,map_inv]
  · apply le_antisymm
    · intro g hg
      rcases (hN g).mp hg with ht|ht
      · exact Subgroup.mem_sup_left ht
      · have he : g=w*(w⁻¹*g) := by group
        rw [he]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
          (Subgroup.mem_sup_left ht)
    · apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.mpr hwN

theorem normalizer_dihedral [Fintype F] (hF : ringChar F ≠ 2)
    {ν : F} (hν : ¬IsSquare ν) {C : SL2} (hC : C ∈ nonsplitSL ν)
    (hy : C.val 1 0 ≠ 0) :
    Nonempty (Subgroup.normalizer (nonsplitTorus ν : Set PSL2) ≃*
      DihedralGroup (Nat.card (nonsplitTorus ν))) := by
  obtain ⟨w,hw,hsq,hinv,hN⟩ := exists_weyl_and_normalizer hF hν hC hy
  obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral (nonsplitTorus ν)
    (nonsplitTorus_isCyclic ν hν) w hw hsq hinv
  exact ⟨(MulEquiv.subgroupCongr hN).trans e⟩

theorem normalizer_card [Fintype F] (hF : ringChar F ≠ 2)
    {ν : F} (hν : ¬IsSquare ν) {C : SL2} (hC : C ∈ nonsplitSL ν)
    (hy : C.val 1 0 ≠ 0) :
    Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set PSL2))=2*Nat.card (nonsplitTorus ν) := by
  obtain ⟨e⟩ := normalizer_dihedral hF hν hC hy
  rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitDihedralNormalizer
