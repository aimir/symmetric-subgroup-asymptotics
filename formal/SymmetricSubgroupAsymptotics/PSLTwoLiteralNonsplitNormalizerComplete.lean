import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitDihedralNormalizer
import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCardinality

/-! Unconditional local nonsplit-normalizer geometry for actual finite fields
of odd characteristic and cardinality≥5. No chosen-element/order callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormalizerComplete
open PSLTwoLiteralNonsplitTorusCyclic PSLTwoLiteralNonsplitNormalizerStructure
open PSLTwoLiteralNonsplitTorusCardinality
variable {F : Type*} [Field F] [Fintype F]
local notation "PSL2" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) F

theorem exists_weyl_and_normalizer (hF : ringChar F ≠ 2) (hq : 5 ≤ Nat.card F)
    (ν : F) (hν : ¬IsSquare ν) : ∃ w : PSL2,
      w ∉ nonsplitTorus ν ∧ w*w=1 ∧
      (∀ x ∈ nonsplitTorus ν,w*x*w⁻¹=x⁻¹) ∧
      Subgroup.normalizer (nonsplitTorus ν : Set PSL2)=nonsplitTorus ν ⊔ Subgroup.zpowers w := by
  obtain ⟨C,hC,hy⟩ := exists_noncentral_SL ν hν hq
  exact PSLTwoLiteralNonsplitDihedralNormalizer.exists_weyl_and_normalizer hF hν hC hy

theorem normalizer_dihedral (hF : ringChar F ≠ 2) (hq : 5 ≤ Nat.card F)
    (ν : F) (hν : ¬IsSquare ν) :
    Nonempty (Subgroup.normalizer (nonsplitTorus ν : Set PSL2) ≃*
      DihedralGroup ((Nat.card F+1)/2)) := by
  obtain ⟨C,hC,hy⟩ := exists_noncentral_SL ν hν hq
  have hh := PSLTwoLiteralNonsplitDihedralNormalizer.normalizer_dihedral hF hν hC hy
  rw [torus_card hF ν hν] at hh
  exact hh

theorem normalizer_card (hF : ringChar F ≠ 2) (hq : 5 ≤ Nat.card F)
    (ν : F) (hν : ¬IsSquare ν) :
    Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set PSL2))=Nat.card F+1 := by
  obtain ⟨C,hC,hy⟩ := exists_noncentral_SL ν hν hq
  rw [PSLTwoLiteralNonsplitDihedralNormalizer.normalizer_card hF hν hC hy,mul_comm]
  exact twice_torus_card hF ν hν

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormalizerComplete
