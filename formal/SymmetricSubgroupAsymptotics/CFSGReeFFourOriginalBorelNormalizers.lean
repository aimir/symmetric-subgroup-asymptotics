import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CoprimeTernaryCentralizerLift

/-! The SAME original derived/full-centre quotient receives the actual
positive and negative Sylow normalizers. Central kernel containment in
both normalizers is explicit; no automorphism of the quotient is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalBorelNormalizers
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourBorelIntersection CFSGReeFFourOriginalMiddleParabolic
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourFixedPositiveSylow
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedAmbientHom
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem fixedToOriginal_kernel_le_diagonal (m : ℕ) (hm : 0<m) :
    (fixedToOriginal m hm).ker≤fixedDiagonal m := by
  rw [fixedDiagonal_eq_pairNormalizer]
  exact (fixedToOriginal_kernel_le_center m hm).trans
    (le_inf (Subgroup.center_le_normalizer (fixedPositive m : Set (originalModelFixed m)))
      (Subgroup.center_le_normalizer (fixedNegative m : Set (originalModelFixed m))))

theorem fixedToOriginal_kernel_le_borel (m : ℕ) (hm : 0<m) :
    (fixedToOriginal m hm).ker≤fixedBorel m :=
  (fixedToOriginal_kernel_le_diagonal m hm).trans (diagonal_le_borel m)

theorem fixedToOriginal_kernel_le_oppositeBorel (m : ℕ) (hm : 0<m) :
    (fixedToOriginal m hm).ker≤oppositeBorel m := by
  change (fixedToOriginal m hm).ker≤
    Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m))
  exact (fixedToOriginal_kernel_le_center m hm).trans
    (Subgroup.center_le_normalizer (fixedNegative m : Set (originalModelFixed m)))

theorem borel_map_original_normalizer (m : ℕ) (hm : 0<m) :
    (fixedBorel m).map (fixedToOriginal m hm)=
      Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m)) := by
  have h := CoprimeTernaryCentralizerLift.sylow_map_normalizer_eq
    (fixedToOriginal m hm) (fixedToOriginal_surjective m hm) (fixedPositiveSylow m)
  rw [←(fixedPositiveSylow m).coe_coe,fixedPositiveSylow_coe] at h
  rw [←fixedBorel_eq_positive_normalizer,positive_original_image] at h
  exact h

theorem oppositeBorel_map_original_normalizer (m : ℕ) (hm : 0<m) :
    (oppositeBorel m).map (fixedToOriginal m hm)=
      Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m)) := by
  let Q : Sylow 2 (originalModelFixed m) :=
    (fixedPositiveSylow m).mapSurjective
      (f:=(MulAut.conj (oppositionFixed m)).toMonoidHom)
      (MulAut.conj (oppositionFixed m)).surjective
  have hQ : (Q : Subgroup (originalModelFixed m))=fixedNegative m := by
    change (fixedPositiveSylow m : Subgroup (originalModelFixed m)).map
      (MulAut.conj (oppositionFixed m)).toMonoidHom=_
    rw [fixedPositiveSylow_coe]
    exact fixed_positive_image_eq_fixed_negative m
  have h := CoprimeTernaryCentralizerLift.sylow_map_normalizer_eq
    (fixedToOriginal m hm) (fixedToOriginal_surjective m hm) Q
  rw [←Q.coe_coe,hQ] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalBorelNormalizers
