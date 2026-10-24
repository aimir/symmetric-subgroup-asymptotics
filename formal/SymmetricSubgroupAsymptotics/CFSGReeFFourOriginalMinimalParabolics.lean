import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalBorelNormalizers
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeMinimalParabolics

/-! Both exhaustive minimal-overgroup families descend through the
actual original projection. Its central kernel lies in the literal
normalizers, so strictness, minimality and labels survive the quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMinimalParabolics
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourPerfectProjection
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourBorelIntersection CFSGReeFFourOriginalBorelNormalizers
open CFSGReeFFourMinimalParabolics CFSGReeFFourOppositeMinimalParabolics
open CFSGReeFFourOppositeParabolicRootIntersection CFSGSurjectiveMinimalOvergroups

def originalSimpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    Subgroup (CFSG.Models.ReeF4 m) :=
  (simpleParabolic m b).map (fixedToOriginal m hm)

def originalNegativeSimpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    Subgroup (CFSG.Models.ReeF4 m) :=
  (negativeSimpleParabolic m b).map (fixedToOriginal m hm)

theorem original_normalizer_lt_simpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m))<
      originalSimpleParabolic m hm b := by
  have h := map_lt_map_of_kernel_le (fixedToOriginal m hm)
    (fixedToOriginal_kernel_le_borel m hm) (borel_lt_simpleParabolic m b)
  rw [borel_map_original_normalizer] at h
  exact h

theorem original_simpleParabolic_minimal (m : ℕ) (hm : 0<m) (b : Bool)
    (H : Subgroup (CFSG.Models.ReeF4 m))
    (hBH : Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m))<H)
    (hHP : H≤originalSimpleParabolic m hm b) : H=originalSimpleParabolic m hm b := by
  have h := map_minimal_overgroup (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)
    (fixedToOriginal_kernel_le_borel m hm) (borel_lt_simpleParabolic m b)
    (simpleParabolic_minimal m b)
  rw [borel_map_original_normalizer] at h
  exact h H hBH hHP

theorem minimal_original_overgroup_eq_simpleParabolic (m : ℕ) (hm : 0<m)
    (H : Subgroup (CFSG.Models.ReeF4 m))
    (hBH : Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m))<H)
    (hmin : ∀M : Subgroup (CFSG.Models.ReeF4 m),
      Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m))<M→M≤H→M=H) :
    ∃b : Bool,H=originalSimpleParabolic m hm b := by
  have h := minimal_overgroup_family_surjective (fixedToOriginal m hm)
    (fixedToOriginal_surjective m hm) (fixedToOriginal_kernel_le_borel m hm)
    (simpleParabolic m) (minimal_overgroup_eq_simpleParabolic m)
  rw [borel_map_original_normalizer] at h
  exact h H hBH hmin

theorem originalSimpleParabolic_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (originalSimpleParabolic m hm) :=
  map_family_injective (fixedToOriginal m hm) (fixedToOriginal_kernel_le_borel m hm)
    (simpleParabolic m) (fun b=>show CFSGReeFFourFixedBorelCardinality.fixedBorel m≤simpleParabolic m b
      from le_sup_left) (simpleParabolic_injective m)

theorem original_negative_normalizer_lt_simpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m))<
      originalNegativeSimpleParabolic m hm b := by
  have h := map_lt_map_of_kernel_le (fixedToOriginal m hm)
    (fixedToOriginal_kernel_le_oppositeBorel m hm) (oppositeBorel_lt_negativeSimpleParabolic m b)
  rw [oppositeBorel_map_original_normalizer] at h
  exact h

theorem original_negativeSimpleParabolic_minimal (m : ℕ) (hm : 0<m) (b : Bool)
    (H : Subgroup (CFSG.Models.ReeF4 m))
    (hBH : Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m))<H)
    (hHP : H≤originalNegativeSimpleParabolic m hm b) : H=originalNegativeSimpleParabolic m hm b := by
  have h := map_minimal_overgroup (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)
    (fixedToOriginal_kernel_le_oppositeBorel m hm) (oppositeBorel_lt_negativeSimpleParabolic m b)
    (negativeSimpleParabolic_minimal m b)
  rw [oppositeBorel_map_original_normalizer] at h
  exact h H hBH hHP

theorem minimal_original_overgroup_eq_negativeSimpleParabolic (m : ℕ) (hm : 0<m)
    (H : Subgroup (CFSG.Models.ReeF4 m))
    (hBH : Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m))<H)
    (hmin : ∀M : Subgroup (CFSG.Models.ReeF4 m),
      Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m))<M→M≤H→M=H) :
    ∃b : Bool,H=originalNegativeSimpleParabolic m hm b := by
  have h := minimal_overgroup_family_surjective (fixedToOriginal m hm)
    (fixedToOriginal_surjective m hm) (fixedToOriginal_kernel_le_oppositeBorel m hm)
    (negativeSimpleParabolic m) (minimal_overgroup_eq_negativeSimpleParabolic m)
  rw [oppositeBorel_map_original_normalizer] at h
  exact h H hBH hmin

theorem originalNegativeSimpleParabolic_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (originalNegativeSimpleParabolic m hm) :=
  map_family_injective (fixedToOriginal m hm) (fixedToOriginal_kernel_le_oppositeBorel m hm)
    (negativeSimpleParabolic m) (fun b=>show oppositeBorel m≤negativeSimpleParabolic m b
      from le_sup_left) (negativeSimpleParabolic_injective m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMinimalParabolics
