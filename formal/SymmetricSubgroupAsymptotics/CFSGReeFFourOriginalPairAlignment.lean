import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleParabolic
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
import SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment

/-! Every automorphism of the SAME original Ree quotient can be adjusted
by an inner automorphism to preserve the literal positive and negative
Sylow images. Mutual disjointness uses the proved central-kernel theorem,
not two separate injectivity assertions. No automorphism lift or ordinary
F4 simplicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairAlignment
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedAmbientHom CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedPositiveSylow CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourOriginalOppositeAlignment CFSGReeFFourOriginalMiddleParabolic
open CFSGReeFFourDerivedOppositeSylow CFSGSubgroupConjugateRestriction
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)
private instance originalFinite (m : ℕ) : Finite (CFSG.Models.ReeF4 m) :=
  Finite.of_surjective (derivedReeHom m) (derivedReeHom_surjective m)

def originalOppositeSylow (m : ℕ) (hm : 0<m) : Sylow 2 (CFSG.Models.ReeF4 m) :=
  (reePositiveSylow m hm).mapSurjective
    (f:=(MulAut.conj (fixedToOriginal m hm (oppositionFixed m))).toMonoidHom)
    (MulAut.conj (fixedToOriginal m hm (oppositionFixed m))).surjective

theorem originalOppositeSylow_coe (m : ℕ) (hm : 0<m) :
    (originalOppositeSylow m hm : Subgroup (CFSG.Models.ReeF4 m))=originalNegative m hm := by
  change (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map
    (MulAut.conj (fixedToOriginal m hm (oppositionFixed m))).toMonoidHom=
      (fixedNegative m).map (fixedToOriginal m hm)
  rw [←positive_original_image,←map_conjugate,fixed_positive_image_eq_fixed_negative]

theorem original_opposite_sylows_disjoint (m : ℕ) (hm : 0<m) :
    (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m))⊓
      (originalOppositeSylow m hm : Subgroup (CFSG.Models.ReeF4 m))=⊥ := by
  have hP : IsPGroup 2 (fixedPositive m) :=
    fixedPositiveSylow_coe m ▸ (fixedPositiveSylow m).isPGroup'
  have hV : IsPGroup 2 (fixedNegative m) := by
    rw [←fixed_positive_image_eq_fixed_negative]
    exact hP.map (MulAut.conj (oppositionFixed m)).toMonoidHom
  have hi : Function.Injective ((fixedToOriginal m hm).comp
      (fixedPositiveSylow m : Subgroup (originalModelFixed m)).subtype) := by
    exact (congrArg (fun P : Subgroup (originalModelFixed m)=>
      Function.Injective ((fixedToOriginal m hm).comp P.subtype))
      (fixedPositiveSylow_coe m)).mpr (fixedToOriginal_positive_injective m hm)
  have hd := CFSGCentralKernelPElements.disjoint_map (fixedToOriginal m hm)
    (fixedPositiveSylow m) hi (fixedToOriginal_kernel_le_center m hm)
    (fixedPositive m) (fixedNegative m) hP hV (fixed_positive_inf_negative m)
  rw [positive_original_image] at hd
  rw [originalOppositeSylow_coe]
  exact hd

theorem original_negative_is_sylow (m : ℕ) (hm : 0<m) :
    ∃S : Sylow 2 (CFSG.Models.ReeF4 m),(S : Subgroup (CFSG.Models.ReeF4 m))=originalNegative m hm ∧
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m))⊓
        (S : Subgroup (CFSG.Models.ReeF4 m))=⊥ :=
  ⟨originalOppositeSylow m hm,originalOppositeSylow_coe m hm,
    original_opposite_sylows_disjoint m hm⟩

theorem original_exists_inner_fix_pair (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m)) :
    ∃g : CFSG.Models.ReeF4 m,
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map
        (MulAut.conj g*f).toMonoidHom=(reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) ∧
      (originalNegative m hm).map (MulAut.conj g*f).toMonoidHom=originalNegative m hm :=
  CFSGOppositeSylowOfAlignment.exists_inner_fix_pair (reePositiveSylow m hm)
    (originalOppositeSylow m hm) (originalNegative m hm)
    (original_opposite_sylows_disjoint m hm) (original_opposite_conjugate_by_positive m hm) f

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairAlignment
