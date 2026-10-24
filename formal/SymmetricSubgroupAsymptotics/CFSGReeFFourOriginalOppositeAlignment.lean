import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGReeFFourPerfectProjection
import SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment

/-! Positive-conjugator alignment descends through the actual surjection
onto the SAME original Ree derived/full-centre quotient for m>0. Only
the proved positive restriction is used; no quotient automorphism lifts
to the fixed group. The parameter m=0 is deliberately excluded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourPerfectProjection
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourFixedOppositeAlignment CFSGQuotientOppositeAlignment

theorem positive_original_image (m : ℕ) (hm : 0<m) :
    (fixedPositive m).map (fixedToOriginal m hm)=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) := by
  rw [reePositiveSylow_coe]
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact ⟨fixedToDerived m hm u,hu,rfl⟩
  · rintro _ ⟨u,hu,rfl⟩
    refine ⟨u.val,hu,?_⟩
    change derivedReeHom m (fixedToDerived m hm u.val)=derivedReeHom m u
    apply congrArg (derivedReeHom m)
    apply Subtype.ext
    rfl

def originalNegative (m : ℕ) (hm : 0<m) : Subgroup (CFSG.Models.ReeF4 m) :=
  (fixedNegative m).map (fixedToOriginal m hm)

theorem original_opposite_conjugate_by_positive (m : ℕ) (hm : 0<m)
    (g : CFSG.Models.ReeF4 m)
    (hdisj : (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m))⊓
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map
        (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)),
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map
        (MulAut.conj g).toMonoidHom=(originalNegative m hm).map
          (MulAut.conj b).toMonoidHom := by
  have h := opposite_alignment_map (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)
    (fixedPositive m) (fixedNegative m) (fixedPositive m)
    (fixedToOriginal_positive_injective m hm) (fixed_opposite_conjugate_by_positive m) g
  rw [positive_original_image] at h
  exact h hdisj

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOppositeAlignment
