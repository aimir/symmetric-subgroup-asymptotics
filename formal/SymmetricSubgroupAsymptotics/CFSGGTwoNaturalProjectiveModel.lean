import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalImageFaithful
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCenter
import SymmetricSubgroupAsymptotics.CFSGGTwoModelEvenOrder

/-! The original simple projective G2 model is equivalent to its
literal natural root group for fields of cardinality at least three.
Both the image-action kernel and actual natural centre are discharged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalProjectiveModel
open CFSGGTwoSerreMatrices CFSGGTwoNaturalImageFaithful CFSGGTwoNaturalCenter
open CFSG.Models.Chevalley
variable (K : Type) [Field K]

private def originalImageProjectiveEquiv [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Projective CartanMatrix.G₂ K ≃*
      naturalActionImage K ⧸ Subgroup.center (naturalActionImage K) := by
  let q := QuotientGroup.mk' (Subgroup.center (naturalActionImage K))
  have hne : q (imageLongWeyl K) ≠ 1 := by
    intro h
    exact imageLongWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (naturalActionImage K ⧸ Subgroup.center (naturalActionImage K)) :=
    ⟨⟨q (imageLongWeyl K), 1, hne⟩⟩
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (modelToNaturalImage K) (modelToNaturalImage_surjective K)

def naturalToOriginal [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    naturalGroup K →* Projective CartanMatrix.G₂ K :=
  (originalImageProjectiveEquiv K).symm.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (naturalActionImage K))).comp
      (naturalImageAction K).rangeRestrict)

theorem naturalToOriginal_surjective [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Function.Surjective (naturalToOriginal K) :=
  (originalImageProjectiveEquiv K).symm.surjective.comp
    ((QuotientGroup.mk'_surjective (Subgroup.center (naturalActionImage K))).comp
      (naturalImageAction K).rangeRestrict_surjective)

theorem naturalToOriginal_injective [Finite K] (hcard : 3 ≤ Nat.card K)
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Function.Injective (naturalToOriginal K) := by
  have hker (g : naturalGroup K) (hg : naturalToOriginal K g = 1) : g = 1 := by
    have hq := congrArg (originalImageProjectiveEquiv K) hg
    change (originalImageProjectiveEquiv K)
      ((originalImageProjectiveEquiv K).symm
        ((QuotientGroup.mk' (Subgroup.center (naturalActionImage K)))
          ((naturalImageAction K).rangeRestrict g))) =
      (originalImageProjectiveEquiv K) 1 at hq
    rw [MulEquiv.apply_symm_apply, map_one] at hq
    have hc := (QuotientGroup.eq_one_iff _).mp hq
    have hgc : g ∈ Subgroup.center (naturalGroup K) := by
      apply Subgroup.mem_center_iff.mpr
      intro h
      apply naturalImageAction_injective K
      have he := congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hc) ((naturalImageAction K).rangeRestrict h))
      simpa only [map_mul] using he
    rw [center_eq_bot K hcard] at hgc
    exact Subgroup.mem_bot.mp hgc
  intro g h he
  have hk : naturalToOriginal K (g⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  exact inv_mul_eq_one.mp (hker (g⁻¹ * h) hk)

def naturalEquivOriginal [Finite K] (hcard : 3 ≤ Nat.card K)
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    naturalGroup K ≃* Projective CartanMatrix.G₂ K :=
  MulEquiv.ofBijective (naturalToOriginal K)
    ⟨naturalToOriginal_injective K hcard, naturalToOriginal_surjective K⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalProjectiveModel
