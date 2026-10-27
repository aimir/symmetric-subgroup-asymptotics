import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreOuterReduction

/-! Actual original-model chart of the normalized M24 swap fibre.
No presentation recovery, automorphism extension, or finite acceptance
capacity is assumed. The two-point tail chart supplies the actual cover. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreChart
open CFSG.Certificates.Mathieu24
open CFSGMathieuTwentyFourTwoPointTailCover

private theorem mul_val_apply (g h : M24) (p : Fin 24) :
    (g*h).val p=g.val (h.val p) := rfl

private theorem subgroup_representation_binding {A X : Type*} [Group A]
    (H : Subgroup (Equiv.Perm X)) (rho : A →* H) (a : A) :
    (H.subtype.comp rho) a=(rho a).val := rfl

private theorem frame_forward_apply (x t k : M24) (p : Fin 24) :
    (x*t*k*t⁻¹).val p=x.val (t.val (k.val (t.val.symm p))) := rfl

private theorem frame_inverse_apply (x t k : M24) (p : Fin 24) :
    (x*t*k*t⁻¹).val.symm p=
      t.val (k.val.symm (t.val.symm (x.val.symm p))) := by
  change ((x*t*k*t⁻¹)⁻¹).val p=_
  simp only [mul_inv_rev,inv_inv,mul_val_apply]
  rfl

/-- The forward scalar composition for h=x*t*k*t^-1. -/
def candidateForward (c : Code) (p : Fin 24) : Fin 24 :=
  CFSGMathieuTwentyFourPresentationWords.x.val
    (transport.val ((decode c).val (transport.val.symm p)))

/-- The inverse scalar composition is t*k^-1*t^-1*x^-1. -/
def candidateInverse (c : Code) (p : Fin 24) : Fin 24 :=
  transport.val ((decode c).val.symm
    (transport.val.symm (CFSGMathieuTwentyFourPresentationWords.x.val.symm p)))

theorem candidateForward_eq (c : Code) (p : Fin 24) :
    candidateForward c p=(swapDecode c).val p := by
  exact (frame_forward_apply CFSGMathieuTwentyFourPresentationWords.x
    transport (decode c) p).symm

theorem candidateInverse_eq (c : Code) (p : Fin 24) :
    candidateInverse c p=(swapDecode c).val.symm p := by
  exact (frame_inverse_apply CFSGMathieuTwentyFourPresentationWords.x
    transport (decode c) p).symm


theorem candidateInverse_forward (c : Code) (p : Fin 24) :
    candidateInverse c (candidateForward c p)=p := by
  rw [candidateInverse_eq,candidateForward_eq]
  exact (swapDecode c).val.symm_apply_apply p

theorem candidateForward_inverse (c : Code) (p : Fin 24) :
    candidateForward c (candidateInverse c p)=p := by
  rw [candidateForward_eq,candidateInverse_eq]
  exact (swapDecode c).val.apply_symm_apply p

/-- Every actual source-generator image in the normalized fibre has a
code in the original stabilizer chart. Only the image element is acted on. -/
theorem swapFibre_image_has_code
    (f : CFSGMathieuTwentyFourSwapFibreOuterReduction.SwapFibre) :
    ∃ c : Code, (swapDecode c).val=
      CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX) := by
  have hbind (a : CFSG.Models.Presentations.M24.Model) :
      (CFSGMathieuTwentyFourActualRepresentation.representation a).val=
        CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation a := by
    unfold CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
    exact (subgroup_representation_binding
      CFSG.Certificates.Mathieu24.M24Subgroup
      CFSGMathieuTwentyFourActualRepresentation.representation a).symm
  obtain ⟨g,hg⟩ : ∃ g : M24, g.val=
      CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX) :=
    ⟨CFSGMathieuTwentyFourActualRepresentation.representation
      (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX),hbind _⟩
  have hg8 : g.val (8 : Fin 24)=11 := by
    rw [hg]
    exact f.property.trans CFSGMathieuTwentyFourSwapFibreOuterReduction.x_image_base
  have hg11 : g.val (11 : Fin 24)=8 := by
    rw [hg]
    exact (congrArg
      (CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX))
      CFSGMathieuTwentyFourSwapFibreOuterReduction.x_image_base.symm).trans
        (CFSGMathieuTwentyFourSwapFibreOuterReduction.swap_fibre_reverse f)
  obtain ⟨c,hc⟩ := swapDecode_surjective_on_swap g hg8 hg11
  exact ⟨c,(congrArg Subtype.val hc).trans hg⟩

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreChart
