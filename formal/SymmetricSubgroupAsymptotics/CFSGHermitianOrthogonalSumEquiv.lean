import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import Mathlib.LinearAlgebra.Projection

/-! Construct the ambient linear equivalence from two actual orthogonal
decompositions and pair-preserving maps on their components. This is an
explicit direct-sum construction, not an isometry-extension axiom. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSumEquiv
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)
variable (W C T D : Submodule K (I → K))

def sumEquiv (hWC : IsCompl W C) (hTD : IsCompl T D)
    (eW : W ≃ₗ[K] T) (eC : C ≃ₗ[K] D) : (I → K) ≃ₗ[K] (I → K) :=
  ((W.prodEquivOfIsCompl C hWC).symm.trans (eW.prodCongr eC)).trans
    (T.prodEquivOfIsCompl D hTD)

theorem sumEquiv_apply_sum (hWC : IsCompl W C) (hTD : IsCompl T D)
    (eW : W ≃ₗ[K] T) (eC : C ≃ₗ[K] D) (w : W) (c : C) :
    sumEquiv W C T D hWC hTD eW eC (w.val+c.val) = (eW w).val+(eC c).val := by
  change (T.prodEquivOfIsCompl D hTD)
    ((eW.prodCongr eC) ((W.prodEquivOfIsCompl C hWC).symm
      ((W.prodEquivOfIsCompl C hWC) (w,c)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem sumEquiv_apply_left (hWC : IsCompl W C) (hTD : IsCompl T D)
    (eW : W ≃ₗ[K] T) (eC : C ≃ₗ[K] D) (w : W) :
    sumEquiv W C T D hWC hTD eW eC w.val = (eW w).val := by
  have hh := sumEquiv_apply_sum W C T D hWC hTD eW eC w 0
  simpa only [ZeroMemClass.coe_zero,add_zero,map_zero] using hh

theorem sumEquiv_pair (hWC : IsCompl W C) (hTD : IsCompl T D)
    (eW : W ≃ₗ[K] T) (eC : C ≃ₗ[K] D)
    (hW : ∀ x y : W, hermitianPair sigma H (eW x).val (eW y).val = hermitianPair sigma H x.val y.val)
    (hC : ∀ x y : C, hermitianPair sigma H (eC x).val (eC y).val = hermitianPair sigma H x.val y.val)
    (hWCzero : Orthogonal sigma H W C) (hCWzero : Orthogonal sigma H C W)
    (hTDzero : Orthogonal sigma H T D) (hDTzero : Orthogonal sigma H D T)
    (x y : I → K) :
    hermitianPair sigma H (sumEquiv W C T D hWC hTD eW eC x)
      (sumEquiv W C T D hWC hTD eW eC y) = hermitianPair sigma H x y := by
  obtain ⟨⟨w,c⟩,rfl⟩ := (W.prodEquivOfIsCompl C hWC).surjective x
  obtain ⟨⟨t,d⟩,rfl⟩ := (W.prodEquivOfIsCompl C hWC).surjective y
  change hermitianPair sigma H (sumEquiv W C T D hWC hTD eW eC (w.val+c.val))
    (sumEquiv W C T D hWC hTD eW eC (t.val+d.val)) =
    hermitianPair sigma H (w.val+c.val) (t.val+d.val)
  rw [sumEquiv_apply_sum,sumEquiv_apply_sum,
    hermitianPair_add_left,hermitianPair_add_left,
    hermitianPair_add_right,hermitianPair_add_right,
    hermitianPair_add_right,hermitianPair_add_right,
    hW,hC,hWCzero _ w.property _ d.property,hCWzero _ c.property _ t.property,
    hTDzero _ (eW w).property _ (eC d).property,
    hDTzero _ (eC c).property _ (eW t).property]

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSumEquiv
