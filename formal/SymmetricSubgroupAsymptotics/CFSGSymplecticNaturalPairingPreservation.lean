import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionForm
import SymmetricSubgroupAsymptotics.CFSGSymplecticFormPreservation
import Mathlib.Tactic.Abel

/-! The checked matrix-form preservation is exactly preservation of
the natural alternating pairing used to label symplectic root groups. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem pairing_eq_neg_dot_J (r : ℕ) (v w : Index r → K) :
    pairing r v w = -(v ⬝ᵥ (Matrix.J (Fin r) K *ᵥ w)) := by
  rw [Matrix.J, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
    zero_add, add_zero, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.neg_apply, pairing, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  simp only [Function.comp_apply]
  abel

theorem elementary_preserves_pairing (r : ℕ) (g : elementaryRootGroup K r)
    (v w : Index r → K) :
    pairing r ((g.val : Mat K r) *ᵥ v) ((g.val : Mat K r) *ᵥ w) = pairing r v w := by
  have hform : (g.val : Mat K r).transpose * Matrix.J (Fin r) K *
      (g.val : Mat K r) = Matrix.J (Fin r) K :=
    _root_.SymplecticGroup.mem_iff'.mp (elementaryToSymplectic K r g).property
  rw [pairing_eq_neg_dot_J, pairing_eq_neg_dot_J]
  congr 1
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hform, ← Matrix.dotProduct_mulVec]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
