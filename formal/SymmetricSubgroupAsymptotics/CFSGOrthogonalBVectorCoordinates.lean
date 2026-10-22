import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-! Literal positive/negative/middle vector coordinates for the SAME B
SL-chain embedding and quadratic short-root words. These are the
Gaussian-normalization primitives, with all scalar coefficients retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
open CFSGOrthogonalBGenerationShortArrays
variable (K : Type) [Field K]

def positivePart (n : ℕ) (v : Index n → K) : Fin n → K := fun i => v (pos n i)
def negativePart (n : ℕ) (v : Index n → K) : Fin n → K := fun i => v (neg n i)

theorem doubleIntoElementary_val (n : ℕ) (A : NaturalSL K n) :
    ((doubleIntoElementary K n A).val : Mat K n) =
      Matrix.fromBlocks (Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose) 0 0 1 := rfl

theorem double_positivePart (n : ℕ) (A : NaturalSL K n) (v : Index n → K) :
    positivePart K n (((doubleIntoElementary K n A).val : Mat K n) *ᵥ v) =
      A.val *ᵥ positivePart K n v := by
  rw [doubleIntoElementary_val]
  funext i
  simp [positivePart, pos, Matrix.fromBlocks_mulVec, Function.comp_def]
  rfl

theorem double_negativePart (n : ℕ) (A : NaturalSL K n) (v : Index n → K) :
    negativePart K n (((doubleIntoElementary K n A).val : Mat K n) *ᵥ v) =
      (A⁻¹).val.transpose *ᵥ negativePart K n v := by
  rw [doubleIntoElementary_val]
  funext i
  simp [negativePart, neg, Matrix.fromBlocks_mulVec, Function.comp_def]
  rfl

theorem double_middle (n : ℕ) (A : NaturalSL K n) (v : Index n → K) :
    ((((doubleIntoElementary K n A).val : Mat K n) *ᵥ v) (middle n)) = v (middle n) := by
  rw [doubleIntoElementary_val]
  simp [middle, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem shortUnit_vector_action (n : ℕ) (b : Fin n ⊕ Fin n) (a : K) (v : Index n → K) :
    (shortUnit K n b a : Mat K n) *ᵥ v = v +
      (a * v (middle n) - a ^ 2 * v (Sum.inl (paired n b))) • Pi.single (Sum.inl b) 1 +
        ((-2) * a * v (Sum.inl (paired n b))) • Pi.single (middle n) 1 := by
  rw [shortUnit_val]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    shortArray, shortSecond, Matrix.sub_mulVec, Matrix.single_mulVec]
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Function.update_apply,
    Pi.single_apply, Pi.zero_apply, smul_eq_mul]
  split_ifs <;> ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
