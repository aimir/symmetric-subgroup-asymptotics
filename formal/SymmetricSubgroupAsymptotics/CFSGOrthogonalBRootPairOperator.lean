import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularRootPlanes
import Mathlib.Tactic.FieldSimp

/-! The SAME original B long-root displacement is the literal bilinear
pair operator of its two natural vectors. Conjugation transports those
vectors by the SAME original elementary-group element. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGAlternatingPairOperator
variable {K : Type} [Field K]

theorem positiveVector_pairing (s : ℕ) (i : Fin (s + 3)) (v : Index (s + 3) → K) :
    (gram K (s + 3)).toBilin' (positiveVector (K := K) s i) v =
      2 * v (neg (s + 3) i) := by
  simp [positiveVector, Matrix.toBilin'_apply, gram, pos, neg,
    Fintype.sum_sum_type, Pi.single_apply, mul_ite, ite_mul]

theorem highestRoot_displacement_pairOperator (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    Matrix.mulVecLin (((highestRoot s a).val : Mat K (s + 3)) - 1) =
      (a / 2) • pairOperator (gram K (s + 3)).toBilin'
        (positiveVector (K := K) s 0) (positiveVector s (secondIndex s)) := by
  have hscale (z : K) : (a / 2) * (2 * z) = a * z := by
    field_simp
  apply LinearMap.ext
  intro x
  rw [Matrix.mulVecLin_apply, highestRoot_displacement h2]
  simp only [LinearMap.smul_apply, pairOperator_apply, positiveVector_pairing,
    smul_sub, smul_smul, hscale]

theorem conjugate_highestRoot_displacement_pairOperator (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) (a : K) :
    Matrix.mulVecLin (((g * highestRoot s a * g⁻¹).val : Mat K (s + 3)) - 1) =
      (a / 2) • pairOperator (gram K (s + 3)).toBilin'
        ((g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s 0)
        ((g.val : Mat K (s + 3)) *ᵥ positiveVector (K := K) s (secondIndex s)) := by
  let L := Matrix.mulVecLin (g.val : Mat K (s + 3))
  let R := Matrix.mulVecLin (↑(g.val⁻¹) : Mat K (s + 3))
  have hL (x y : Index (s + 3) → K) :
      (gram K (s + 3)).toBilin' (L x) (L y) = (gram K (s + 3)).toBilin' x y :=
    natural_pairing_invariant h2 (s + 3) g x y
  have hLR (x : Index (s + 3) → K) : L (R x) = x := by
    change (g.val : Mat K (s + 3)) *ᵥ ((↑(g.val⁻¹) : Mat K (s + 3)) *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hc := pairOperator_conjugation (gram K (s + 3)).toBilin' L R hL hLR
    (positiveVector (K := K) s 0) (positiveVector (K := K) s (secondIndex s))
  change Matrix.mulVecLin
    (((g.val * (highestRoot s a).val * g.val⁻¹ : (Mat K (s + 3))ˣ) : Mat K (s + 3)) - 1) = _
  rw [CFSGMatrixConjugateDisplacement.conjugate_sub_one,
    Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, highestRoot_displacement_pairOperator h2]
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun hc x
  change L (pairOperator (gram K (s + 3)).toBilin'
    (positiveVector (K := K) s 0) (positiveVector (K := K) s (secondIndex s)) (R x)) = _ at he
  change L ((a / 2) • pairOperator (gram K (s + 3)).toBilin'
    (positiveVector (K := K) s 0) (positiveVector (K := K) s (secondIndex s)) (R x)) = _
  rw [map_smul, he]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
