import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleCoordinates
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays

/-! Coordinate-root matching for the actual all-characteristic pole
shear. A positive tail-coordinate parameter gives the original upper
skew root with its exact minus parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGSplitQuadraticPoleCoordinates CFSGSplitQuadraticBasisParameters
open CFSGOrthogonalDGenerationRootArrays CFSGQuadraticHyperbolicShear
variable (K : Type) [Field K]

theorem positive_head (n : ℕ) (z : Index n → K) (v : Index (n + 1) → K) :
    poleShear K n z v (Sum.inl 0) = v (Sum.inl 0) -
      QuadraticMap.polar (CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm K n)
        z (v ∘ tailIndex n) -
      CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm K n z * v (Sum.inr 0) :=
  congrArg Prod.fst (coordinates_poleShear K n z v)

theorem negative_head (n : ℕ) (z : Index n → K) (v : Index (n + 1) → K) :
    poleShear K n z v (Sum.inr 0) = v (Sum.inr 0) :=
  congrArg (fun x : K × ((Index n → K) × K) => x.2.2) (coordinates_poleShear K n z v)

theorem tail_action (n : ℕ) (z : Index n → K) (v : Index (n + 1) → K) (i : Index n) :
    poleShear K n z v (tailIndex n i) = v (tailIndex n i) + v (Sum.inr 0) * z i :=
  congrArg (fun x : K × ((Index n → K) × K) => x.2.1 i) (coordinates_poleShear K n z v)

theorem poleShear_zero_apply (n : ℕ) (v : Index (n + 1) → K) :
    poleShear K n 0 v = v := by
  apply (coordinateEquiv K n).injective
  change coordinates K n (poleShear K n 0 v) = coordinates K n v
  rw [coordinates_poleShear, transform_zero]

theorem poleShear_add_apply (n : ℕ) (z t : Index n → K) (v : Index (n + 1) → K) :
    poleShear K n (z + t) v = poleShear K n z (poleShear K n t v) := by
  apply (coordinateEquiv K n).injective
  change coordinates K n (poleShear K n (z + t) v) =
    coordinates K n (poleShear K n z (poleShear K n t v))
  rw [coordinates_poleShear, coordinates_poleShear, coordinates_poleShear]
  exact (transform_comp _ z t _).symm

theorem positive_single_action (n : ℕ) (j : Fin n) (a : K) (v : Index (n + 1) → K) :
    poleShear K n (Pi.single (Sum.inl j) a) v =
      plusArray (0 : Fin (n + 1)) j.succ (-a) *ᵥ v := by
  apply (coordinateEquiv K n).injective
  change coordinates K n (poleShear K n (Pi.single (Sum.inl j) a) v) =
    coordinates K n (plusArray (0 : Fin (n + 1)) j.succ (-a) *ᵥ v)
  apply Prod.ext
  · change poleShear K n (Pi.single (Sum.inl j) a) v (Sum.inl 0) = _
    rw [positive_head]
    simp [coordinates, positive_norm, positive_polar, plusArray,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
      Function.update_apply, tailIndex, Function.comp_apply,
      Fin.succ_ne_zero j, Ne.symm (Fin.succ_ne_zero j)] <;> ring
  · apply Prod.ext
    · funext i
      change poleShear K n (Pi.single (Sum.inl j) a) v (tailIndex n i) = _
      rw [tail_action]
      cases i with
      | inl k =>
        by_cases hk : k = j
        · subst k
          simp [coordinates, plusArray, Matrix.add_mulVec, Matrix.sub_mulVec,
            Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
            tailIndex, Function.comp_apply, Pi.single_apply,
            Fin.succ_ne_zero j, Ne.symm (Fin.succ_ne_zero j)] <;> ring
        · simp [coordinates, plusArray, Matrix.add_mulVec, Matrix.sub_mulVec,
            Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
            tailIndex, Function.comp_apply, Pi.single_apply, hk, Ne.symm hk,
            Fin.succ_ne_zero k, Ne.symm (Fin.succ_ne_zero k)] <;> ring
      | inr k =>
        simp [coordinates, plusArray, Matrix.add_mulVec, Matrix.sub_mulVec,
          Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
          tailIndex, Function.comp_apply, Pi.single_apply]
    · change poleShear K n (Pi.single (Sum.inl j) a) v (Sum.inr 0) = _
      rw [negative_head]
      simp [coordinates, plusArray, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply]

end SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootAction
