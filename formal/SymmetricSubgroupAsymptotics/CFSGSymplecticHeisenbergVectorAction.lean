import SymmetricSubgroupAsymptotics.CFSGSymplecticAdditiveOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergCoordinates

/-! The literal quotient-coordinate change (a,b) -> (b,-a) transports
the actual smaller elementary symplectic action. Actual original words
prove its nonzero transitivity. No full-field linearity is imposed on
any stabilizer subgroup to which this action is later applied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergVectorAction

open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticHeisenbergCoordinates
variable (K : Type) [Field K]

def vectorEquiv (m : ℕ) : ((Fin m → K) × (Fin m → K)) ≃ₗ[K] (Index m → K) where
  toFun v := Sum.elim v.2 (-v.1)
  invFun w := (-w ∘ Sum.inr, w ∘ Sum.inl)
  left_inv v := by
    apply Prod.ext <;> funext i <;> simp
  right_inv w := by
    funext i
    cases i <;> simp
  map_add' v w := by
    funext i
    cases i <;> simp [Pi.add_apply, Pi.neg_apply] <;> ring
  map_smul' a v := by
    funext i
    cases i <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

@[reducible] def vectorAction (m : ℕ) :
    MulAction (elementaryRootGroup K m) ((Fin m → K) × (Fin m → K)) where
  smul A v := (vectorEquiv K m).symm ((A.val : Mat K m) *ᵥ vectorEquiv K m v)
  one_smul v := by
    change (vectorEquiv K m).symm ((1 : Mat K m) *ᵥ vectorEquiv K m v) = v
    rw [Matrix.one_mulVec]
    exact (vectorEquiv K m).symm_apply_apply v
  mul_smul A B v := by
    change (vectorEquiv K m).symm (((A.val : Mat K m) * (B.val : Mat K m)) *ᵥ
      vectorEquiv K m v) =
        (vectorEquiv K m).symm ((A.val : Mat K m) *ᵥ vectorEquiv K m
          ((vectorEquiv K m).symm ((B.val : Mat K m) *ᵥ vectorEquiv K m v)))
    rw [(vectorEquiv K m).apply_symm_apply, Matrix.mulVec_mulVec]

local instance vectorActionInstance (m : ℕ) :
    MulAction (elementaryRootGroup K m) ((Fin m → K) × (Fin m → K)) := vectorAction K m

theorem vectorAction_apply (m : ℕ) (A : elementaryRootGroup K m)
    (v : (Fin m → K) × (Fin m → K)) :
    A • v = (vectorEquiv K m).symm ((A.val : Mat K m) *ᵥ vectorEquiv K m v) := rfl

theorem vectorAction_zero (m : ℕ) (A : elementaryRootGroup K m) :
    A • (0 : (Fin m → K) × (Fin m → K)) = 0 := by
  rw [vectorAction_apply, map_zero, Matrix.mulVec_zero, map_zero]

theorem vectorAction_nonzero_transitive (r : ℕ) (hr : 0 < r)
    (v w : (Fin (r + 1) → K) × (Fin (r + 1) → K)) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : elementaryRootGroup K (r + 1), A • v = w := by
  have hv' : vectorEquiv K (r + 1) v ≠ 0 := by
    intro hz
    exact hv ((vectorEquiv K (r + 1)).injective
      (hz.trans ((map_zero (vectorEquiv K (r + 1))).symm)))
  have hw' : vectorEquiv K (r + 1) w ≠ 0 := by
    intro hz
    exact hw ((vectorEquiv K (r + 1)).injective
      (hz.trans ((map_zero (vectorEquiv K (r + 1))).symm)))
  obtain ⟨A, hA⟩ := CFSGSymplecticAdditiveOrbitIndex.exists_map_nonzero K r hr
    (vectorEquiv K (r + 1) v) (vectorEquiv K (r + 1) w) hv' hw'
  refine ⟨A, ?_⟩
  rw [vectorAction_apply, hA]
  exact (vectorEquiv K (r + 1)).symm_apply_apply w

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergVectorAction
