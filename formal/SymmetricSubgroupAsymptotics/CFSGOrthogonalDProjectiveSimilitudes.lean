import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSimilitudeGroup
import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
import Mathlib.GroupTheory.Index

/-! The actual similitude group acts on the SAME original Q-singular
points. All scalar units lie in its kernel and inject there. Cancelling
this contained scalar subgroup, without a converse kernel-recognition
claim, bounds the actual point-image order by the original isometry order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveSimilitudes
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveGraph
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDSimilitudeGroup
variable (K : Type) [Field K]

def pointHom (r : ℕ) : similitudes K r →* Equiv.Perm (Points (splitQuadraticForm K r)) where
  toFun g := CFSGQuadraticSimilitudeGeometry.pointEquiv (splitQuadraticForm K r)
    (ambientLinearEquiv K r g.val) (multiplier K r g : K) (multiplier K r g).ne_zero
    (fun x => by
      rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
      exact multiplier_spec K r g x)
  map_one' := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (Matrix.mulVecLin (1 : Mat K r)) = P.val
    rw [Matrix.mulVecLin_one, Submodule.map_id]
  map_mul' g h := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change P.val.map (Matrix.mulVecLin ((g.val : Mat K r) * (h.val : Mat K r))) =
      (P.val.map (Matrix.mulVecLin (h.val : Mat K r))).map
        (Matrix.mulVecLin (g.val : Mat K r))
    rw [Matrix.mulVecLin_mul, Submodule.map_comp]

theorem pointHom_apply_val (r : ℕ) (g : similitudes K r)
    (P : Points (splitQuadraticForm K r)) :
    (pointHom K r g P).val = P.val.map (Matrix.mulVecLin (g.val : Mat K r)) := rfl

def scalarWeightsHom (r : ℕ) : Kˣ →* (Index r → Kˣ) where
  toFun c _ := c
  map_one' := rfl
  map_mul' _ _ := rfl

def scalarUnitsHom (r : ℕ) : Kˣ →* (Mat K r)ˣ :=
  (CFSGDiagonalMatrixUnits.diagonalHom (Index r) K).comp (scalarWeightsHom K r)

theorem scalarUnits_action (r : ℕ) (c : Kˣ) (v : Index r → K) :
    (scalarUnitsHom K r c : Mat K r) *ᵥ v = (c : K) • v := by
  change Matrix.diagonal (fun _ : Index r => (c : K)) *ᵥ v = _
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

def scalarElement (r : ℕ) (c : Kˣ) : similitudes K r :=
  ⟨scalarUnitsHom K r c, c ^ 2, by
    intro v
    rw [scalarUnits_action]
    have h := (splitQuadraticForm K r).map_smul (c : K) v
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply] at h
    simpa only [Units.val_pow_eq_pow_val, pow_two, smul_eq_mul] using h⟩

theorem scalar_mem_ker (r : ℕ) (c : Kˣ) : scalarElement K r c ∈ (pointHom K r).ker := by
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro P
  apply Subtype.ext
  rw [pointHom_apply_val]
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    change (scalarUnitsHom K r c : Mat K r) *ᵥ v ∈ P.val
    rw [scalarUnits_action]
    exact P.val.smul_mem _ hv
  · intro v hv
    refine ⟨((c⁻¹ : Kˣ) : K) • v, P.val.smul_mem _ hv, ?_⟩
    change (scalarUnitsHom K r c : Mat K r) *ᵥ (((c⁻¹ : Kˣ) : K) • v) = v
    rw [scalarUnits_action, smul_smul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul]

def scalarToKernel (r : ℕ) (c : Kˣ) : (pointHom K r).ker :=
  ⟨scalarElement K r c, scalar_mem_ker K r c⟩

theorem scalarToKernel_injective (r : ℕ) (hr : 0 < r) : Function.Injective (scalarToKernel K r) := by
  intro c d he
  let i : Index r := Sum.inl ⟨0, hr⟩
  apply Units.ext
  have h := congrArg (fun g : (pointHom K r).ker => (g.val.val : Mat K r) i i) he
  change Matrix.diagonal (fun _ : Index r => (c : K)) i i =
    Matrix.diagonal (fun _ : Index r => (d : K)) i i at h
  simpa only [Matrix.diagonal_apply_eq] using h

theorem pointImage_card_le_quadratic [Finite K] (r : ℕ) (hr : 0 < r) :
    Nat.card (pointHom K r).range ≤ Nat.card (quadraticPreserving K r) := by
  have hk : Nat.card Kˣ ≤ Nat.card (pointHom K r).ker :=
    Nat.card_le_card_of_injective (scalarToKernel K r) (scalarToKernel_injective K r hr)
  have he := (pointHom K r).ker.card_mul_index
  rw [Subgroup.index_ker] at he
  have hbound : Nat.card Kˣ * Nat.card (pointHom K r).range ≤
      Nat.card Kˣ * Nat.card (quadraticPreserving K r) := by
    calc
      Nat.card Kˣ * Nat.card (pointHom K r).range ≤
          Nat.card (pointHom K r).ker * Nat.card (pointHom K r).range := Nat.mul_le_mul_right _ hk
      _ = Nat.card (similitudes K r) := he
      _ = _ := similitudes_card K r hr
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := Kˣ))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveSimilitudes
