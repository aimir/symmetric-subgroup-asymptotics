import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelCenterWeights
import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateLongRoots

/-! Actual coordinate-torus words supply the two independent centre
weights. Every conjugator lies in the same original Borel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def coordinateTorusInB (r : ℕ) (i : Fin (r + 1)) (u : Kˣ) : borel K (r + 1) :=
  ⟨⟨coordinateTorusUnit K r i u, coordinateTorusUnit_mem K r i u⟩, by
    change (coordinateTorusUnit K r i u : Mat K (r + 1)).BlockTriangular (flagEquiv (r + 1))
    rw [coordinateTorusUnit_val]
    exact Matrix.blockTriangular_diagonal _⟩

theorem coordinateTorusInB_positive_diagonal (r : ℕ) (i j : Fin (r + 1)) (u : Kˣ) :
    ((coordinateTorusInB r i u).val.val : Mat K (r + 1)) (Sum.inl j) (Sum.inl j) =
      if j = i then (u : K) else 1 := by
  change (coordinateTorusUnit K r i u : Mat K (r + 1)) (Sum.inl j) (Sum.inl j) = _
  rw [coordinateTorusUnit_val]
  simp [coordinateTorusDiagonal]

theorem borel_diagonal_mul (r : ℕ) (g h : borel K (r + 1)) (i : Index (r + 1)) :
    ((g * h).val.val : Mat K (r + 1)) i i =
      (g.val.val : Mat K (r + 1)) i i * (h.val.val : Mat K (r + 1)) i i :=
  CFSGMatrixFlagSubgroups.upper_diag_mul (flagEquiv (r + 1)) g.property h.property i

variable [CharP K 2]

theorem secondTorus_center_action (r : ℕ) (hr : 0 < r) (u : Kˣ) (a b : K) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    (coordinateTorusInB r k u).val * (centerParameterElement r hr a b).val *
      (coordinateTorusInB r k u).val⁻¹ =
        (centerParameterElement r hr a (b * (u : K))).val := by
  dsimp only
  let k : Fin (r + 1) := ⟨1, by omega⟩
  have hk : (0 : Fin (r + 1)) ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have h0 : ((coordinateTorusInB r k u).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inl 0) = 1 := by
    simpa only [if_neg hk] using coordinateTorusInB_positive_diagonal r k 0 u
  have h1 : ((coordinateTorusInB r k u).val.val : Mat K (r + 1))
      (Sum.inl k) (Sum.inl k) = (u : K) := by
    simpa only [if_pos rfl] using coordinateTorusInB_positive_diagonal r k k u
  have h1' : ((coordinateTorusInB r k u).val.val : Mat K (r + 1))
      (Sum.inl (⟨1, by omega⟩ : Fin (r + 1))) (Sum.inl (⟨1, by omega⟩ : Fin (r + 1))) =
      (u : K) := h1
  simpa only [h0, h1', one_pow, mul_one] using
    borel_centerParameter_conjugation r hr (coordinateTorusInB r k u) a b

def leftWeightTorus (r : ℕ) (hr : 0 < r) (u : Kˣ) : borel K (r + 1) :=
  let k : Fin (r + 1) := ⟨1, by omega⟩
  coordinateTorusInB r 0 u * coordinateTorusInB r k u⁻¹

theorem leftWeightTorus_center_action (r : ℕ) (hr : 0 < r) (u : Kˣ) (a b : K) :
    (leftWeightTorus r hr u).val * (centerParameterElement r hr a b).val *
      (leftWeightTorus r hr u).val⁻¹ =
        (centerParameterElement r hr (a * (u : K) ^ 2) b).val := by
  let k : Fin (r + 1) := ⟨1, by omega⟩
  have hk : (0 : Fin (r + 1)) ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have h0 : ((leftWeightTorus r hr u).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inl 0) = (u : K) := by
    change ((coordinateTorusInB r 0 u * coordinateTorusInB r k u⁻¹).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inl 0) = _
    rw [borel_diagonal_mul, coordinateTorusInB_positive_diagonal,
      coordinateTorusInB_positive_diagonal]
    simp only [if_true, if_neg hk, mul_one]
  have h1 : ((leftWeightTorus r hr u).val.val : Mat K (r + 1))
      (Sum.inl k) (Sum.inl k) = ((u : K)⁻¹) := by
    change ((coordinateTorusInB r 0 u * coordinateTorusInB r k u⁻¹).val.val : Mat K (r + 1))
      (Sum.inl k) (Sum.inl k) = _
    rw [borel_diagonal_mul, coordinateTorusInB_positive_diagonal,
      coordinateTorusInB_positive_diagonal]
    simp only [if_neg (Ne.symm hk), if_true, one_mul, Units.val_inv_eq_inv_val]
  have h1' : ((leftWeightTorus r hr u).val.val : Mat K (r + 1))
      (Sum.inl (⟨1, by omega⟩ : Fin (r + 1))) (Sum.inl (⟨1, by omega⟩ : Fin (r + 1))) =
      ((u : K)⁻¹) := h1
  have h := borel_centerParameter_conjugation r hr (leftWeightTorus r hr u) a b
  simpa only [h0, h1', mul_assoc, mul_inv_cancel₀ (Units.ne_zero u), mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
