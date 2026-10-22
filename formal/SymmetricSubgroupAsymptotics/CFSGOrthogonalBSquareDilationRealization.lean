import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNegativeDilation

/-! An actual square ratio on the original zero-middle points is
realized by a literal determinant-one paired GL scalar lift. The ratio
is on the NEGATIVE projection: [x+y] ↦ [x+t y]. No claim that t is square
is made here; that genuine geometric obligation remains separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSquareDilationRealization
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBGeneralLinearLift CFSGOrthogonalBGeneralLinearForm
open CFSGOrthogonalBSpecialFormGroup
variable (K : Type) [Field K]

abbrev ratioMap (n : ℕ) (t : K) := CFSGOrthogonalBNegativeDilation.map K n t

def pairedUnit (n : ℕ) (u : Kˣ) : (Mat K n)ˣ :=
  generalLinearLift K n (CFSGMatrixDiagonalBlockLift.diagonalUnit (fun _ => u⁻¹))

theorem pairedUnit_mem_special (n : ℕ) (u : Kˣ) : pairedUnit K n u ∈ specialFormUnits K n :=
  generalLinearLift_mem_special K n _

theorem pairedUnit_val (n : ℕ) (u : Kˣ) :
    (pairedUnit K n u : Mat K n) = Matrix.fromBlocks
      (Matrix.fromBlocks (Matrix.diagonal (fun _ => ((u⁻¹ : Kˣ) : K))) 0 0
        (Matrix.diagonal (fun _ => (u : K)))) 0 0 1 := by
  change (generalLinearLift K n
    (CFSGMatrixDiagonalBlockLift.diagonalUnit (fun _ => u⁻¹)) : Mat K n) = _
  rw [generalLinearLift_val]
  change Matrix.fromBlocks (Matrix.fromBlocks
      (Matrix.diagonal (fun _ : Fin n => ((u⁻¹ : Kˣ) : K))) 0 0
        (Matrix.diagonal (fun _ : Fin n => (((u⁻¹)⁻¹ : Kˣ) : K))).transpose) 0 0 1 = _
  rw [inv_inv, Matrix.diagonal_transpose]

theorem pairedUnit_positive (n : ℕ) (u : Kˣ) (v : Index n → K) (i : Fin n) :
    ((pairedUnit K n u : Mat K n) *ᵥ v) (pos n i) = ((u⁻¹ : Kˣ) : K) * v (pos n i) := by
  rw [pairedUnit_val]
  simp [Matrix.fromBlocks_mulVec, Matrix.mulVec_diagonal, pos, Function.comp_def]

theorem pairedUnit_negative (n : ℕ) (u : Kˣ) (v : Index n → K) (i : Fin n) :
    ((pairedUnit K n u : Mat K n) *ᵥ v) (neg n i) = (u : K) * v (neg n i) := by
  rw [pairedUnit_val]
  simp [Matrix.fromBlocks_mulVec, Matrix.mulVec_diagonal, neg, Function.comp_def]

theorem pairedUnit_middle (n : ℕ) (u : Kˣ) (v : Index n → K) :
    ((pairedUnit K n u : Mat K n) *ᵥ v) (middle n) = v (middle n) := by
  rw [pairedUnit_val]
  simp [Matrix.fromBlocks_mulVec, middle]

theorem square_ratio_vector (n : ℕ) (u : Kˣ) (v : Index n → K)
    (hm : v (middle n) = 0) :
    ratioMap K n ((u : K) ^ 2) v = (u : K) • ((pairedUnit K n u : Mat K n) *ᵥ v) := by
  funext i
  rcases i with (i | i) | ⟨⟩
  · change v (pos n i) = (u : K) * ((pairedUnit K n u : Mat K n) *ᵥ v) (pos n i)
    rw [pairedUnit_positive, Units.val_inv_eq_inv_val]
    change v (pos n i) = (u : K) * ((u : K)⁻¹ * v (pos n i))
    rw [← mul_assoc, mul_inv_cancel₀ u.ne_zero, one_mul]
  · change (u : K) ^ 2 * v (neg n i) =
      (u : K) * ((pairedUnit K n u : Mat K n) *ᵥ v) (neg n i)
    rw [pairedUnit_negative]
    ring
  · change v (middle n) = (u : K) * ((pairedUnit K n u : Mat K n) *ᵥ v) (middle n)
    rw [pairedUnit_middle, hm, mul_zero]

theorem map_eq_of_scalar_on_submodule {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (P : Submodule K V) (f g : V →ₗ[K] W)
    (c : K) (hc : c ≠ 0) (he : ∀ v ∈ P, f v = c • g v) : P.map f = P.map g := by
  apply le_antisymm
  · rintro y ⟨v, hv, rfl⟩
    rw [he v hv]
    exact (P.map g).smul_mem c ⟨v, hv, rfl⟩
  · rintro y ⟨v, hv, rfl⟩
    have hm : c⁻¹ • f v ∈ P.map f := (P.map f).smul_mem _ ⟨v, hv, rfl⟩
    rw [he v hv, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
    exact hm

theorem square_ratio_submodule (n : ℕ) (u : Kˣ) (P : Submodule K (Index n → K))
    (hm : ∀ v ∈ P, v (middle n) = 0) :
    P.map (ratioMap K n ((u : K) ^ 2)) = P.map (pairedUnit K n u : Mat K n).mulVecLin :=
  map_eq_of_scalar_on_submodule K P _ _ (u : K) u.ne_zero
    (fun v hv => square_ratio_vector K n u v (hm v hv))

theorem exists_special_square_ratio (n : ℕ) (t : K)
    (ht : ∃ u : K, u ≠ 0 ∧ u ^ 2 = t) :
    ∃ g : specialFormUnits K n, ∀ P : Submodule K (Index n → K),
      (∀ v ∈ P, v (middle n) = 0) →
        P.map (ratioMap K n t) = P.map (g.val : Mat K n).mulVecLin := by
  obtain ⟨u, hu, hut⟩ := ht
  let a : Kˣ := Units.mk0 u hu
  refine ⟨⟨pairedUnit K n a, pairedUnit_mem_special K n a⟩, ?_⟩
  intro P hm
  change P.map (ratioMap K n t) = P.map (pairedUnit K n a : Mat K n).mulVecLin
  rw [← hut]
  exact square_ratio_submodule K n a P hm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSquareDilationRealization
