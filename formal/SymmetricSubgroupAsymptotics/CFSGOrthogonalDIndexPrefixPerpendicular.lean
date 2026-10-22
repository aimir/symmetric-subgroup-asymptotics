import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixNormalizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm

/-! The perpendicular half of the same partial natural flag. Quadratic
polar preservation transports the already intrinsic positive prefixes;
this does not separate the final hyperbolic pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPrefixNormalizer CFSGMatrixFlagNormalizer
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def positivePerpendicular (r k : ℕ) : Submodule K (Index r → K) where
  carrier := {x | ∀ i : Fin r, i.val < k → x (Sum.inr i) = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro x y hx hy i hi
    simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro a x hx i hi
    simp only [Pi.smul_apply, hx i hi, smul_zero]

theorem prefix_polar_zero (r k : ℕ) (hk : k ≤ r)
    (v x : Index r → K)
    (hv : v ∈ flagPrefix (K := K) (flagEquiv r) k)
    (hx : x ∈ positivePerpendicular K r k) : polar K v x = 0 := by
  have hneg (j : Fin r) : v (Sum.inr j) = 0 := hv (Sum.inr j) (by
    change k ≤ r + (Fin.rev j).val
    omega)
  have hsum : leftPart K v ⬝ᵥ rightPart K x = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < k
    · change v (Sum.inl j) * x (Sum.inr j) = 0
      rw [hx j hj, mul_zero]
    · change v (Sum.inl j) * x (Sum.inr j) = 0
      rw [hv (Sum.inl j) (by change k ≤ j.val; omega), zero_mul]
  have hsum' : leftPart K x ⬝ᵥ rightPart K v = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    change x (Sum.inl j) * v (Sum.inr j) = 0
    rw [hneg j, mul_zero]
  exact (congrArg₂ (· + ·) hsum hsum').trans (zero_add 0)

theorem polar_positive_basis (r : ℕ) (i : Fin r) (x : Index r → K) :
    polar K (Pi.single (Sum.inl i) 1) x = x (Sum.inr i) := by
  simp [polar, leftPart, rightPart, Pi.single_apply, dotProduct, eq_comm]

theorem normalizer_preserves_positivePerpendicular (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (k : ℕ) (hk : k < s + 4) (x : Index (s + 4) → K)
    (hx : x ∈ positivePerpendicular K (s + 4) k) :
    (A.val : Mat K (s + 4)) *ᵥ x ∈ positivePerpendicular K (s + 4) k := by
  intro j hj
  have hv : Pi.single (Sum.inl j) (1 : K) ∈
      flagPrefix (K := K) (flagEquiv (s + 4)) k := by
    intro i hi
    have hne : i ≠ Sum.inl j := by
      intro he
      subst i
      change k ≤ j.val at hi
      omega
    exact Pi.single_eq_of_ne hne 1
  have hAi : A⁻¹ ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))) :=
    (Subgroup.normalizer _).inv_mem hA
  have hv' := normalizer_preserves_positivePrefix K s A⁻¹ hAi k hk _ hv
  have hz := prefix_polar_zero K (s + 4) k (by omega) _ x hv' hx
  have hp := elementary_preserves_polar K s A
    (((A⁻¹).val : Mat K (s + 4)) *ᵥ Pi.single (Sum.inl j) 1) x
  have hiM : (A.val : Mat K (s + 4)) * ((A⁻¹).val : Mat K (s + 4)) = 1 := by
    have he := map_mul (naturalMatrixHom K (s + 4)) A A⁻¹
    rw [mul_inv_cancel, map_one] at he
    exact he.symm
  rw [Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec, polar_positive_basis] at hp
  exact hp.trans hz

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular
