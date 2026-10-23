import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPairTailMatrices
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailLinearExtension

/-! An actual quadratic isometry fixing the first hyperbolic pair is
exactly a tail extension of an actual smaller quadratic isometry. The
proof retains Q itself in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDQuadraticPairTail
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
variable (K : Type) [Field K]

theorem pairing_first_negative (n : ℕ) (v : Index (n + 1) → K) :
    polar K (Pi.single (Sum.inr (0 : Fin (n + 1))) 1) v = v (Sum.inl 0) := by
  simp [polar, leftPart, rightPart, dotProduct, Pi.single_apply, mul_ite]

theorem exists_quadratic_tail (n : ℕ) (u : (Mat K (n + 1))ˣ)
    (hQ : u ∈ quadraticPreserving K (n + 1))
    (hp : (u : Mat K (n + 1)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (hn : (u : Mat K (n + 1)) *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1) :
    ∃ a : quadraticPreserving K n, tailUnitHom K n a.val = u := by
  have hB (v w : Index (n + 1) → K) :
      polar K ((u : Mat K (n + 1)) *ᵥ v) ((u : Mat K (n + 1)) *ᵥ w) = polar K v w := by
    have h := hQ (v + w)
    rw [Matrix.mulVec_add, splitQ_add, splitQ_add, hQ v, hQ w] at h
    exact add_left_cancel h
  have hrp (v : Index (n + 1) → K) :
      ((u : Mat K (n + 1)) *ᵥ v) (Sum.inl 0) = v (Sum.inl 0) := by
    have h := hB (Pi.single (Sum.inr 0) 1) v
    rw [hn, pairing_first_negative, pairing_first_negative] at h
    exact h
  have hrn (v : Index (n + 1) → K) :
      ((u : Mat K (n + 1)) *ᵥ v) (Sum.inr 0) = v (Sum.inr 0) := by
    have h := hB (Pi.single (Sum.inl 0) 1) v
    rw [hp, pairing_first_positive, pairing_first_positive] at h
    exact h
  obtain ⟨a, ha⟩ := CFSGOrthogonalDPairTailMatrices.exists_tail_unit K n u hp hn hrp hrn
  have haQ : a ∈ quadraticPreserving K n := by
    intro x
    have ht : tailRestriction K n ((u : Mat K (n + 1)) *ᵥ tailExtension K n x) =
        (a : Mat K n) *ᵥ x := by
      rw [← ha]
      funext i
      change (tailMatrixHom K n (a : Mat K n) *ᵥ tailExtension K n x)
        (tailEquiv n (Sum.inl i)) = _
      rw [tailMatrixHom_mulVec_at_equiv]
      have he : tailExtension K n x ∘ tailEquiv n = Sum.elim x (fun _ => (0 : K)) := by
        funext j
        simp only [tailExtension, LinearMap.coe_mk, AddHom.coe_mk,
          Function.comp_apply, (tailEquiv n).symm_apply_apply]
      rw [he, Matrix.fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Matrix.zero_mulVec, add_zero]
    have hy : ((u : Mat K (n + 1)) *ᵥ tailExtension K n x) (Sum.inr 0) = 0 :=
      (hrn (tailExtension K n x)).trans (tailExtension_negative_head K n x)
    calc
      splitQ K ((a : Mat K n) *ᵥ x) =
          splitQ K ((u : Mat K (n + 1)) *ᵥ tailExtension K n x) := by
        rw [splitQ_tail_of_negative_head_zero K n _ hy, ht]
      _ = splitQ K (tailExtension K n x) := hQ _
      _ = splitQ K x := tailExtension_norm K n x
  exact ⟨⟨a, haQ⟩, ha⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDQuadraticPairTail
