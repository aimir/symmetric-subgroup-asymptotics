import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexLowerShearParity

/-! The genuine even-component subgroup is pulled back to the literal
matrix unit group. Its membership is actual Q preservation plus the
proved positive-space intersection parity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentMatrices
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexSingularComponents CFSGOrthogonalDIndexLowerShearParity
open CFSGMatrixShearUnits
variable (K : Type) [Field K]

def evenLinearIsometries (r : ℕ) : Subgroup ((Index r → K) ≃ₗ[K] (Index r → K)) :=
  (componentStabilizer (splitQuadraticForm K r) (splitQuadraticForm_nondegenerate K r)
    r (naturalSpace_finrank K r) (positiveSpace K r) (positiveSpace_self_orthogonal K r)
    (positiveSpace_singular K r)).map (isometryGroup (splitQuadraticForm K r)).subtype

def componentMatrices (r : ℕ) : Subgroup (Mat K r)ˣ :=
  (evenLinearIsometries K r).comap (ambientLinearEquiv K r).toMonoidHom

theorem mem_componentMatrices_iff (r : ℕ) (g : (Mat K r)ˣ) :
    g ∈ componentMatrices K r ↔
      (∀ x, splitQuadraticForm K r (ambientLinearEquiv K r g x) = splitQuadraticForm K r x) ∧
      Even (distance r (positiveSpace K r)
        ((positiveSpace K r).map (ambientLinearEquiv K r g).toLinearMap)) := by
  constructor
  · intro hg
    change ambientLinearEquiv K r g ∈ evenLinearIsometries K r at hg
    obtain ⟨f, hf, he⟩ := hg
    change f.val = ambientLinearEquiv K r g at he
    refine ⟨?_, ?_⟩
    · rw [← he]
      exact f.property
    · change Even (distance r (positiveSpace K r)
        ((positiveSpace K r).map (ambientLinearEquiv K r g).toLinearMap))
      rw [← he]
      exact hf
  · rintro ⟨hQ, hEven⟩
    let f : isometryGroup (splitQuadraticForm K r) := ⟨ambientLinearEquiv K r g, hQ⟩
    change ambientLinearEquiv K r g ∈ evenLinearIsometries K r
    exact ⟨f, hEven, rfl⟩

theorem mem_componentMatrices_of_positive_fixed (r : ℕ) (g : (Mat K r)ˣ)
    (hQ : ∀ x, splitQuadraticForm K r (ambientLinearEquiv K r g x) = splitQuadraticForm K r x)
    (hP : (positiveSpace K r).map (ambientLinearEquiv K r g).toLinearMap = positiveSpace K r) :
    g ∈ componentMatrices K r := by
  apply (mem_componentMatrices_iff K r g).mpr
  refine ⟨hQ, ?_⟩
  change Even (r - Module.finrank K ↥(positiveSpace K r ⊓
    (positiveSpace K r).map (ambientLinearEquiv K r g).toLinearMap))
  rw [hP, inf_idem, positiveSpace_finrank, Nat.sub_self]
  exact ⟨0, rfl⟩

theorem lower_mem_componentMatrices (r : ℕ) (S : Matrix (Fin r) (Fin r) K)
    (hQ : ∀ x, splitQuadraticForm K r (ambientLinearEquiv K r (lower S) x) = splitQuadraticForm K r x) :
    lower S ∈ componentMatrices K r :=
  (mem_componentMatrices_iff K r (lower S)).mpr ⟨hQ, lower_even_distance K r S hQ⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentMatrices
