import SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleProbes

/-! The actual original coordinate halves pair nondegenerately, with
the literal Gram coefficient two retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPairedNondegeneracy
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBZeroMiddleProbes
variable (K : Type) [Field K] [Finite K]

theorem negative_orthogonal_positive_eq_zero (h2 : (2 : K)≠0) (n : ℕ)
    (v : Index n→K) (hv : v∈negativeSubspace K n)
    (horth : ∀w∈positiveSubspace K n,(gram K n).toBilin' v w=0) : v=0 := by
  obtain ⟨a,rfl⟩ := hv
  have ha : a=0 := by
    funext i
    have he := horth (Pi.single (pos n i) 1) (positive_basis_mem K n i)
    rw [pairing_positive] at he
    exact (mul_eq_zero.mp he).resolve_left h2
  rw [ha,map_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPairedNondegeneracy
