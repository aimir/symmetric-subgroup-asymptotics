import SymmetricSubgroupAsymptotics.CFSGFlagPrefixSpan
import SymmetricSubgroupAsymptotics.CFSGGTwoSingularPrefix
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace

/-! Literal span and singularity data for the first three natural G2
prefixes, inside the same split eight-dimensional quadratic space. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPrefixGeometry
open CFSGGTwoSerreMatrices CFSGGTwoSingularPrefix CFSGMatrixFlagNormalizer
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def basisVector (k : ℕ) : Index → K :=
  if hk : k < 8 then Pi.single ((flagEquiv 4).symm ⟨k, hk⟩) 1 else 0

theorem prefix_zero : positivePrefix K 0 = ⊥ :=
  CFSGFlagPrefixSpan.zero_eq_bot (flagEquiv 4)

theorem prefix_span (k : ℕ) (hk : k < 3) :
    positivePrefix K (k + 1) = positivePrefix K k ⊔ Submodule.span K {basisVector K k} := by
  simpa only [positivePrefix, basisVector, dif_pos (show k < 8 by omega)] using
    (CFSGFlagPrefixSpan.succ_eq_sup_single (K := K) (flagEquiv 4) k (by omega))

theorem prefix_le_positive (k : ℕ) (hk : k ≤ 4) :
    positivePrefix K k ≤ positiveSpace K 4 := by
  intro v hv i
  exact hv (Sum.inr i) (by change k ≤ 4 + (Fin.rev i).val; omega)

theorem prefix_singular (k : ℕ) (hk : k ≤ 3) (v : Index → K)
    (hv : v ∈ positivePrefix K k) : splitQuadraticForm K 4 v = 0 :=
  positiveSpace_singular K 4 ⟨v, prefix_le_positive K k (by omega) hv⟩

theorem basis_mem (k : ℕ) (hk : k < 3) :
    basisVector K k ∈ positivePrefix K (k + 1) := by
  simpa only [basisVector, dif_pos (show k < 8 by omega), positivePrefix] using
    (CFSGFlagPrefixSpan.single_mem_succ (K := K) (flagEquiv 4) k (by omega))

theorem basis_singular (k : ℕ) (hk : k < 3) :
    splitQuadraticForm K 4 (basisVector K k) = 0 :=
  prefix_singular K (k + 1) (by omega) _ (basis_mem K k hk)

end SymmetricSubgroupAsymptotics.CFSGGTwoPrefixGeometry
