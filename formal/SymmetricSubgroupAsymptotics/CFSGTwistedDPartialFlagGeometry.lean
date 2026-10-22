import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPrefix
import SymmetricSubgroupAsymptotics.CFSGFlagPrefixSpan
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements

/-! Literal chain/folded-fork tests and their singular positive prefixes
in natural D of every rank at least four. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPartialFlagGeometry
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDSingularPrefix
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGMatrixFlagNormalizer
variable (K : Type) [Field K] (s : ℕ)

def testRoot : Fin (s + 2) ⊕ Unit → elementaryRootGroup K (s + 4)
  | Sum.inl i => rootElement K (s + 4) false (chainNode (s + 2) i) 1
  | Sum.inr _ => rootElement K (s + 4) false (pen (s + 2)) 1 *
      rootElement K (s + 4) false (last (s + 2)) 1

def basisVector (k : ℕ) : Index (s + 4) → K :=
  if hk : k < (s + 4) + (s + 4) then
    Pi.single ((flagEquiv (s + 4)).symm ⟨k, hk⟩) 1 else 0

theorem prefix_zero : positivePrefix K (s + 2) 0 = ⊥ :=
  CFSGFlagPrefixSpan.zero_eq_bot (flagEquiv (s + 4))

theorem prefix_span (k : ℕ) (hk : k < s + 3) :
    positivePrefix K (s + 2) (k + 1) = positivePrefix K (s + 2) k ⊔
      Submodule.span K {basisVector K s k} := by
  simpa only [positivePrefix, basisVector, dif_pos (show k < (s + 4) + (s + 4) by omega)] using
    (CFSGFlagPrefixSpan.succ_eq_sup_single (K := K) (flagEquiv (s + 4)) k (by omega))

theorem prefix_le_positive (k : ℕ) (hk : k ≤ s + 4) :
    positivePrefix K (s + 2) k ≤ positiveSpace K (s + 4) := by
  intro v hv i
  exact hv (Sum.inr i) (by change k ≤ s + 4 + (Fin.rev i).val; omega)

theorem prefix_singular (k : ℕ) (hk : k ≤ s + 3) (v : Index (s + 4) → K)
    (hv : v ∈ positivePrefix K (s + 2) k) : splitQuadraticForm K (s + 4) v = 0 :=
  positiveSpace_singular K (s + 4) ⟨v, prefix_le_positive K s k (by omega) hv⟩

theorem basis_mem (k : ℕ) (hk : k < s + 3) :
    basisVector K s k ∈ positivePrefix K (s + 2) (k + 1) := by
  simpa only [basisVector, dif_pos (show k < (s + 4) + (s + 4) by omega), positivePrefix] using
    (CFSGFlagPrefixSpan.single_mem_succ (K := K) (flagEquiv (s + 4)) k (by omega))

theorem basis_singular (k : ℕ) (hk : k < s + 3) :
    splitQuadraticForm K (s + 4) (basisVector K s k) = 0 :=
  prefix_singular K s (k + 1) (by omega) _ (basis_mem K s k hk)

end SymmetricSubgroupAsymptotics.CFSGTwistedDPartialFlagGeometry
