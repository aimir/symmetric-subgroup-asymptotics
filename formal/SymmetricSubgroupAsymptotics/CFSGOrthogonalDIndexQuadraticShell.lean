import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic

/-! A nonzero original singular axis pairs surjectively with EVERY
quadratic shell of the literal split space of rank>=2. This constructive
fact is valid over F2: an actual original root word normalizes the axis,
and e1+c*f1+d*f0 realizes arbitrary quadratic/polar values (c,d). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShell
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexAllRankQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexVectorCoordinates CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

theorem elementary_preserves_polar_all_ranks (r : ℕ) (hr : 2 ≤ r)
    (g : elementaryRootGroup K r) (x y : Index r → K) :
    polar K ((g.val : Mat K r) *ᵥ x) ((g.val : Mat K r) *ᵥ y) = polar K x y := by
  have h := elementary_preserves_splitQ_all_ranks K r hr g (x + y)
  rw [Matrix.mulVec_add, splitQ_add, splitQ_add,
    elementary_preserves_splitQ_all_ranks K r hr g x,
    elementary_preserves_splitQ_all_ranks K r hr g y] at h
  exact add_left_cancel h

def shellVector (s : ℕ) (c d : K) : Index (s + 2) → K :=
  Sum.elim (Pi.single (⟨1, by omega⟩ : Fin (s + 2)) 1)
    (Pi.single (⟨1, by omega⟩ : Fin (s + 2)) c + Pi.single 0 d)

theorem shellVector_quadratic (s : ℕ) (c d : K) : splitQ K (shellVector K s c d) = c := by
  change (Pi.single (⟨1, by omega⟩ : Fin (s + 2)) (1 : K)) ⬝ᵥ
    ((Pi.single (⟨1, by omega⟩ : Fin (s + 2)) c + Pi.single (0 : Fin (s + 2)) d) : Fin (s + 2) → K) = c
  rw [single_dotProduct, one_mul]
  simp [Pi.single_apply, Fin.ext_iff]

theorem shellVector_polar (s : ℕ) (c d : K) :
    polar K (Pi.single (Sum.inl 0) 1) (shellVector K s c d) = d := by
  rw [pairing_first_positive K (s + 1)]
  simp [shellVector, Pi.single_apply, Fin.ext_iff]

theorem exists_shell_polar_values (s : ℕ) (v : Index (s + 2) → K)
    (hv : v ≠ 0) (hs : splitQ K v = 0) (c d : K) :
    ∃ z : Index (s + 2) → K, splitQ K z = c ∧ polar K v z = d := by
  obtain ⟨g, hg⟩ := exists_normalize_singular K s v hv hs
  let t := shellVector K s c d
  let z := (↑(g.val⁻¹) : Mat K (s + 2)) *ᵥ t
  have hgz : (g.val : Mat K (s + 2)) *ᵥ z = t := by
    change (g.val : Mat K (s + 2)) *ᵥ ((↑(g.val⁻¹) : Mat K (s + 2)) *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨z, ?_, ?_⟩
  · exact (elementary_preserves_splitQ_all_ranks K (s + 2) (by omega) g⁻¹ t).trans
      (shellVector_quadratic K s c d)
  · have h := elementary_preserves_polar_all_ranks K (s + 2) (by omega) g v z
    rw [hg, hgz] at h
    exact h.symm.trans (shellVector_polar K s c d)

theorem exists_quadratic_polar_values (s : ℕ) (v : Index (s + 2) → K)
    (hv : v ≠ 0) (hs : splitQuadraticForm K (s + 2) v = 0) (c d : K) :
    ∃ z : Index (s + 2) → K,
      splitQuadraticForm K (s + 2) z = c ∧ (splitQuadraticForm K (s + 2)).polarBilin v z = d := by
  obtain ⟨z, hzQ, hzB⟩ := exists_shell_polar_values K s v hv
    ((splitQuadraticForm_apply K (s + 2) v).symm.trans hs) c d
  exact ⟨z, (splitQuadraticForm_apply K (s + 2) z).trans hzQ,
    (splitQuadraticForm_polar K (s + 2) v z).trans hzB⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShell
