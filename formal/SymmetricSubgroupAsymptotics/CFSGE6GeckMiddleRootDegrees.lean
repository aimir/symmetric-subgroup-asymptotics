import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleAThreeCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist

/-! Four selected integral root degrees for the middle A3 cell.
The calculations involve only six integer coordinates. Their actual
Geck words therefore lie in the positive subgroup over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees
open CFSGE6GeckMiddleAThreeCollecting CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateLatticeWord
open CFSGSignedCartanReflections
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylRootMembership CFSGTwistedE6GeckPositiveTwist
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem wordRoot_val_eq_latticeWord (w : List (Fin 6)) (j : Fin 6) :
    (wordRoot A hs hp E6Base E6Index w (E6Index j)).val =
      latticeWord A w *ᵥ (Pi.single j 1 : Fin 6 → ℤ) := by
  have hm := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w)
    (Pi.single j (1 : ℤ))
  have hr := wordLinear_root A hs hp E6Base E6Index w (E6Index j)
  change wordLinear A hs hp E6Base E6Index w (Pi.single j 1) = _ at hr
  exact hr.symm.trans hm.symm

theorem highest_root_degree :
    (wordRoot A hs hp E6Base E6Index [2, 4] (E6Index 3)).val = ![0, 0, 1, 1, 1, 0] := by
  rw [wordRoot_val_eq_latticeWord]
  decide

theorem reflected_highest_root_degree :
    (wordRoot A hs hp E6Base E6Index [3, 2, 4] (E6Index 3)).val = ![0, 0, 1, 1, 1, 0] := by
  rw [wordRoot_val_eq_latticeWord]
  decide

theorem paired_first_degree :
    (wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val = ![0, 0, 1, 1, 0, 0] := by
  rw [wordRoot_val_eq_latticeWord]
  decide

theorem paired_second_degree :
    (wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val = ![0, 0, 0, 1, 1, 0] := by
  rw [wordRoot_val_eq_latticeWord]
  decide

theorem highestMiddle_mem_positive (K : Type) [Field K] (r : K) :
    highestMiddle K r ∈ Positive K := by
  have hm := positive_word_mem A hd hs hp ho K [2, 4] 3 r (by
    change ∀ l, 0 ≤ (wordRoot A hs hp E6Base E6Index [2, 4] (E6Index 3)).val l
    rw [highest_root_degree]
    intro i
    fin_cases i <;> decide)
  simpa only [rootWord, wordUnit, mul_one, highestMiddle] using hm

theorem reflected_highestMiddle_mem_positive (K : Type) [Field K] (r : K) :
    CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 3 * highestMiddle K r *
      (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 3)⁻¹ ∈ Positive K := by
  have hm := positive_word_mem A hd hs hp ho K [3, 2, 4] 3 r (by
    change ∀ l, 0 ≤ (wordRoot A hs hp E6Base E6Index [3, 2, 4] (E6Index 3)).val l
    rw [reflected_highest_root_degree]
    intro i
    fin_cases i <;> decide)
  have he : rootWord A hd hs hp ho K [3, 2, 4] 3 r =
      CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 3 * highestMiddle K r *
        (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 3)⁻¹ := by
    change (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 3 *
      (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 2 *
        (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 4 * 1))) *
      CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 3 r *
      (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 3 *
        (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 2 *
          (CFSGSerreQuadraticMatrix.canonicalWeyl rawData K 4 * 1)))⁻¹ = _
    dsimp only [highestMiddle]
    group
  exact he ▸ hm

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees
