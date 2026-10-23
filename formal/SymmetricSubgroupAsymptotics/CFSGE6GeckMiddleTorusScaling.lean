import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordTorusScaling
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! Actual coroot scalars on the two middle factors, computed from
small literal E6 lattice words. The paired height-two factor has node-3
weight one; the height-three factor has weights (1,0,1) at nodes 2,3,4. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusScaling
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckMiddleAThreeCollecting
open CFSGE6GeckSignedSimpleParameters CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateWordTorusScaling CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem word_coroot (i j : Fin 6) (w : List (Fin 6)) :
    integerPairing A (E6Index i : Roots A).val (wordRoot A hs hp E6Base E6Index w (E6Index j)).val=
      integerPairing A (Pi.single i (1 : ℤ) : Fin 6→ℤ)
        (latticeWord A w*ᵥ(Pi.single j (1 : ℤ) : Fin 6→ℤ)) := by
  have hdeg : (wordRoot A hs hp E6Base E6Index w (E6Index j)).val=
      latticeWord A w*ᵥ(Pi.single j (1 : ℤ) : Fin 6→ℤ) := by
    rw [←wordLinear_root]
    have hh := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w)
      (Pi.single j (1 : ℤ) : Fin 6→ℤ)
    exact hh.symm
  rw [hdeg]
  rfl

private theorem torus_word (K : Type) [Field K] (i : Fin 6) (t : Kˣ)
    (w : List (Fin 6)) (j : Fin 6) (a : K) :
    parameterTorus A hs hp E6Base E6Index K i t*rootWord rawData K w false j a*
      (parameterTorus A hs hp E6Base E6Index K i t)⁻¹=
      rootWord rawData K w false j
        (a*(t : K)^(integerPairing A (E6Index i : Roots A).val
          (wordRoot A hs hp E6Base E6Index w (E6Index j)).val)) :=
  torus_conjugate_positive_word A hd hs hp ho K i t w j a

theorem middleShort_torus_scale (K : Type) [Field K] (sigma : RingAut K)
    (t : Kˣ) (ht : sigma (t : K)=(t : K)) (a : K) :
    parameterTorus A hs hp E6Base E6Index K 3 t*
      (canonicalWeyl rawData K 3*rawPairedHom K sigma false 1 (Multiplicative.ofAdd a)*(canonicalWeyl rawData K 3)⁻¹)*
      (parameterTorus A hs hp E6Base E6Index K 3 t)⁻¹=
      canonicalWeyl rawData K 3*rawPairedHom K sigma false 1 (Multiplicative.ofAdd (a*(t : K)))*
        (canonicalWeyl rawData K 3)⁻¹ := by
  have h2 := torus_word K 3 t [3] 2 a
  have h4 := torus_word K 3 t [3] 4 (sigma a)
  have hw2 : integerPairing A (E6Index 3 : Roots A).val
      (wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val=1 := by rw [word_coroot]; decide
  have hw4 : integerPairing A (E6Index 3 : Roots A).val
      (wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val=1 := by rw [word_coroot]; decide
  rw [hw2,zpow_one] at h2
  rw [hw4,zpow_one] at h4
  simp only [rootWord,canonicalWord,mul_one] at h2 h4
  let H := parameterTorus A hs hp E6Base E6Index K 3 t
  let W := canonicalWeyl rawData K 3
  change H*(W*(canonicalRoot rawData K false 2 a*canonicalRoot rawData K false 4 (sigma a))*W⁻¹)*H⁻¹=
    W*(canonicalRoot rawData K false 2 (a*(t : K))*canonicalRoot rawData K false 4 (sigma (a*(t : K))))*W⁻¹
  rw [map_mul,ht]
  calc
    _=(H*(W*canonicalRoot rawData K false 2 a*W⁻¹)*H⁻¹)*
        (H*(W*canonicalRoot rawData K false 4 (sigma a)*W⁻¹)*H⁻¹) := by group
    _=(W*canonicalRoot rawData K false 2 (a*(t : K))*W⁻¹)*
        (W*canonicalRoot rawData K false 4 (sigma a*(t : K))*W⁻¹) := by
          dsimp only [H,W]
          rw [h2,h4]
    _=_ := by group

theorem middleLong_torus_outer (K : Type) [Field K] (j : Fin 2) (t : Kˣ) (a : K) :
    parameterTorus A hs hp E6Base E6Index K (![2,4] j) t*highestMiddle K a*
      (parameterTorus A hs hp E6Base E6Index K (![2,4] j) t)⁻¹=
      highestMiddle K (a*(t : K)) := by
  have hh := torus_word K (![2,4] j) t [2,4] 3 a
  have hw : integerPairing A (E6Index (![2,4] j) : Roots A).val
      (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val=1 := by
    rw [word_coroot]
    fin_cases j <;> decide
  rw [hw,zpow_one] at hh
  simpa only [rootWord,canonicalWord,mul_one,highestMiddle] using hh

theorem middleLong_torus_three (K : Type) [Field K] (t : Kˣ) (a : K) :
    parameterTorus A hs hp E6Base E6Index K 3 t*highestMiddle K a*
      (parameterTorus A hs hp E6Base E6Index K 3 t)⁻¹=highestMiddle K a := by
  have hh := torus_word K 3 t [2,4] 3 a
  have hw : integerPairing A (E6Index 3 : Roots A).val
      (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val=0 := by rw [word_coroot]; decide
  rw [hw,zpow_zero,mul_one] at hh
  simpa only [rootWord,canonicalWord,mul_one,highestMiddle] using hh

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusScaling
