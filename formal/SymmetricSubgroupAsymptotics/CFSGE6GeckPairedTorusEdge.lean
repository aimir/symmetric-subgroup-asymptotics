import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation
import Mathlib.Tactic.Group

/-! Along the paired-paired edge the literal second paired torus acts
on the first paired root by an arbitrary inverse extension-field scalar.
This is an actual matrix identity in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckPairedTorusEdge
open CFSGE6GeckPairedParameterizedWeyl CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6PairedFixedRoots
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckTorusConjugation
open CFSGIntegerMatrixPairing CFSGSerreQuadraticMatrix

private theorem edge_pairing (i j : Fin 2) :
    integerPairing CartanMatrix.E₆
      (E6Index (![2,4] i) : CFSGNormTwoRootPairing.Roots CartanMatrix.E₆).val
      (E6Index (![0,5] j) : CFSGNormTwoRootPairing.Roots CartanMatrix.E₆).val =
        if i = j then -1 else 0 := by
  change integerPairing CartanMatrix.E₆ (Pi.single (![2,4] i) (1 : ℤ) : Fin 6 → ℤ)
    (Pi.single (![0,5] j) (1 : ℤ) : Fin 6 → ℤ) = _
  fin_cases i <;> fin_cases j <;> decide

private theorem edge_torus_root (K : Type) [Field K] (i j : Fin 2) (t : Kˣ) (a : K) :
    parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      K (![2,4] i) t * canonicalRoot rawData K false (![0,5] j) a *
    (parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      K (![2,4] i) t)⁻¹ =
        canonicalRoot rawData K false (![0,5] j) (if i = j then a * (t : K)⁻¹ else a) := by
  have hh := torus_conjugate_positive CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K (![2,4] i) (![0,5] j) t a
  rw [edge_pairing] at hh
  by_cases hij : i = j
  · simpa only [if_pos hij, zpow_neg_one] using hh
  · simpa only [if_neg hij, zpow_zero, mul_one] using hh

theorem pairedTorus_second_on_first (K : Type) [Field K] (sigma : RingAut K)
    (t : Kˣ) (a : K) :
    pairedParameterTorus K sigma 1 t * rawPairedHom K sigma false 0 (Multiplicative.ofAdd a) *
      (pairedParameterTorus K sigma 1 t)⁻¹ =
        rawPairedHom K sigma false 0 (Multiplicative.ofAdd (a * (t : K)⁻¹)) := by
  rw [pairedParameterTorus_eq]
  let T (i : Fin 2) (c : Kˣ) := parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K (![2,4] i) c
  let st : Kˣ := Units.map sigma.toMonoidHom t
  change (T 0 t * T 1 st) *
    (canonicalRoot rawData K false 0 a * canonicalRoot rawData K false 5 (sigma a)) *
      (T 0 t * T 1 st)⁻¹ = _
  calc
    _ = (T 0 t * (T 1 st * canonicalRoot rawData K false (![0,5] 0) a * (T 1 st)⁻¹) * (T 0 t)⁻¹) *
      (T 0 t * (T 1 st * canonicalRoot rawData K false (![0,5] 1) (sigma a) * (T 1 st)⁻¹) * (T 0 t)⁻¹) := by
        change (T 0 t * T 1 st) *
          (canonicalRoot rawData K false 0 a * canonicalRoot rawData K false 5 (sigma a)) *
          (T 0 t * T 1 st)⁻¹ =
          (T 0 t * (T 1 st * canonicalRoot rawData K false 0 a * (T 1 st)⁻¹) * (T 0 t)⁻¹) *
          (T 0 t * (T 1 st * canonicalRoot rawData K false 5 (sigma a) * (T 1 st)⁻¹) * (T 0 t)⁻¹)
        group
    _ = _ := by
      dsimp only [T]
      rw [edge_torus_root, edge_torus_root]
      simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, if_true]
      rw [edge_torus_root, edge_torus_root]
      simp only [show (0 : Fin 2) ≠ 1 by decide, if_false, if_true]
      change canonicalRoot rawData K false 0 (a * (t : K)⁻¹) *
        canonicalRoot rawData K false 5 (sigma a * (st : K)⁻¹) =
          canonicalRoot rawData K false 0 (a * (t : K)⁻¹) *
            canonicalRoot rawData K false 5 (sigma (a * (t : K)⁻¹))
      simp only [st, Units.coe_map, map_mul, map_inv₀]
      rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckPairedTorusEdge
