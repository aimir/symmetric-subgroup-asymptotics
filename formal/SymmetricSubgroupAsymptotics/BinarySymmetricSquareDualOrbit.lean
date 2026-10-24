import SymmetricSubgroupAsymptotics.BinaryQuadraticFunctionalStabilizer
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Lean.Elab.Tactic.Omega

/-! Actual binary symmetric-square dual orbits have size at least q²
when their quadratic cross coefficient is nonzero in characteristic two
and q is at least eight. The bound uses the literal GL2 cardinal and the
actual functional stabilizer, without orbit classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySymmetricSquareDualOrbit

open BinarySymmetricSquareAction
open BinaryQuadraticFunctionalStabilizer
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The same actual congruence action, restricted to the base field. -/
def restrictedCongruence :
    GeneralLinear (K := K) →* Space (K := K) ≃ₗ[F] Space (K := K) where
  toFun A := (congruence A).restrictScalars F
  map_one' := by
    apply LinearEquiv.ext
    intro S
    change congruenceLinearMap 1 S = S
    exact congruenceLinearMap_one S
  map_mul' A B := by
    apply LinearEquiv.ext
    intro S
    change congruenceLinearMap (A * B) S =
      congruenceLinearMap A (congruenceLinearMap B S)
    exact congruenceLinearMap_mul A B S

local instance congruenceDualAction :
    MulAction (GeneralLinear (K := K)) (Module.Dual F (Space (K := K))) :=
  InvariantAnnihilatorOrbitIndex.dualAction (restrictedCongruence (F := F) (K := K))

private theorem dual_stabilizer_eq_preservers (f : Module.Dual F K) (a b c : K) :
    MulAction.stabilizer (GeneralLinear (K := K)) (functional f a b c) =
      preservers f a b c := by
  ext A
  constructor
  · intro hA S
    change (functional f a b c).comp
      ((restrictedCongruence (F := F) (K := K)) A⁻¹).toLinearMap = functional f a b c at hA
    have he := congrArg
      (fun ℓ : Module.Dual F (Space (K := K)) => ℓ (congruenceLinearMap A S)) hA
    change functional f a b c (congruenceLinearMap A⁻¹ (congruenceLinearMap A S)) =
      functional f a b c (congruenceLinearMap A S) at he
    rw [← congruenceLinearMap_mul, inv_mul_cancel, congruenceLinearMap_one] at he
    exact he.symm
  · intro hA
    change (functional f a b c).comp
      ((restrictedCongruence (F := F) (K := K)) A⁻¹).toLinearMap = functional f a b c
    apply LinearMap.ext
    intro S
    have hi : A⁻¹ ∈ preservers f a b c := (preservers f a b c).inv_mem hA
    exact hi S

/-- The actual two-column GL cardinal dominates the needed orbit numerator. -/
theorem four_mul_cube_le_generalLinear_card [Finite K]
    (hq : 8 ≤ Nat.card K) :
    (4 * Nat.card K) * Nat.card K ^ 2 ≤ Nat.card (GeneralLinear (K := K)) := by
  letI : Fintype K := Fintype.ofFinite K
  let q := Nat.card K
  have hq' : 8 ≤ q := hq
  have hq1 : 1 ≤ q := by omega
  have hq7 : 7 ≤ q - 1 := by omega
  have hsub : q ^ 2 - q = q * (q - 1) := by
    simp only [pow_two, Nat.mul_sub_left_distrib, mul_one]
  have hlow : q * (q - 1) ≤ q ^ 2 - 1 := by
    rw [← hsub]
    exact Nat.sub_le_sub_left hq1 (q ^ 2)
  have hsquare : 4 * q ≤ (q - 1) ^ 2 := by
    have hm := Nat.mul_le_mul_right (q - 1) hq7
    rw [← pow_two] at hm
    omega
  have hGL : Nat.card (GeneralLinear (K := K)) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    dsimp only [q]
    simpa only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      Nat.card_eq_fintype_card] using (Matrix.card_GL_field (𝔽 := K) 2)
  calc
    (4 * Nat.card K) * Nat.card K ^ 2 = q ^ 2 * (4 * q) := by ring
    _ ≤ q ^ 2 * (q - 1) ^ 2 := Nat.mul_le_mul_left _ hsquare
    _ = (q * (q - 1)) * (q * (q - 1)) := by ring
    _ ≤ (q ^ 2 - 1) * (q ^ 2 - q) := by
      rw [hsub]
      exact Nat.mul_le_mul_right _ hlow
    _ = Nat.card (GeneralLinear (K := K)) := hGL.symm

/-- This is the literal dual orbit of the actual restricted congruence
representation, not an assumed orbit or minimum-degree certificate. -/
theorem field_square_le_functional_dual_orbit [Finite K] [CharP K 2]
    (hq : 8 ≤ Nat.card K) (f : Module.Dual F K) (hf : f ≠ 0)
    (a b c : K) (hb : b ≠ 0) :
    Nat.card K ^ 2 ≤ Nat.card
      (InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedCongruence (F := F) (K := K)) (functional f a b c)) := by
  let ℓ := functional f a b c
  let S := MulAction.stabilizer (GeneralLinear (K := K)) ℓ
  let O := MulAction.orbit (GeneralLinear (K := K)) ℓ
  have hS : Nat.card S ≤ 4 * Nat.card K := by
    change Nat.card (MulAction.stabilizer (GeneralLinear (K := K))
      (functional f a b c)) ≤ _
    rw [dual_stabilizer_eq_preservers]
    exact card_preservers_le_four_mul_card f hf a b c hb
  have hcard : Nat.card (GeneralLinear (K := K)) = Nat.card O * Nat.card S := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup (GeneralLinear (K := K)) ℓ)).symm
  have hlow : (4 * Nat.card K) * Nat.card K ^ 2 ≤ (4 * Nat.card K) * Nat.card O := by
    calc
      _ ≤ Nat.card (GeneralLinear (K := K)) := four_mul_cube_le_generalLinear_card hq
      _ = Nat.card O * Nat.card S := hcard
      _ ≤ Nat.card O * (4 * Nat.card K) := Nat.mul_le_mul_left _ hS
      _ = (4 * Nat.card K) * Nat.card O := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hlow (by omega)

end SymmetricSubgroupAsymptotics.BinarySymmetricSquareDualOrbit
