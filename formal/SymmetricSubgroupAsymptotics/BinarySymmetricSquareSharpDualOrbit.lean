import SymmetricSubgroupAsymptotics.BinaryQuadraticSharpIsometryCardinality
import SymmetricSubgroupAsymptotics.BinarySymmetricSquareDualOrbit

/-! The actual dual orbit bound with the sharp 2(q+1) stabilizer.
It gives q(q-1)^2 <= 2|orbit| uniformly, and q² <= |orbit| for q>=4.
No conic or small-field orbit classification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpDualOrbit

open BinarySymmetricSquareAction BinaryQuadraticFunctionalStabilizer
open BinarySymmetricSquareDualOrbit
variable {K : Type*} [Field K]

/-- Specialization of the proved two-column GL cardinal, with all
natural subtractions justified by the field cardinal being at least two. -/
theorem generalLinear_card [Finite K] :
    Nat.card (GeneralLinear (K := K)) =
      Nat.card K * (Nat.card K - 1) ^ 2 * (Nat.card K + 1) := by
  letI : Fintype K := Fintype.ofFinite K
  let q := Nat.card K
  let r := q - 1
  have hq : 2 ≤ q := by
    have hh : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hr : r + 1 = q := Nat.sub_add_cancel (by omega)
  have hsq : 1 ≤ q ^ 2 := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) 2)
  have hpoly : r * (q + 1) + 1 = q ^ 2 := by
    rw [← hr]
    ring
  have hfac : q ^ 2 - 1 = r * (q + 1) :=
    Nat.add_right_cancel ((Nat.sub_add_cancel hsq).trans hpoly.symm)
  have hsub : q ^ 2 - q = q * r := by
    change q ^ 2 - q = q * (q - 1)
    simp only [pow_two, Nat.mul_sub_left_distrib, mul_one]
  have hGL : Nat.card (GeneralLinear (K := K)) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    dsimp only [q]
    simpa only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      Nat.card_eq_fintype_card] using (Matrix.card_GL_field (𝔽 := K) 2)
  calc
    Nat.card (GeneralLinear (K := K)) = (q ^ 2 - 1) * (q ^ 2 - q) := hGL
    _ = q * r ^ 2 * (q + 1) := by rw [hfac, hsub]; ring

variable {F : Type*} [Field F] [Algebra F K]

local instance sharpCongruenceDualAction :
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

/-- The bound holds for every finite characteristic-two field,
without a lower field-cardinality threshold. -/
theorem field_mul_square_sub_one_le_two_mul_dual_orbit [Finite K] [CharP K 2]
    (f : Module.Dual F K) (hf : f ≠ 0) (a b c : K) (hb : b ≠ 0) :
    Nat.card K * (Nat.card K - 1) ^ 2 ≤ 2 * Nat.card
      (InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedCongruence (F := F) (K := K)) (functional f a b c)) := by
  let ℓ := functional f a b c
  let S := MulAction.stabilizer (GeneralLinear (K := K)) ℓ
  let O := MulAction.orbit (GeneralLinear (K := K)) ℓ
  have hS : Nat.card S ≤ 2 * (Nat.card K + 1) := by
    change Nat.card (MulAction.stabilizer (GeneralLinear (K := K))
      (functional f a b c)) ≤ _
    rw [dual_stabilizer_eq_preservers]
    exact BinaryQuadraticSharpIsometryCardinality.card_preservers_le_two_mul_card_add_one
      f hf a b c hb
  have hcard : Nat.card (GeneralLinear (K := K)) = Nat.card O * Nat.card S := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup (GeneralLinear (K := K)) ℓ)).symm
  have hlow : (Nat.card K * (Nat.card K - 1) ^ 2) * (Nat.card K + 1) ≤
      (2 * Nat.card O) * (Nat.card K + 1) := by
    calc
      _ = Nat.card (GeneralLinear (K := K)) := generalLinear_card.symm
      _ = Nat.card O * Nat.card S := hcard
      _ ≤ Nat.card O * (2 * (Nat.card K + 1)) := Nat.mul_le_mul_left _ hS
      _ = (2 * Nat.card O) * (Nat.card K + 1) := by ring
  exact Nat.le_of_mul_le_mul_right hlow (Nat.zero_lt_succ _)

/-- In particular, the actual quadratic-functional dual orbit has
cardinality at least q² for q>=4, including the field of order four. -/
theorem field_square_le_functional_dual_orbit [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (f : Module.Dual F K) (hf : f ≠ 0)
    (a b c : K) (hb : b ≠ 0) :
    Nat.card K ^ 2 ≤ Nat.card
      (InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedCongruence (F := F) (K := K)) (functional f a b c)) := by
  have hq3 : 3 ≤ Nat.card K - 1 := by omega
  have hm := Nat.mul_le_mul_right (Nat.card K - 1) hq3
  rw [← pow_two] at hm
  have hsquare : 2 * Nat.card K ≤ (Nat.card K - 1) ^ 2 := by omega
  have hlow : 2 * Nat.card K ^ 2 ≤ 2 * Nat.card
      (InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedCongruence (F := F) (K := K)) (functional f a b c)) := by
    calc
      _ = Nat.card K * (2 * Nat.card K) := by ring
      _ ≤ Nat.card K * (Nat.card K - 1) ^ 2 := Nat.mul_le_mul_left _ hsquare
      _ ≤ _ := field_mul_square_sub_one_le_two_mul_dual_orbit f hf a b c hb
  exact Nat.le_of_mul_le_mul_left hlow (by decide : 0 < 2)

end SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpDualOrbit
