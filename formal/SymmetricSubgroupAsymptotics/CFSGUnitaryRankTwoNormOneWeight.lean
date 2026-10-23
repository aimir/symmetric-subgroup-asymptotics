import SymmetricSubgroupAsymptotics.CFSGInvolutiveScalarWeights
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! An actual norm-one unit with nontrivial first-layer weight exists
for every admissible rank-two field. It kills a torus-equivariant
central shear without invoking a unitary geometry classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGInvolutiveScalarWeights
open CFSGTwistedDNormOneUnits

theorem quadratic_normOneUnits_card (q : CFSG.PrimePower) :
    Nat.card (normOneUnits q) = q.order + 1 := by
  change Nat.card (powMonoidHom (q.order + 1) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker = _
  rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units, extension_two_card]
  apply Nat.gcd_eq_right_iff_dvd.mpr
  refine ⟨q.order - 1, ?_⟩
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have h1 := Nat.sub_add_cancel (show 1 ≤ q.order by omega)
  have h2 := Nat.sub_add_cancel (show 1 ≤ q.order ^ 2 by nlinarith)
  nlinarith

theorem exists_norm_one_nontrivial_first_weight (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ∃ z : (q.Extension 2)ˣ,
      (z : q.Extension 2) * definingFieldAutomorphism q 2 z = 1 ∧
      CFSGTwistedA2DiagonalTorus.firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z ≠ 1 := by
  let H := weightHom (definingFieldAutomorphism q 2)
  have hnot : ¬ normOneUnits q ≤ H.ker := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    have hk := kernel_card_le_gcd (definingFieldAutomorphism q 2)
      (fun x => extension_two_pow_twice q x)
    have hg : (Nat.card (q.Extension 2) - 1).gcd 3 ≤ 3 := Nat.gcd_le_right _ (by decide)
    rw [quadratic_normOneUnits_card] at hc
    change Nat.card H.ker ≤ _ at hk
    omega
  change ¬ ∀ z, z ∈ normOneUnits q → z ∈ H.ker at hnot
  push Not at hnot
  obtain ⟨z, hz, hw⟩ := hnot
  refine ⟨z, ?_, ?_⟩
  · rw [frobenius_eq_inv q ⟨z, hz⟩, mul_inv_cancel₀ (Units.ne_zero z)]
  · intro he
    apply hw
    change H z = 1
    apply Units.ext
    exact (weightHom_val (definingFieldAutomorphism q 2) z).trans he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
