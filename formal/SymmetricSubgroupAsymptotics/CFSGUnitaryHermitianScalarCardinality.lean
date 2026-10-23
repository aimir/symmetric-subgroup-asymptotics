import SymmetricSubgroupAsymptotics.CFSGHermitianSpecialIsometryCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits

/-! Both scalar factors in the actual quadratic-field Hermitian count
are bounded on the pinned field types. No unitary order formula or
similitude splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianScalarCardinality
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGHermitianSimilitudeGroup

def fixedUnitEmbedding (q : CFSG.PrimePower) :
    fixedUnits (definingFieldAutomorphism q 2) → (fixedField q)ˣ := fun z =>
  Units.mk0 (⟨(z.val : q.Extension 2), z.property⟩ : fixedField q) (by
    intro h
    exact Units.ne_zero z.val (congrArg (fun x : fixedField q => (x : q.Extension 2)) h))

theorem fixedUnitEmbedding_injective (q : CFSG.PrimePower) :
    Function.Injective (fixedUnitEmbedding q) := by
  intro z w he
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun u : (fixedField q)ˣ => ((u : fixedField q) : q.Extension 2)) he

theorem fixedUnits_card_le (q : CFSG.PrimePower) :
    Nat.card (fixedUnits (definingFieldAutomorphism q 2)) ≤ q.order - 1 := by
  have hh := Nat.card_le_card_of_injective (fixedUnitEmbedding q) (fixedUnitEmbedding_injective q)
  simpa only [Nat.card_units, fixedField_card] using hh

theorem normOneUnits_eq (q : CFSG.PrimePower) :
    normOneUnits (definingFieldAutomorphism q 2) = CFSGTwistedDNormOneUnits.normOneUnits q := by
  ext z
  constructor
  · intro hz
    apply Units.ext
    have hh := congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hz
    change definingFieldAutomorphism q 2 (z : q.Extension 2) * (z : q.Extension 2) = 1 at hh
    change (z : q.Extension 2) ^ (q.order + 1) = 1
    simpa only [pow_succ, definingFieldAutomorphism_apply] using hh
  · intro hz
    apply Units.ext
    have hh := congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hz
    change (z : q.Extension 2) ^ (q.order + 1) = 1 at hh
    change definingFieldAutomorphism q 2 (z : q.Extension 2) * (z : q.Extension 2) = 1
    simpa only [pow_succ, definingFieldAutomorphism_apply] using hh

theorem normOneUnits_card_le (q : CFSG.PrimePower) :
    Nat.card (normOneUnits (definingFieldAutomorphism q 2)) ≤ q.order + 1 := by
  rw [normOneUnits_eq]
  exact CFSGTwistedDNormOneUnits.normOneUnits_card_le q

theorem similitudes_card_le_special_mul_field_units
    (q : CFSG.PrimePower) {I : Type*} [Fintype I] [DecidableEq I]
    (eps : q.Extension 2) (H : (Matrix I I (q.Extension 2))ˣ)
    (hH : (H : Matrix I I (q.Extension 2)).map (definingFieldAutomorphism q 2) =
      eps • (H : Matrix I I (q.Extension 2)).transpose) (i₀ : I) :
    Nat.card (similitudes (definingFieldAutomorphism q 2) H) ≤
      Nat.card (specialIsometries (definingFieldAutomorphism q 2) H) * (q.order ^ 2 - 1) := by
  have hh := similitudes_card_le_special (definingFieldAutomorphism q 2)
    (fun x => CFSGTwistedANaturalMatrices.extension_two_pow_twice q x) eps H hH i₀
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hn : (q.order + 1) * (q.order - 1) = q.order ^ 2 - 1 := by
    have h1 := Nat.sub_add_cancel (show 1 ≤ q.order by omega)
    have h2 := Nat.sub_add_cancel (show 1 ≤ q.order ^ 2 by nlinarith)
    nlinarith
  calc
    _ ≤ _ := hh
    _ ≤ Nat.card (specialIsometries (definingFieldAutomorphism q 2) H) *
        (q.order + 1) * (q.order - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (normOneUnits_card_le q)) (fixedUnits_card_le q)
    _ = _ := by rw [mul_assoc, hn]

end SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianScalarCardinality
