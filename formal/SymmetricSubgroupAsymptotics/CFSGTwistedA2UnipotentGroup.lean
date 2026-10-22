import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentNatural
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentParameters
import Mathlib.GroupTheory.PGroup

/-! The actual natural elementary upper-unipotent subgroup, with exact
parameter equivalence and q^3 order. These are subgroup/cardinality
statements on literal matrices, without a whole-unitary-group premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGTwistedA2UnipotentParameters
variable (K : Type) [Field K] (σ : K ≃+* K)

theorem upperNatural_zero : upperNatural K σ 0 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact (upperNatural_val K σ 0 0).trans (upperArray_zero σ)

theorem upperNatural_mul (a b c d : K) :
    upperNatural K σ a b * upperNatural K σ c d =
      upperNatural K σ (a + c) (b + d + a * σ c) := by
  apply Subtype.ext
  apply Units.ext
  change ((upperNatural K σ a b).val : Mat K 2) *
    ((upperNatural K σ c d).val : Mat K 2) = _
  rw [upperNatural_val, upperNatural_val, upperNatural_val, upperArray_mul]

theorem upperNatural_inv (a b : K) :
    (upperNatural K σ a b)⁻¹ = upperNatural K σ (-a) (-b + a * σ a) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Units.ext
  change ((upperNatural K σ a b).val : Mat K 2) *
    ((upperNatural K σ (-a) (-b + a * σ a)).val : Mat K 2) = 1
  rw [upperNatural_val, upperNatural_val]
  exact upperArray_inverse_right σ a b

theorem upperNatural_injective : Function.Injective (fun ab : K × K => upperNatural K σ ab.1 ab.2) := by
  intro ab cd h
  have he := congrArg (fun g : NaturalElementary K 2 => (g.val : Mat K 2)) h
  change ((upperNatural K σ ab.1 ab.2).val : Mat K 2) =
    ((upperNatural K σ cd.1 cd.2).val : Mat K 2) at he
  rw [upperNatural_val, upperNatural_val] at he
  apply Prod.ext
  · have hh := congrArg (fun M : Mat K 2 => M 0 1) he
    simpa [upperArray] using hh
  · have hh := congrArg (fun M : Mat K 2 => M 0 2) he
    simpa [upperArray] using hh

def naturalUnipotent (q : CFSG.PrimePower) : Subgroup (NaturalElementary (q.Extension 2) 2) where
  carrier := {g | ∃ a b, NormCondition (definingFieldAutomorphism q 2) a b ∧
    g = upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) a b}
  one_mem' := ⟨0, 0, normCondition_zero _, (upperNatural_zero _ _).symm⟩
  mul_mem' := by
    rintro g h ⟨a, b, hab, rfl⟩ ⟨c, d, hcd, rfl⟩
    refine ⟨a + c, b + d + a * definingFieldAutomorphism q 2 c,
      normCondition_mul _ (fun x => extension_two_pow_twice q x) a b c d hab hcd, ?_⟩
    exact upperNatural_mul _ _ a b c d
  inv_mem' := by
    rintro g ⟨a, b, hab, rfl⟩
    refine ⟨-a, -b + a * definingFieldAutomorphism q 2 a,
      normCondition_inverse _ (fun x => extension_two_pow_twice q x) a b hab, ?_⟩
    exact upperNatural_inv _ _ a b

def naturalParameterEquiv (q : CFSG.PrimePower) : Parameters q ≃ naturalUnipotent q :=
  Equiv.ofBijective (fun ab =>
    ⟨upperNatural (q.Extension 2) (definingFieldAutomorphism q 2) ab.val.1 ab.val.2,
      ⟨ab.val.1, ab.val.2, ab.property, rfl⟩⟩) (by
    constructor
    · intro ab cd h
      apply Subtype.ext
      exact upperNatural_injective _ _ (congrArg Subtype.val h)
    · rintro ⟨g, a, b, hab, hg⟩
      exact ⟨⟨(a, b), hab⟩, Subtype.ext hg.symm⟩)

theorem naturalUnipotent_card (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (naturalUnipotent q) = q.order ^ 3 :=
  (Nat.card_congr (naturalParameterEquiv q).symm).trans (parameters_card q hq)

theorem naturalUnipotent_isPGroup (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    IsPGroup q.prime (naturalUnipotent q) := by
  apply IsPGroup.of_card (n := q.exponent * 3)
  rw [naturalUnipotent_card q hq]
  exact (pow_mul q.prime q.exponent 3).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
