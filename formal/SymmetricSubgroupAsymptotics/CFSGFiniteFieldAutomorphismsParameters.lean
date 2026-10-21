import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds
import SymmetricSubgroupAsymptotics.External.CFSG.Parameters

/-! Exact field-automorphism facts on the pinned CFSG field types.
These are facts about the original field automorphisms only; a future
simple-group outer bound must separately prove its actual structural
map to field, graph, and diagonal factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms

/-- The original extension exponent is exactly the size of the actual
field-automorphism group in the pinned model. -/
theorem primePower_card_ringAut (q : CFSG.PrimePower) :
    Nat.card (q.Field ≃+* q.Field)=q.exponent :=
  card_galoisField_ringAut q.prime q.exponent (Nat.ne_of_gt q.exponent_pos)

/-- Every automorphism of the original pinned field is an original
Frobenius power, with exponent strictly below the parameter exponent. -/
theorem primePower_exists_frobenius_pow (q : CFSG.PrimePower) (σ : q.Field ≃+* q.Field) :
    ∃ k : Fin q.exponent,primeFrobenius q.Field q.prime^k.val=σ := by
  obtain ⟨k,hk⟩ := exists_primeFrobenius_pow q.Field q.prime σ
  have he : Module.finrank (ZMod q.prime) q.Field=q.exponent :=
    GaloisField.finrank q.prime (Nat.ne_of_gt q.exponent_pos)
  exact ⟨Fin.cast he k,hk⟩

theorem primePower_card_ringAut_le_logb (q : CFSG.PrimePower) :
    (Nat.card (q.Field ≃+* q.Field) : ℝ)≤Real.logb 2 q.order := by
  simpa only [q.card_field] using card_ringAut_le_logb q.Field

theorem primePower_exponent_le_logb (q : CFSG.PrimePower) :
    (q.exponent : ℝ)≤Real.logb 2 q.order := by
  simpa only [primePower_card_ringAut q] using primePower_card_ringAut_le_logb q

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
