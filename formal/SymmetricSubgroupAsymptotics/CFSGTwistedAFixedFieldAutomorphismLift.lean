import SymmetricSubgroupAsymptotics.CFSGFiniteFieldFrobeniusEmbedding
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField

/-! Every actual quadratic Frobenius-fixed field automorphism extends to
the SAME original quadratic extension. A power of its arithmetic
Frobenius gives the extension and commutes with the defining involution.
There is no field-extension or semilinear-recognition hypothesis here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
open CFSGFiniteFieldAutomorphisms CFSGSerreOrdinaryTwists

def baseFixedEquiv (q : CFSG.PrimePower) : q.Field ≃+* fixedField q :=
  RingEquiv.ofBijective (baseToFixed q)
    ((baseToFixed q).injective.bijective_of_nat_card_le (by
      rw [fixedField_card, q.card_field]))

theorem baseFixedEquiv_val (q : CFSG.PrimePower) (x : q.Field) :
    (baseFixedEquiv q x).val = baseEmbedding q x := rfl

theorem extension_automorphism_commutes_defining (q : CFSG.PrimePower)
    (tau : q.Extension 2 ≃+* q.Extension 2) :
    Function.Commute (definingFieldAutomorphism q 2) tau := by
  intro x
  simp only [definingFieldAutomorphism_apply, map_pow]

theorem exists_fixedField_automorphism_lift (q : CFSG.PrimePower)
    (rho : fixedField q ≃+* fixedField q) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      (∀ a : fixedField q, tau a.val = (rho a).val) ∧
        Function.Commute (definingFieldAutomorphism q 2) tau := by
  let e := baseFixedEquiv q
  let r : q.Field ≃+* q.Field := (e.trans rho).trans e.symm
  obtain ⟨k, hk⟩ := primePower_exists_frobenius_pow q r
  let tau : q.Extension 2 ≃+* q.Extension 2 := primeFrobenius (q.Extension 2) q.prime ^ k.val
  refine ⟨tau, ?_, extension_automorphism_commutes_defining q tau⟩
  intro a
  let x := e.symm a
  have hx : baseEmbedding q x = a.val := congrArg (fun b : fixedField q => b.val) (e.apply_symm_apply a)
  rw [← hx]
  have ht : tau (baseEmbedding q x) = baseEmbedding q (r x) := by
    have hm := embedding_primeFrobenius_pow q.prime (baseEmbedding q).toRingHom k.val x
    change tau (baseEmbedding q x) = baseEmbedding q ((primeFrobenius q.Field q.prime ^ k.val) x) at hm
    rw [hk] at hm
    exact hm
  rw [ht]
  have he : e (r x) = rho a := by
    dsimp only [r, RingEquiv.trans_apply]
    rw [e.apply_symm_apply, e.apply_symm_apply]
  exact congrArg (fun b : fixedField q => b.val) he

end SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
