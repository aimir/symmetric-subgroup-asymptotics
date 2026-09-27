import SymmetricSubgroupAsymptotics.BinaryTranslationMoments
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-! Four-point translation moments in an exact original point chart. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryTranslationMoments

variable {V X : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem sum_eq_zero_of_card_four (hV : Nat.card V=4) : (∑ v : V,v)=0 := by
  have hd : Module.finrank (ZMod 2) V=2 := by
    apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV,Nat.card_zmod] at hc
    exact hc.symm
  let e : V ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hd,Module.finrank_prod]; simp)
  have hs : (∑ v : ZMod 2 × ZMod 2,v)=0 := by decide +kernel
  apply e.injective
  rw [map_sum,map_zero]
  exact (Equiv.sum_comp e.toEquiv (fun v => v)).trans hs

def leftFunction (e : V ⊕ V ≃ X) (f : X → ZMod 2) : V → ZMod 2 :=
  fun v => f (e (Sum.inl v))

def rightFunction (e : V ⊕ V ≃ X) (f : X → ZMod 2) : V → ZMod 2 :=
  fun v => f (e (Sum.inr v))

/-- The inverse permutation in the permutation-function action is
derived from the actual point action, with the same original chart. -/
theorem leftFunction_permutation (e : V ⊕ V ≃ X) (t : Equiv.Perm X) (u : V)
    (ht : ∀ v,t (e (Sum.inl v))=e (Sum.inl (u+v))) (f : X → ZMod 2) :
    leftFunction e (fun x => f (t⁻¹ x))=translate u (leftFunction e f) := by
  funext v
  change f (t⁻¹ (e (Sum.inl v)))=f (e (Sum.inl (v-u)))
  apply congrArg f
  apply t.injective
  change t (t.symm (e (Sum.inl v)))=t (e (Sum.inl (v-u)))
  rw [Equiv.apply_symm_apply,ht]
  congr 2
  abel

theorem leftFunction_add (e : V ⊕ V ≃ X) (f g : X → ZMod 2) :
    leftFunction e (f+g)=leftFunction e f+leftFunction e g := rfl

theorem leftFunction_sub (e : V ⊕ V ≃ X) (f g : X → ZMod 2) :
    leftFunction e (f-g)=leftFunction e f-leftFunction e g := rfl

/-- Block constants in the literal four-point chart have zero moment. -/
theorem left_moment_eq_zero_of_constant (hV : Nat.card V=4)
    (e : V ⊕ V ≃ X) (f : X → ZMod 2)
    (hf : ∀ v,f (e (Sum.inl v))=f (e (Sum.inl 0))) :
    moment (leftFunction e f)=0 := by
  have he : leftFunction e f=(fun _ : V => f (e (Sum.inl 0))) := funext hf
  rw [he,moment_const,sum_eq_zero_of_card_four hV,smul_zero]

/-- The two exact original affine products give a vector equation after
passing only through the literal first-block moment. -/
theorem left_commutator_moment (e : V ⊕ V ≃ X)
    (t s : Equiv.Perm X) (u v : V)
    (ht : ∀ x,t (e (Sum.inl x))=e (Sum.inl (u+x)))
    (hs : ∀ x,s (e (Sum.inl x))=e (Sum.inl (v+x)))
    (a b : X → ZMod 2) :
    moment (leftFunction e
      ((fun x => b (t⁻¹ x))+a-((fun x => a (s⁻¹ x))+b)))=
      parity (leftFunction e b) • u+parity (leftFunction e a) • v := by
  rw [leftFunction_sub,leftFunction_add,leftFunction_add,
    leftFunction_permutation e t u ht,leftFunction_permutation e s v hs,
    moment_commutator_binary]

end SymmetricSubgroupAsymptotics.BinaryTranslationMoments
