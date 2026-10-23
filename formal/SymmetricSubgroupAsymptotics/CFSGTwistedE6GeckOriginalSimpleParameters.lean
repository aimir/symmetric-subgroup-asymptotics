import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Linarith

/-! Actual signed relative-simple parameter charts in the ORIGINAL
twisted E6 group. Singleton lines have q elements and paired lines q^2,
with both assertions proved by injective ORIGINAL homomorphisms. Hence
no original automorphism can exchange these displayed two kinds of line.
No claim of intrinsic recognition of the whole line family is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGE6GeckFixedSimpleParameters CFSGTwistedE6GeckSignedOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGSerreOrdinaryTwists

theorem coefficient_involutive (q : CFSG.PrimePower) :
    Function.Involutive (definingFieldAutomorphism q 2) := by
  intro a
  change (a^q.order)^q.order=a
  exact CFSGTwistedANaturalMatrices.extension_two_pow_twice q a

def singletonOriginalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (neg : Bool) (j : Fin 2) :
    Multiplicative (fixedCoefficient (q.Extension 2) (definingFieldAutomorphism q 2))→*
      CFSG.Models.TwistedE6 q :=
  (signedFixedToOriginal q neg).comp
    (singletonFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) neg j)

def pairedOriginalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (neg : Bool) (j : Fin 2) : Multiplicative (q.Extension 2)→*CFSG.Models.TwistedE6 q :=
  (signedFixedToOriginal q neg).comp
    (pairedFixedHom (q.Extension 2) (definingFieldAutomorphism q 2) (coefficient_involutive q) neg j)

theorem singletonOriginalHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    Function.Injective (singletonOriginalHom q neg j) :=
  (signedFixedToOriginal_injective q neg).comp
    (singletonFixedHom_injective (q.Extension 2) (definingFieldAutomorphism q 2) neg j)

theorem pairedOriginalHom_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    Function.Injective (pairedOriginalHom q neg j) :=
  (signedFixedToOriginal_injective q neg).comp
    (pairedFixedHom_injective (q.Extension 2) (definingFieldAutomorphism q 2)
      (coefficient_involutive q) neg j)

theorem singletonOriginalHom_range_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    Nat.card (singletonOriginalHom q neg j).range=q.order := by
  calc
    _=Nat.card (Multiplicative (fixedCoefficient (q.Extension 2) (definingFieldAutomorphism q 2))) :=
      (Nat.card_congr (MonoidHom.ofInjective (singletonOriginalHom_injective q neg j)).toEquiv).symm
    _=Nat.card (fixedCoefficient (q.Extension 2) (definingFieldAutomorphism q 2)) :=
      Nat.card_congr Multiplicative.toAdd
    _=q.order := CFSGTwistedA2FixedField.fixedField_card q

theorem pairedOriginalHom_range_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    Nat.card (pairedOriginalHom q neg j).range=q.order^2 := by
  calc
    _=Nat.card (Multiplicative (q.Extension 2)) :=
      (Nat.card_congr (MonoidHom.ofInjective (pairedOriginalHom_injective q neg j)).toEquiv).symm
    _=Nat.card (q.Extension 2) := Nat.card_congr Multiplicative.toAdd
    _=q.order^2 := CFSGTwistedANaturalMatrices.extension_two_card q

theorem singleton_image_ne_paired_range (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg₁ neg₂ : Bool) (i j : Fin 2)
    (f : MulAut (CFSG.Models.TwistedE6 q)) :
    (singletonOriginalHom q neg₁ i).range.map f.toMonoidHom≠(pairedOriginalHom q neg₂ j).range := by
  intro he
  have hc := congrArg (fun S : Subgroup (CFSG.Models.TwistedE6 q)=>Nat.card S) he
  dsimp only at hc
  rw [Subgroup.card_map_of_injective f.injective,
    singletonOriginalHom_range_card,pairedOriginalHom_range_card] at hc
  have hq : 2≤q.order := by
    rw [←q.card_field]
    exact Finite.one_lt_card
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSimpleParameters
