import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectNormalGenerators
import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The two possible scalar-and-swap upper groups have uniform normal
width one. The commuting case is the coprime cyclic product; the inverted
case is the faithful irreducible affine action on the prime ternary group.
Neither proof uses a normal-subgroup list. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernarySwapUpperNormalGenerators

open SemidirectProduct

abbrev Ternary := Multiplicative (ZMod 3)
abbrev Binary := Multiplicative (ZMod 2)

def inversion : MulAut Ternary where
  toFun c := c⁻¹
  invFun c := c⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' c d := by rw [mul_inv_rev, mul_comm]

def inversionAction : Binary →* MulAut Ternary where
  toFun b := if b = 1 then 1 else inversion
  map_one' := if_pos rfl
  map_mul' b c := by
    rcases C2Wreath.cases b with rfl | rfl <;>
      rcases C2Wreath.cases c with rfl | rfl
    · simp
    · simp [C2Wreath.gen_ne_one]
    · simp [C2Wreath.gen_ne_one]
    · rw [C2Wreath.gen_mul_gen, if_pos rfl, if_neg C2Wreath.gen_ne_one]
      apply MulEquiv.ext
      intro c
      exact (inv_inv c).symm

def action (twisted : Bool) : Binary →* MulAut Ternary :=
  if twisted then inversionAction else 1

abbrev Upper (twisted : Bool) := Ternary ⋊[action twisted] Binary

theorem inversionAction_injective : Function.Injective inversionAction := by
  rw [injective_iff_map_eq_one]
  intro c hc
  rcases C2Wreath.cases c with rfl | rfl
  · rfl
  · have he := congrArg (fun f : MulAut Ternary ↦ f (Multiplicative.ofAdd 1)) hc
    have hne : inversionAction C2Wreath.gen (Multiplicative.ofAdd 1) ≠
        (1 : MulAut Ternary) (Multiplicative.ofAdd 1) := by decide +kernel
    exact (hne he).elim

theorem ternary_irreducible (φ : Binary →* MulAut Ternary) :
    IrreducibleAbelianSemidirect.Irreducible φ := by
  intro S _
  letI : Fact (Nat.card Ternary).Prime := ⟨by
    simp only [Ternary, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    norm_num⟩
  exact S.eq_bot_or_eq_top_of_prime_card

theorem normal_generating_singletons (twisted : Bool) :
    ∀ N : Subgroup (Upper twisted), N.Normal →
      ∃ x : Fin 1 → Upper twisted, Subgroup.normalClosure (Set.range x) = N := by
  cases twisted
  · let e : Upper false ≃* Ternary × Binary := SemidirectProduct.mulEquivProd
    letI : IsCyclic (Ternary × Binary) := Group.isCyclic_prod_iff.mpr
      ⟨inferInstance, inferInstance, by
        simp only [Ternary, Binary, Nat.card_eq_fintype_card,
          Fintype.card_multiplicative, ZMod.card]
        norm_num⟩
    exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      normal_generating_singletons_of_isCyclic
  · exact IrreducibleAbelianSemidirect.normal_generating_tuples inversionAction
      inversionAction_injective (ternary_irreducible inversionAction) (by decide)
      normal_generating_singletons_of_isCyclic

end TernarySwapUpperNormalGenerators
end SymmetricSubgroupAsymptotics

end
