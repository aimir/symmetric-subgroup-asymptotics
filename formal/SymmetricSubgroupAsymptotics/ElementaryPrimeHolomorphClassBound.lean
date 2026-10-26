import SymmetricSubgroupAsymptotics.BinaryEightElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.BinaryThirtyTwoParabolicSubgroupClassBound
import SymmetricSubgroupAsymptotics.BinarySixtyFourElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.TernaryTwentySevenParabolicSubgroupClassBound
import SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassGap
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
import Mathlib.Tactic.IntervalCases

/-! The actual elementary affine image has a proved class bound at each
small prime rank. These are vector-rank cases, not a group or action
census. The full original subgroup of the literal holomorph is kept. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElementaryPrimeHolomorphClassBound

private def autPermutation (N : Type) [Group N] : MulAut N →* Equiv.Perm N where
  toFun a := a.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private def permutationHom (N : Type) [Group N] :
    N ⋊[MonoidHom.id (MulAut N)] MulAut N →* Equiv.Perm N :=
  SemidirectProduct.lift (MulAction.toPermHom N N) (autPermutation N) (by
    intro a
    apply MonoidHom.ext
    intro n
    apply Equiv.ext
    intro x
    change a n*x=a (n*a.symm x)
    rw [map_mul,MulEquiv.apply_symm_apply])

private theorem permutationHom_injective (N : Type) [Group N] :
    Function.Injective (permutationHom N) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hpoint (n : N) : g.left*g.right n=n := by
    change permutationHom N g n=n
    rw [hg]
    rfl
  have hl : g.left=1 := by simpa only [map_one,mul_one] using hpoint 1
  have hr : g.right=1 := by
    apply MulEquiv.ext
    intro n
    simpa only [hl,one_mul,MulAut.one_apply] using hpoint n
  exact SemidirectProduct.ext hl hr

private theorem small_subgroup_bound (N : Type) [Group N] [Finite N]
    (hsmall : Nat.card N≤4)
    (H : Subgroup (N ⋊[MonoidHom.id (MulAut N)] MulAut N)) :
    Nat.card (ConjClasses H)≤
      if Nat.card N≤1 then 1 else if Nat.card N≤2 then 2 else
        if Nat.card N≤3 then 3 else 5 := by
  let f := (permutationHom N).comp H.subtype
  have hf : Function.Injective f := (permutationHom_injective N).comp Subtype.val_injective
  letI : Finite H := Finite.of_injective f hf
  have hc : Nat.card (ConjClasses H)≤Nat.card (ConjClasses f.range) :=
    (conjugacyClass_card_congr (MonoidHom.ofInjective hf)).le
  apply hc.trans
  by_cases h1 : Nat.card N≤1
  · simp only [if_pos h1]
    exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (f.range.card_le_card_group.trans (by
        rw [Nat.card_perm]
        simpa using Nat.factorial_le h1))
  · simp only [if_neg h1]
    by_cases h2 : Nat.card N≤2
    · simp only [if_pos h2]
      exact SmallPermutationClassBudgets.subgroup_class_card_le_two h2 f.range
    · simp only [if_neg h2]
      by_cases h3 : Nat.card N≤3
      · simp only [if_pos h3]
        exact SmallPermutationClassBudgets.subgroup_class_card_le_three h3 f.range
      · simp only [if_neg h3]
        have h4 : Nat.card N=4 := by omega
        let e : N≃Fin 4 := Finite.equivFinOfCardEq h4
        let L := f.range.map e.permCongrHom.toMonoidHom
        have ht : Nat.card (ConjClasses f.range)≤Nat.card (ConjClasses L) :=
          (conjugacyClass_card_congr (e.permCongrHom.subgroupMap f.range)).le
        exact ht.trans (FourPointPermutationClassBound.subgroup_class_card_le_five L)

def binaryBudget : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 24
  | 4 => 772
  | 5 => 351240
  | _ => 32*(2^30+1)

def ternaryBudget : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 39
  | _ => 12247

local instance finiteAut (N : Type) [Group N] [Finite N] : Finite (MulAut N) :=
  Finite.of_injective (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective

variable {N : Type} [CommGroup N] [Finite N]

theorem binary_subgroup_class_card_le [Module (ZMod 2) (Additive N)]
    (r : ℕ) (hr : r≤6) (hcard : Nat.card N=2^r)
    (H : Subgroup (N ⋊[MonoidHom.id (MulAut N)] MulAut N)) :
    Nat.card (ConjClasses H)≤binaryBudget r := by
  interval_cases r
  · simpa [hcard,binaryBudget] using small_subgroup_bound N
      (by rw [hcard]; decide) H
  · simpa [hcard,binaryBudget] using small_subgroup_bound N
      (by rw [hcard]; decide) H
  · simpa [hcard,binaryBudget] using small_subgroup_bound N
      (by rw [hcard]; decide) H
  · exact BinaryEightElementSemidirectClassBound.subgroup_class_card_le_twentyFour
      rfl (by simpa using hcard) (MonoidHom.id _) Function.injective_id H
  · exact BinarySixteenParabolicSubgroupClassBound.subgroup_class_card_le_sevenSeventyTwo
      rfl (by simpa using hcard) (MonoidHom.id _) Function.injective_id H
  · exact BinaryThirtyTwoParabolicSubgroupClassBound.subgroup_class_card_le_threeFiftyOneTwoForty
      rfl (by simpa using hcard) (MonoidHom.id _) Function.injective_id H
  · exact BinarySixtyFourElementSemidirectClassBound.subgroup_class_card_le
      rfl (by simpa using hcard) (MonoidHom.id _) Function.injective_id H

theorem ternary_subgroup_class_card_le [Module (ZMod 3) (Additive N)]
    (r : ℕ) (hr : r≤3) (hcard : Nat.card N=3^r)
    (H : Subgroup (N ⋊[MonoidHom.id (MulAut N)] MulAut N)) :
    Nat.card (ConjClasses H)≤ternaryBudget r := by
  interval_cases r
  · simpa [hcard,ternaryBudget] using small_subgroup_bound N
      (by rw [hcard]; decide) H
  · simpa [hcard,ternaryBudget] using small_subgroup_bound N
      (by rw [hcard]; decide) H
  · exact NineElementSemidirectSubgroupClassGap.subgroup_class_card_le_thirtyNine
      (by simpa using hcard) (MonoidHom.id _) Function.injective_id H
  · exact TernaryTwentySevenParabolicSubgroupClassBound.subgroup_class_card_le_twelveTwoFortySeven
      (by simpa using hcard) (MonoidHom.id _) Function.injective_id H

end SymmetricSubgroupAsymptotics.ElementaryPrimeHolomorphClassBound
