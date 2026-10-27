import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity

/-! An even involution in degree4*k+3 has at least three fixed points.
The proof uses its actual cycle type, not a finite permutation census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.EvenInvolutionFixedPointLowerBound

theorem three_le_fixed_card_of_card_four_mul_add_three
    {X : Type*} [Fintype X] [DecidableEq X] (sigma : Equiv.Perm X)
    (k : ℕ) (hcard : Fintype.card X = 4*k+3)
    (hsquare : sigma ^ 2 = 1) (hsign : Equiv.Perm.sign sigma = 1) :
    3 ≤ Nat.card {p : X // sigma p = p} := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have htype := Equiv.Perm.cycleType_of_pow_prime_eq_one hsquare
  have hsum : sigma.cycleType.sum = sigma.cycleType.card * 2 := by
    calc
      _ = (Multiset.replicate sigma.cycleType.card 2).sum := congrArg Multiset.sum htype
      _ = _ := by simp only [Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  have hsignCount : Equiv.Perm.sign sigma = (-1 : ℤˣ) ^ sigma.cycleType.card := by
    calc
      _ = (sigma.cycleType.map (fun n => -(-1 : ℤˣ) ^ n)).prod :=
        Equiv.Perm.sign_of_cycleType' sigma
      _ = ((Multiset.replicate sigma.cycleType.card 2).map
          (fun n => -(-1 : ℤˣ) ^ n)).prod :=
        congrArg (fun s : Multiset ℕ => (s.map (fun n => -(-1 : ℤˣ) ^ n)).prod) htype
      _ = _ := by simp only [Multiset.map_replicate,Multiset.prod_replicate,neg_one_sq]
  have heven : Even sigma.cycleType.card :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp
      (hsignCount.symm.trans hsign)
  obtain ⟨t,ht⟩ := heven
  have hbound := sigma.sum_cycleType_le
  rw [hsum,ht,hcard] at hbound
  change 3 ≤ Nat.card (Function.fixedPoints sigma)
  rw [Nat.card_eq_fintype_card,sigma.card_fixedPoints,hcard,hsum,ht]
  omega

theorem three_le_fixed_card_fin_twentyThree (sigma : Equiv.Perm (Fin 23))
    (hsquare : sigma ^ 2 = 1) (hsign : Equiv.Perm.sign sigma = 1) :
    3 ≤ Nat.card {p : Fin 23 // sigma p = p} :=
  three_le_fixed_card_of_card_four_mul_add_three sigma 5 (by decide) hsquare hsign

end SymmetricSubgroupAsymptotics.EvenInvolutionFixedPointLowerBound
