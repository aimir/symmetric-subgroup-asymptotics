import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import Mathlib.Tactic.NormNum

/-! Sum the actual commuting-pair capacities with the original identity
pair counted only once. An identity reserve of4T and off-identity boundT
cost at most(k(Q)+1)T after dividing by |Q|>=3. There is no independent
kernel/top maximum or splitting assertion in this finite sum lemma. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CommutingPairIdentityReserveBound
open AbelianActionClassBound
variable {Q : Type*} [Group Q]

def identityPair : CommutingPairs Q := ⟨(1,1),rfl⟩

def weightedSum [Finite Q] (f : CommutingPairs Q→ℕ) : ℕ :=
  letI : Fintype (CommutingPairs Q) := Fintype.ofFinite _
  ∑ t : CommutingPairs Q, f t

/-- The actual identity summand is separated from the remaining actual
commuting pairs before any numerical reserve is charged. -/
theorem sum_le_identity_add_off [Finite Q] (f : CommutingPairs Q→ℕ) (a T : ℕ)
    (hidentity : f identityPair≤a)
    (hoff : ∀ t : CommutingPairs Q, t≠identityPair → f t≤T) :
    weightedSum f≤a+(Nat.card (CommutingPairs Q)-1)*T := by
  letI : Fintype (CommutingPairs Q) := Fintype.ofFinite _
  change (∑ t : CommutingPairs Q, f t)≤_
  rw [←Finset.add_sum_erase _ _ (Finset.mem_univ (identityPair : CommutingPairs Q))]
  apply Nat.add_le_add hidentity
  calc
    (∑ t ∈ (Finset.univ : Finset (CommutingPairs Q)).erase identityPair, f t)≤
        ∑ _t ∈ (Finset.univ : Finset (CommutingPairs Q)).erase identityPair, T := by
      apply Finset.sum_le_sum
      intro t ht
      exact hoff t (Finset.mem_erase.mp ht).1
    _=(Nat.card (CommutingPairs Q)-1)*T := by
      simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ,smul_eq_mul,←Nat.card_eq_fintype_card]

/-- |Q|>=3 absorbs the three extra identity units. The same original
commuting-pair sum is retained in the conclusion. -/
theorem sum_le_group_mul_class_add_one [Finite Q] (f : CommutingPairs Q→ℕ) (T : ℕ)
    (hQ : 3≤Nat.card Q) (hidentity : f identityPair≤4*T)
    (hoff : ∀ t : CommutingPairs Q, t≠identityPair → f t≤T) :
    weightedSum f≤Nat.card Q*((Nat.card (ConjClasses Q)+1)*T) := by
  have hcard : Nat.card (CommutingPairs Q)=Nat.card Q*Nat.card (ConjClasses Q) := by
    rw [card_comm_eq_card_conjClasses_mul_card]
    exact Nat.mul_comm _ _
  have hn : 1≤Nat.card (CommutingPairs Q) := by
    letI : Nonempty (CommutingPairs Q) := ⟨identityPair⟩
    exact Nat.card_pos
  calc
    weightedSum f≤4*T+(Nat.card (CommutingPairs Q)-1)*T :=
      sum_le_identity_add_off f (4*T) T hidentity hoff
    _=(Nat.card (CommutingPairs Q)+3)*T := by
      rw [←Nat.add_mul]
      exact congrArg (fun n : ℕ => n*T) (by omega)
    _=Nat.card (CommutingPairs Q)*T+3*T := Nat.add_mul _ _ _
    _≤Nat.card (CommutingPairs Q)*T+Nat.card Q*T :=
      Nat.add_le_add_left (Nat.mul_le_mul_right T hQ) _
    _=Nat.card Q*((Nat.card (ConjClasses Q)+1)*T) := by rw [hcard]; ring

/-- Exact scalar margins for the two original point degrees that
motivate the shared identity reserve, without an action catalogue. -/
theorem binary_seven : ((12+1)*2^(7-2))^3≤5^(2*7-2) := by norm_num

theorem binary_eight : ((12+1)*2^(8-2))^3≤5^(2*8-2) := by norm_num

end SymmetricSubgroupAsymptotics.CommutingPairIdentityReserveBound
