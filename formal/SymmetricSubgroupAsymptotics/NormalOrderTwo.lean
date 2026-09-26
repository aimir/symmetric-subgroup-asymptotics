import SymmetricSubgroupAsymptotics.PrimeNormalHeadOrder
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.GroupTheory.OrderOfElement

/-! An order-two subgroup normal in the ORIGINAL ambient group is
central. Its original relative binary radical, head, and complete normal
head maximum follow without replacing the ambient conjugation action. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.NormalOrderTwo

variable {G : Type*} [Group G]

theorem eq_of_ne_one (S : Subgroup G) (hcard : Nat.card S = 2)
    (x y : S) (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hcard
  exact (ha x hx).trans (ha y hy).symm

theorem square_eq_one (S : Subgroup G) (hcard : Nat.card S = 2) (x : S) :
    (x : G) ^ 2 = 1 := by
  have h : x ^ Nat.card S = 1 := pow_card_eq_one'
  rw [hcard] at h
  exact congrArg Subtype.val h

theorem le_center (S : Subgroup G) [S.Normal] (hcard : Nat.card S = 2) :
    S ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  by_cases h1 : x = 1
  · simp only [h1, mul_one, one_mul]
  · let s : S := ⟨x, hx⟩
    let c : S := ⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hx g⟩
    have hs : s ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    have hc : c ≠ 1 := by
      intro h
      have he : g * x * g⁻¹ = 1 := congrArg Subtype.val h
      apply h1
      apply mul_left_cancel (a := g)
      exact (mul_inv_eq_one.mp he).trans (mul_one g).symm
    have he : g * x * g⁻¹ = x := congrArg Subtype.val (eq_of_ne_one S hcard c s hc hs)
    have hm := congrArg (fun z : G => z * g) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

theorem relativeRadical_eq_bot (S : Subgroup G) [S.Normal] (hcard : Nat.card S = 2) :
    primeRelativeRadical 2 S = ⊥ := by
  apply le_antisymm _ bot_le
  rw [primeRelativeRadical_eq_powerCommutator]
  apply sup_le
  · apply (Subgroup.closure_le (⊥ : Subgroup G)).mpr
    rintro _ ⟨x, rfl⟩
    exact square_eq_one S hcard x
  · apply Subgroup.commutator_le.mpr
    intro x hx g _
    change ⁅x, g⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp (le_center S hcard hx) g).symm

variable [Finite G]

theorem relativeHead_eq_one (S : Subgroup G) [S.Normal] (hcard : Nat.card S = 2) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 S) = 1 := by
  have h : Nat.card S = 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 S) *
      Nat.card (primeRelativeRadical 2 S) := primeRelativeRadical_card_factorization 2 S
  rw [relativeRadical_eq_bot S hcard, hcard, Subgroup.card_bot, mul_one] at h
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h.symm

theorem normalHeadMax_eq_one (S : Subgroup G) [S.Normal] (hcard : Nat.card S = 2) :
    primeNormalHeadMax 2 S = 1 := by
  apply le_antisymm
  · exact (primeNormalHeadMax_le_log_card 2 S).trans (by rw [hcard]; decide)
  · have h := primeRelativeHead_le_normalHeadMax 2 S S le_rfl
    rwa [relativeHead_eq_one S hcard] at h

theorem subgroup_cases (S : Subgroup G) (hcard : Nat.card S = 2)
    (M : Subgroup G) (hM : M ≤ S) : M = ⊥ ∨ M = S := by
  have hc : Nat.card M ≤ 2 := by
    have h := Subgroup.card_le_of_le hM
    rwa [hcard] at h
  by_cases hs : Nat.card M ≤ 1
  · exact Or.inl (M.eq_bot_of_card_le hs)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hM (by rw [hcard]; omega))

theorem relativeRadical_bot : primeRelativeRadical 2 (⊥ : Subgroup G) = ⊥ :=
  le_antisymm (primeRelativeRadical_le 2 ⊥) bot_le

theorem relativeHead_bot :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (⊥ : Subgroup G)) = 0 := by
  have h := primeRelativeRadical_card_factorization 2 (⊥ : Subgroup G)
  rw [relativeRadical_bot, Subgroup.card_bot, mul_one] at h
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h.symm

theorem normalHeadMax_bot : primeNormalHeadMax 2 (⊥ : Subgroup G) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (primeNormalHeadMax_le_log_card 2 (⊥ : Subgroup G)).trans
    (by rw [Subgroup.card_bot]; decide)

end SymmetricSubgroupAsymptotics.NormalOrderTwo
