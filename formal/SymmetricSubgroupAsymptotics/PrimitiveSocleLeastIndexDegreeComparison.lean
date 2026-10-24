import SymmetricSubgroupAsymptotics.SimpleLeastIndexStrictOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Least-index degree comparisons from the literal structural degree
forms alone. No simple index-square bound or outer estimate is used.
In particular, two-factor primitive actions and every smaller local
component give genuinely smaller simple coset actions for induction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
open PrimitiveSocleRawStructure

theorem least_index_lt_order (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hnc : ¬ IsMulCommutative T) (ell : ℕ) (hell : LeastProperIndex T ell) :
    ell < Nat.card T := by
  obtain ⟨x,hx⟩ := exists_ne (1 : T)
  let H := Subgroup.zpowers x
  have hHne : H ≠ ⊥ := by
    intro he
    have hm : x ∈ H := Subgroup.mem_zpowers x
    rw [he] at hm
    exact hx (Subgroup.mem_bot.mp hm)
  have hHtop : H ≠ ⊤ := by
    intro he
    letI : IsCyclic T := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x,he⟩
    exact hnc inferInstance
  have hi0 : 0 < H.index := by rw [H.index_eq_card]; exact Nat.card_pos
  have hsmall : H.index < Nat.card T := by
    rw [←H.index_mul_card]
    exact lt_mul_of_one_lt_right hi0 (H.one_lt_card_iff_ne_bot.mpr hHne)
  exact (hell.2 H hHtop).trans_lt hsmall

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem least_index_le_degree (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    ell ≤ Nat.card X := by
  rcases D.indexForm with ⟨H,hH,hdegree⟩ | ⟨a,hka,hdegree⟩
  · have hi := H.one_lt_index_of_ne_top hH
    have hp : H.index ≤ H.index^D.factorCount := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < H.index)
        (show 1 ≤ D.factorCount by have hh := D.factorCount_pos; omega)
    exact ((hell.2 H hH).trans hp).trans_eq hdegree.symm
  · have ha : 1 ≤ a := by have hh := D.factorCount_pos; omega
    have hp : Nat.card D.Simple ≤ Nat.card D.Simple^a := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (Nat.card_pos (α := D.Simple)) ha
    exact ((least_index_lt_order D.Simple D.noncommutative ell hell).le.trans hp).trans_eq
      hdegree.symm

theorem least_index_lt_degree_of_two_factors (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hk : 2 ≤ D.factorCount) :
    ell < Nat.card X := by
  rcases D.indexForm with ⟨H,hH,hdegree⟩ | ⟨a,hka,hdegree⟩
  · have hi := H.one_lt_index_of_ne_top hH
    have hp : H.index^2 ≤ H.index^D.factorCount :=
      Nat.pow_le_pow_right (by omega : 0 < H.index) hk
    have hs : H.index < H.index^2 := by
      simpa only [pow_two,mul_one] using
        Nat.mul_lt_mul_of_pos_left hi (by omega : 0 < H.index)
    exact ((hell.2 H hH).trans_lt (hs.trans_le hp)).trans_eq hdegree.symm
  · have ha : 1 ≤ a := by omega
    have hp : Nat.card D.Simple ≤ Nat.card D.Simple^a := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (Nat.card_pos (α := D.Simple)) ha
    exact ((least_index_lt_order D.Simple D.noncommutative ell hell).trans_le hp).trans_eq
      hdegree.symm

end SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
