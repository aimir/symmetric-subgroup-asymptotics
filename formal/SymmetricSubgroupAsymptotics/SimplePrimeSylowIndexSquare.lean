import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A nonabelian simple group with a Sylow subgroup of prime order has
order greater than the square of that prime. A degree-prime action with
a moved point then supplies the strict least-index square. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimplePrimeSylowIndexSquare
open PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime]

theorem order_gt_prime_square (hn : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) : p^2 < Nat.card G := by
  have hp := (Fact.out : Nat.Prime p).two_le
  have hne : Nat.card (Sylow p G) ≠ 1 := by
    intro hc
    letI : Subsingleton (Sylow p G) := Finite.card_le_one_iff_subsingleton.mp hc.le
    letI : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) inferInstance with hb | ht
    · have hh : Nat.card P = 1 := by rw [hb,Subgroup.card_bot]
      omega
    · have hh : Nat.card G = p := by
        have he : Nat.card P = Nat.card G := by rw [ht,Subgroup.card_top]
        exact he.symm.trans hP
      letI : IsCyclic G := isCyclic_of_prime_card hh
      exact hn inferInstance
  have hmod : Nat.card (Sylow p G) % p = 1 := by
    have hm := card_sylow_modEq_one p G
    change Nat.card (Sylow p G) % p = 1 % p at hm
    simpa only [Nat.mod_eq_of_lt (show 1 < p by omega)] using hm
  have hcount : p+1 ≤ Nat.card (Sylow p G) := by
    by_contra h
    have hle : Nat.card (Sylow p G) ≤ p := by omega
    by_cases he : Nat.card (Sylow p G) = p
    · rw [he,Nat.mod_self] at hmod
      omega
    · have hlt : Nat.card (Sylow p G) < p := by omega
      rw [Nat.mod_eq_of_lt hlt] at hmod
      exact hne hmod
  let N := Subgroup.normalizer (P : Set G)
  have hN : p ≤ Nat.card N := by
    have hle : Nat.card P ≤ Nat.card N :=
      Nat.le_of_dvd (Nat.card_pos (α := N))
        (Subgroup.card_dvd_of_le (P : Subgroup G).le_normalizer)
    exact (Nat.le_of_eq hP.symm).trans hle
  have hprod : Nat.card N * Nat.card (Sylow p G) = Nat.card G := by
    have hh := N.card_mul_index
    rw [←P.card_eq_index_normalizer] at hh
    exact hh
  have hb := Nat.mul_le_mul hN hcount
  rw [hprod] at hb
  nlinarith

theorem least_index_square_of_moved_point [MulAction G (Fin p)]
    (hn : ¬IsMulCommutative G) (P : Sylow p G) (hP : Nat.card P = p)
    (g : G) (i : Fin p) (hmove : g • i ≠ i)
    (ell : ℕ) (hell : LeastProperIndex G ell) : ell^2 < Nat.card G := by
  let K := MulAction.stabilizer G i
  have hK : K ≠ ⊤ := by
    intro h
    have hg : g ∈ K := by rw [h]; trivial
    exact hmove hg
  have hi : K.index ≤ p := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer G i).trans_le (Set.ncard_le_card _)
  exact (Nat.pow_le_pow_left ((hell.2 K hK).trans hi) 2).trans_lt
    (order_gt_prime_square hn P hP)

end SymmetricSubgroupAsymptotics.SimplePrimeSylowIndexSquare
