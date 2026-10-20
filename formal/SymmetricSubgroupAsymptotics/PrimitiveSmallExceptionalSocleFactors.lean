import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability

/-! The only exceptional degrees needed by the strict-head reduction force
one nonabelian simple factor. The proof uses actual degree forms, Burnside,
and the elementary lower bound5 on a proper simple-group index. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

private theorem selected_divisor_receipt :
    ∀ r∈({6,9,10,11,12,13,18,27} : Finset ℕ),
      r.divisors⊆({1,2,3,4,5,6,9,10,11,12,13,18,27} : Finset ℕ) := by decide +kernel

theorem isSolvable_of_card_dvd_small_head_degree
    {G : Type} [Group G] [Finite G] (r : ℕ)
    (hr : r=6 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=18 ∨ r=27)
    (hdvd : Nat.card G∣r) : IsSolvable G := by
  have hr0 : r≠0 := by omega
  have hm := selected_divisor_receipt r (by simpa only [Finset.mem_insert,
    Finset.mem_singleton] using hr) (Nat.mem_divisors.mpr ⟨hdvd,hr0⟩)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 0 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 0 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 2 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 5 5 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 1 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 3 3 2 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 5 1 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 11 11 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 2 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 13 13 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 2 3 1 2 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable G 3 3 3 0 (by decide) (by decide) (by norm_num [h])

private theorem selected_power_exponent_one {r a k : ℕ}
    (hr : r=6 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=18 ∨ r=27)
    (ha : 5≤a) (hk : 0<k) (hpower : r=a^k) : k=1 := by
  have hr27 : r≤27 := by omega
  have hk3 : k<3 := by
    by_contra h
    have h3 : 3≤k := by omega
    have hlarge : 125≤r := calc
      125=5^3 := by decide
      _ ≤ a^3 := Nat.pow_le_pow_left ha 3
      _ ≤ a^k := Nat.pow_le_pow_right (by omega) h3
      _ = r := hpower.symm
    omega
  have hcases : k=1 ∨ k=2 := by omega
  rcases hcases with h|h
  · exact h
  · have ha6 : a<6 := by
      by_contra h6
      have h6' : 6≤a := by omega
      have h36 : 36≤r := calc
        36=6^2 := by decide
        _ ≤ a^2 := Nat.pow_le_pow_left h6' 2
        _ = r := by simpa only [h] using hpower.symm
      omega
    have ha5 : a=5 := by omega
    have hr25 : r=25 := by simpa only [ha5,h] using hpower
    omega

namespace PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.factorCount_eq_one_of_small_head_degree
    (D : NonaffineData G X)
    (hdegree : Nat.card X=6 ∨ Nat.card X=9 ∨ Nat.card X=10 ∨ Nat.card X=11 ∨
      Nat.card X=12 ∨ Nat.card X=13 ∨ Nat.card X=18 ∨ Nat.card X=27) :
    D.factorCount=1 := by
  rcases D.indexForm with ⟨H,hH,hform⟩ | ⟨a,_,hform⟩
  · exact selected_power_exponent_one hdegree
      (nonabelianSimple_proper_index_five_le
        (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) H hH)
      D.factorCount_pos hform
  · have ha : a≠0 := by
      intro h
      rw [h,pow_zero] at hform
      omega
    have hdvd : Nat.card D.Simple∣Nat.card X := by
      rw [hform]
      exact dvd_pow_self _ ha
    have hs := isSolvable_of_card_dvd_small_head_degree (Nat.card X) hdegree hdvd
    exact (D.noncommutative ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩).elim

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
