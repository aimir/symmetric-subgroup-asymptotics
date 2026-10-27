import SymmetricSubgroupAsymptotics.FiniteGroupOrderBelowThirtySolvable
import SymmetricSubgroupAsymptotics.SimplePrimeSylowSuccessorIndexSquare

/-! Burnside handles orders below sixty except30/42. Transfer's genuine
cyclic-Sylow normalizer lower bound excludes those two simple-group cases. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonabelianSimpleOrderAtLeastSixty

private def p : Fin 30 → ℕ :=
  ![2,31,2,3,2,5,2,37,2,3,2,41,2,43,2,3,2,47,2,7,2,3,2,53,2,5,2,3,2,59]
private def q : Fin 30 → ℕ :=
  ![3,31,2,11,17,7,3,37,19,13,5,41,3,43,11,5,23,47,3,7,5,17,13,53,3,11,7,19,29,59]
private def a : Fin 30 → ℕ :=
  ![1,1,5,1,1,1,2,1,1,1,3,1,1,1,2,2,1,1,4,2,1,1,2,1,1,1,3,1,1,1]
private def b : Fin 30 → ℕ :=
  ![1,0,0,1,1,1,2,0,1,1,1,0,1,0,1,1,1,0,1,0,2,1,1,0,3,1,1,1,1,0]
private theorem specification : ∀ i : Fin 30, i.val≠0 → i.val≠12 →
    (p i).Prime ∧ (q i).Prime ∧ i.val+30=p i ^ a i * q i ^ b i := by
  decide +kernel

private theorem not_thirty {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : Nat.card G≠30 := by
  intro hcard
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := Classical.choice inferInstance
  have hP : Nat.card P=5 := by rw [P.card_eq_multiplicity,hcard]; decide +kernel
  have hN := SimplePrimeSylowSuccessorIndexSquare.normalizer_card_ge_twice_prime hn P hP
  have hc := SimplePrimeSylowSuccessorIndexSquare.sylow_count_ge_prime_succ hn P hP
  have hm := (Subgroup.normalizer (P : Set G)).card_mul_index
  rw [←P.card_eq_index_normalizer,hcard] at hm
  have hb := Nat.mul_le_mul hN hc
  rw [hm] at hb
  norm_num at hb

private theorem not_fortyTwo {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : Nat.card G≠42 := by
  intro hcard
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 G := Classical.choice inferInstance
  have hP : Nat.card P=7 := by rw [P.card_eq_multiplicity,hcard]; decide +kernel
  have hN := SimplePrimeSylowSuccessorIndexSquare.normalizer_card_ge_twice_prime hn P hP
  have hc := SimplePrimeSylowSuccessorIndexSquare.sylow_count_ge_prime_succ hn P hP
  have hm := (Subgroup.normalizer (P : Set G)).card_mul_index
  rw [←P.card_eq_index_normalizer,hcard] at hm
  have hb := Nat.mul_le_mul hN hc
  rw [hm] at hb
  norm_num at hb

theorem sixty_le_card (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : 60≤Nat.card G := by
  have hlo := FiniteGroupOrderBelowThirtySolvable.thirty_le_card_of_nonabelian_simple G hn
  have h30 := not_thirty hn
  have h42 := not_fortyTwo hn
  by_contra hh
  let i : Fin 30 := ⟨Nat.card G-30,by omega⟩
  have hs := specification i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have he : Nat.card G=p i ^ a i * q i ^ b i := by
    have hi : i.val+30=Nat.card G := by dsimp only [i]; omega
    exact hi.symm.trans hs.2.2
  letI : IsSolvable G := burnsideTwoPrimeSolvability.solvable G
    (p i) (q i) (a i) (b i) hs.1 hs.2.1 he
  exact hn (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))

end SymmetricSubgroupAsymptotics.NonabelianSimpleOrderAtLeastSixty
