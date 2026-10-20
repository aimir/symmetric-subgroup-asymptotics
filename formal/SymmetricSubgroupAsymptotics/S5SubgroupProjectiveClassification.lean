import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.PublishedBurnsideTwoPrimeSolvability
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.NormNum

/-! Subgroups of S5 without A5 have order at most24, by the faithful
coset action and the factorial bound. Burnside's group-uniform two-prime
theorem then proves they are soluble. No subgroup census or published
S5-subgroup classification is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.S5SubgroupProjectiveClassification
abbrev FiveSymmetric := Equiv.Perm (Fin 5)
abbrev FiveAlternating : Subgroup FiveSymmetric := alternatingGroup (Fin 5)

theorem card_symmetric : Nat.card FiveSymmetric=120 := by
  rw [Nat.card_perm,Nat.card_fin]
  decide +kernel

theorem card_le_twentyFour_of_not_contains (P : Subgroup FiveSymmetric)
    (hA : ¬ FiveAlternating ≤ P) : Nat.card P ≤ 24 := by
  have hcore : P.normalCore=⊥ := by
    by_contra h
    letI : P.normalCore.Normal := P.normalCore_normal
    letI : Nontrivial P.normalCore := P.normalCore.nontrivial_iff_ne_bot.mpr h
    have he : FiveAlternating ≤ P.normalCore :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp [FiveSymmetric]) inferInstance
    exact hA (he.trans P.normalCore_le)
  have hdiv : P.normalCore.index ∣ P.index.factorial := by
    rw [Subgroup.normalCore_eq_ker,Subgroup.index_ker,Subgroup.index_eq_card,← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card (MulAction.toPermHom FiveSymmetric (FiveSymmetric ⧸ P)).range
  rw [hcore,Subgroup.index_bot,card_symmetric] at hdiv
  have hi : 5 ≤ P.index := by
    by_contra h
    have hsmall : P.index ≤ 4 := by omega
    have hfac : P.index.factorial ≤ 24 := by
      exact (Nat.factorial_le hsmall).trans (by decide)
    have hlarge : 120 ≤ P.index.factorial := Nat.le_of_dvd (Nat.factorial_pos _) hdiv
    omega
  have hmul := Nat.mul_le_mul_left (Nat.card P) hi
  have hc := P.card_mul_index
  rw [card_symmetric] at hc
  omega

private def order : Fin 12 → ℕ := ![1,2,3,4,5,6,8,10,12,15,20,24]
private def p : Fin 12 → ℕ := ![2,2,3,2,5,2,2,2,2,3,2,2]
private def q : Fin 12 → ℕ := ![3,3,2,3,2,3,3,5,3,5,5,3]
private def a : Fin 12 → ℕ := ![0,1,1,2,1,1,3,1,2,1,2,3]
private def b : Fin 12 → ℕ := ![0,0,0,0,0,1,0,1,1,1,1,1]
private theorem order_specification (i : Fin 12) :
    Nat.Prime (p i) ∧ Nat.Prime (q i) ∧ order i=(p i)^(a i)*(q i)^(b i) := by
  fin_cases i <;> decide +kernel
private theorem divisor_menu : ∀ n : Fin 25,n.val ∣ 120 → ∃ i : Fin 12,n.val=order i := by
  decide +kernel

theorem isSolvable_of_not_contains (B : PublishedBurnsideTwoPrimeSolvabilityInput)
    (P : Subgroup FiveSymmetric) (hA : ¬ FiveAlternating ≤ P) : IsSolvable P := by
  have hcard := card_le_twentyFour_of_not_contains P hA
  have hdiv : Nat.card P ∣ 120 := by
    simpa only [card_symmetric] using Subgroup.card_subgroup_dvd_card P
  obtain ⟨i,hi⟩ := divisor_menu ⟨Nat.card P,by omega⟩ hdiv
  exact B.solvable P (p i) (q i) (a i) (b i)
    (order_specification i).1 (order_specification i).2.1
    (hi.trans (order_specification i).2.2)

theorem not_isSolvable_alternating : ¬ IsSolvable FiveAlternating := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  intro h
  have hc : IsMulCommutative FiveAlternating :=
    ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr h⟩⟩
  rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hc
  norm_num at hc

theorem card_le_twentyFour_of_isSolvable (P : Subgroup FiveSymmetric)
    (hP : IsSolvable P) : Nat.card P ≤ 24 := by
  apply card_le_twentyFour_of_not_contains P
  intro hA
  letI : IsSolvable P := hP
  exact not_isSolvable_alternating
    (solvable_of_solvable_injective (Subgroup.inclusion_injective hA))

theorem alternating_le_of_not_isSolvable
    (B : PublishedBurnsideTwoPrimeSolvabilityInput) (P : Subgroup FiveSymmetric)
    (hP : ¬ IsSolvable P) : FiveAlternating ≤ P := by
  by_contra hA
  exact hP (isSolvable_of_not_contains B P hA)

theorem eq_alternating_or_top_of_not_isSolvable
    (B : PublishedBurnsideTwoPrimeSolvabilityInput) (P : Subgroup FiveSymmetric)
    (hP : ¬ IsSolvable P) : P=FiveAlternating ∨ P=⊤ :=
  indexTwo_maximal FiveAlternating alternatingGroup.index_eq_two P
    (alternating_le_of_not_isSolvable B P hP)

end SymmetricSubgroupAsymptotics.S5SubgroupProjectiveClassification
