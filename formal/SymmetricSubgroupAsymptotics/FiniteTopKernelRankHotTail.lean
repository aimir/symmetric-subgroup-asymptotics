import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHot
import SymmetricSubgroupAsymptotics.BinaryRankTailFiftyOne
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! A bounded finite top preserves the quadratic binary-rank deficit after
multiplying by the entire literal target fibre, on the same complete source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
variable (T Q : Type) [Group T] [Group Q] [Finite T] [Finite Q]

theorem finiteTopKernelRankHot51_card_le (b : ℕ) :
    ((Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      FiniteTopKernelRankHot T (51/200) J)).card : ℝ) ≤
      (Nat.factorial b : ℝ)^Nat.card T *
        ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ)) := by
  have hJc : (Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      FiniteTopKernelRankHot T (51/200) J)).card =
      Nat.card {J : Subgroup (Equiv.Perm (Fin b)) // FiniteTopKernelRankHot T (51/200) J} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hFc : (Finset.univ.filter (fun F : Subgroup (Equiv.Perm (Fin b)) =>
      BinaryRankHot (51/200) F)).card =
      Nat.card {F : Subgroup (Equiv.Perm (Fin b)) // BinaryRankHot (51/200) F} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hc : ((Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      FiniteTopKernelRankHot T (51/200) J)).card : ℝ) ≤
      (Nat.factorial b : ℝ)^Nat.card T *
        ((Finset.univ.filter (fun F : Subgroup (Equiv.Perm (Fin b)) =>
          BinaryRankHot (51/200) F)).card : ℝ) := by
    rw [hJc,hFc]
    exact_mod_cast hot_card_le T (51/200) b
  exact hc.trans (mul_le_mul_of_nonneg_left (binaryRankHot51_card_le b) (by positivity))

/-- No exceptional quotient map is discarded on a hot source. -/
theorem finiteTopKernelRankHot51_epi_sum_le (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      FiniteTopKernelRankHot T (51/200) J),
      (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (Nat.factorial b : ℝ)^(m+Nat.card T) *
        ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ)) := by
  calc
    _ ≤ ∑ _J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
        FiniteTopKernelRankHot T (51/200) J), (Nat.factorial b : ℝ)^m := by
      apply Finset.sum_le_sum
      intro J _
      exact_mod_cast groupEpimorphism_card_le_factorial_pow J hQ
    _ = ((Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
        FiniteTopKernelRankHot T (51/200) J)).card : ℝ)*(Nat.factorial b : ℝ)^m := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ((Nat.factorial b : ℝ)^Nat.card T *
        ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ)))*(Nat.factorial b : ℝ)^m :=
      mul_le_mul_of_nonneg_right (finiteTopKernelRankHot51_card_le T b) (by positivity)
    _ = _ := by rw [pow_add]; ring
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
