import SymmetricSubgroupAsymptotics.ScalarFourCentralColdTwoCount
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHotTail

/-! The complete source sum for an actual central-repeat target. The hot
term keeps every epimorphism, and the cold term counts every finite top map. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}

theorem raw_summed_count_of_cold
    (A theta : ℝ) (hA : 0≤A)
    (hCold : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      ¬FiniteTopKernelRankHot T (51/200) J →
      (Nat.card (GroupEpimorphism J Q) : ℝ)≤A*(2 : ℝ)^(theta*b))
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (Nat.factorial b : ℝ)^(m+Nat.card T) *
        ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ)) +
      (subgroupCount b : ℝ)*(A*(2 : ℝ)^(theta*b)) := by
  classical
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop :=
    FiniteTopKernelRankHot T (51/200)
  have hh := finiteTopKernelRankHot51_epi_sum_le T Q m hQ b
  have hcold :
      (∑ J ∈ Finset.univ.filter (fun J => ¬hot J),
        (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (subgroupCount b : ℝ)*(A*(2 : ℝ)^(theta*b)) := by
    calc
      _ ≤ ∑ _J ∈ Finset.univ.filter (fun J => ¬hot J),
          A*(2 : ℝ)^(theta*b) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact hCold b J (Finset.mem_filter.mp hJ).2
      _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)),
          A*(2 : ℝ)^(theta*b) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro J _ _
        positivity
      _ = _ := by simp [subgroupCount]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  exact add_le_add hh hcold

theorem raw_summed_count_two (D : ScalarFourCentralTopCoordinates Q T c d)
    (hc : c≤2) (hd : d≤2)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (Nat.factorial b : ℝ)^(m+Nat.card T) *
        ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ)) +
      (subgroupCount b : ℝ)*(D.coldCoefficient*(2 : ℝ)^(coldSlopeTwo*b)) := by
  exact raw_summed_count_of_cold (T := T) D.coldCoefficient coldSlopeTwo
    (by unfold coldCoefficient; positivity)
    (fun b J hJ => D.cold_envelope_two hc hd f hf hZmud lit b J hJ) m hQ b
end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
