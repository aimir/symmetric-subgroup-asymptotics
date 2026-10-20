import SymmetricSubgroupAsymptotics.ScalarFourCentralColdEnvelope
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHotTail

/-! The complete source sum for an actual central-repeat target. The hot
term keeps every epimorphism, and the cold term counts every finite top map. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

theorem raw_summed_count (hc : c≤3) (hd : d≤3)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (Nat.factorial b : ℝ)^(m+Nat.card T) *
        ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ)) +
      (subgroupCount b : ℝ)*(D.coldCoefficient*(2 : ℝ)^(coldSlope*b)) := by
  classical
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop :=
    FiniteTopKernelRankHot T (51/200)
  have hh := finiteTopKernelRankHot51_epi_sum_le T Q m hQ b
  have hcold :
      (∑ J ∈ Finset.univ.filter (fun J => ¬hot J),
        (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (subgroupCount b : ℝ)*(D.coldCoefficient*(2 : ℝ)^(coldSlope*b)) := by
    calc
      _ ≤ ∑ _J ∈ Finset.univ.filter (fun J => ¬hot J),
          D.coldCoefficient*(2 : ℝ)^(coldSlope*b) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact D.cold_envelope hc hd f hf hZmud lit b J (Finset.mem_filter.mp hJ).2
      _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)),
          D.coldCoefficient*(2 : ℝ)^(coldSlope*b) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro J _ _
        unfold coldCoefficient
        positivity
      _ = _ := by simp [subgroupCount]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  exact add_le_add hh hcold
end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
