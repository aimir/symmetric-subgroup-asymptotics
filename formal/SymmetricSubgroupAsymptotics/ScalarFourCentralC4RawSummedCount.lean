import SymmetricSubgroupAsymptotics.ScalarFourCentralC4ColdEnvelope
import SymmetricSubgroupAsymptotics.MarkedC4KernelHotCount

/-! The complete source sum for an actual central-repeat target. The hot
term keeps every epimorphism, and the cold term counts every finite top map. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

theorem raw_summed_count (hc : c≤3) (hd : d≤3)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b +
      (subgroupCount b : ℝ)*(D.coldCoefficient*(2 : ℝ)^(coldSlope*b)) := by
  classical
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop :=
    MarkedC4KernelHotCount.KernelHot T (51/200)
  have hh := MarkedC4KernelHotCount.kernel_hot_epi_sum_le T Q m hQ b
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
end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
