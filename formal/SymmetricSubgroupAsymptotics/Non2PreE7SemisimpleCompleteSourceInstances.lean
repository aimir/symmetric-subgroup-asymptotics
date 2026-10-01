import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceComparator
import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate

/-!
# Existing semisimple sources as direct complete-source certificates

The older semisimple source records already prove the joint outer-fibre
inequality.  These adapters route that proof through the direct complete
normal-axis certificate, so the outer factor is no longer repeated once for
every literal normal subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private theorem coefficient_le_axis_total
    {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w))) (c : ℝ) (hc : 0 ≤ c) :
    c ≤ fusionAxisEnvelopeTotal U (fun _ => c) := by
  unfold fusionAxisEnvelopeTotal
  let N : {N : Subgroup U // N.Normal} := ⟨⊥, inferInstance⟩
  simpa only using Finset.single_le_sum
    (f := fun _ : {N : Subgroup U // N.Normal} => c)
    (fun _ _ => hc) (Finset.mem_univ N)

/-- Convert an outer-comparator semisimple source without changing any of
its structural data. -/
noncomputable def PreE7SemisimpleOuterSourceData.completeNumericalData
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7SemisimpleOuterSourceData family w i)
    (parameters : PreE7CharacterEntryParameters preE7CharacterRho w
      D.v D.eta D.delta D.cutoff D.alpha D.theta) :
    PreE7CompleteSourceNumericalData family w i :=
  (show PreE7SemisimpleCompleteSourceData family w i from
    { E := D.E
      E_normal := D.E_normal
      chart := D.chart
      v := D.v
      action := D.action
      action_injective := D.action_injective
      coefficient := D.coefficient
      eta := D.eta
      delta := D.delta
      cutoff := D.cutoff
      alpha := D.alpha
      theta := D.theta
      alpha_eq := D.alpha_eq
      coefficient_nonneg := D.coefficient_nonneg
      parameters := parameters
      coefficient_bound := fun b =>
        (coefficient_le_axis_total (preE7NonPairAction w i)
          (D.coefficient b) (D.coefficient_nonneg b)).trans
            (D.coefficient_total_bound b)
      outer_bound := D.outer_bound }).numericalData

/-- Convert a direct semisimple source.  Its already-proved combined bound
is now used at the complete-source level. -/
noncomputable def PreE7SemisimpleDirectSourceData.completeNumericalData
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7SemisimpleDirectSourceData family w i)
    (parameters : PreE7CharacterEntryParameters preE7CharacterRho w
      D.v D.eta D.delta D.cutoff D.alpha D.theta) :
    PreE7CompleteSourceNumericalData family w i :=
  (show PreE7SemisimpleDirectCompleteSourceData family w i from
    { E := D.E
      E_normal := D.E_normal
      chart := D.chart
      v := D.v
      coefficient := D.coefficient
      eta := D.eta
      delta := D.delta
      cutoff := D.cutoff
      alpha := D.alpha
      theta := D.theta
      alpha_eq := D.alpha_eq
      coefficient_nonneg := D.coefficient_nonneg
      parameters := parameters
      coefficient_bound := fun b =>
        (coefficient_le_axis_total (preE7NonPairAction w i)
          (D.coefficient b) (D.coefficient_nonneg b)).trans
            (D.coefficient_total_bound b)
      combined_bound := D.combined_bound }).numericalData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
