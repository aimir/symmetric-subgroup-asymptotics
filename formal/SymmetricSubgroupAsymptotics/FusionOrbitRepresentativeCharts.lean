import SymmetricSubgroupAsymptotics.FusionActualOrbitCharts
import SymmetricSubgroupAsymptotics.BinaryTransitiveActionClasses

/-!
# Original orbit charts at a chosen action representative

Only the labels on the selected original orbit are changed. Both restriction
coordinates still come from the same original element, so the complementary
action and every correlation with it remain in the deleted subgroup. Action
classes, rather than all conjugating charts, index the resulting cover.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts

open FusionActualOrbitCharts

variable {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = w) (c : Equiv.Perm (Fin w))

/-- Reindex only the first block by the actual ambient conjugator. -/
def chart : Fin w ⊕ Fin (n-w) ≃ Fin n :=
  (Equiv.sumCongr c.symm (Equiv.refl (Fin (n-w)))).trans
    (FusionActualOrbitCharts.chart H x hw)

def pairHom : H →* Equiv.Perm (Fin w) × Equiv.Perm (Fin (n-w)) :=
  (c.permCongrHom.toMonoidHom.comp (firstHom H x hw)).prod (secondHom H x hw)

/-- The same original element acts in both coordinates after reindexing. -/
theorem chart_pairHom_apply (g : H) (z : Fin w ⊕ Fin (n-w)) :
    chart H x hw c (Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w))
      (pairHom H x hw c g) z) =
        (g : Equiv.Perm (Fin n)) (chart H x hw c z) := by
  rcases z with i | i
  · change FusionActualOrbitCharts.chart H x hw
      (Sum.inl (c.symm (c (firstHom H x hw g (c.symm i))))) = _
    rw [Equiv.symm_apply_apply]
    exact FusionActualOrbitCharts.chart_pairHom_apply H x hw g (Sum.inl (c.symm i))
  · exact FusionActualOrbitCharts.chart_pairHom_apply H x hw g (Sum.inr i)

theorem chart_conjugate_pair (g : H) :
    (chart H x hw c).symm.permCongr (g : Equiv.Perm (Fin n)) =
      Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw c g) := by
  apply Equiv.ext
  intro z
  apply (chart H x hw c).injective
  change chart H x hw c ((chart H x hw c).symm
    ((g : Equiv.Perm (Fin n)) (chart H x hw c z))) = _
  rw [Equiv.apply_symm_apply]
  exact (chart_pairHom_apply H x hw c g z).symm

theorem chart_preserves :
    ∀ k ∈ relabelSubgroup (chart H x hw c).symm H,
      Set.MapsTo k (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w)))
        (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w))) := by
  intro k hk
  change k ∈ H.map (chart H x hw c).symm.permCongrHom.toMonoidHom at hk
  obtain ⟨g,hg,rfl⟩ := hk
  rw [show (chart H x hw c).symm.permCongrHom.toMonoidHom g =
      Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw c ⟨g,hg⟩)
    from chart_conjugate_pair H x hw c ⟨g,hg⟩]
  rintro _ ⟨i,rfl⟩
  exact ⟨c (firstHom H x hw ⟨g,hg⟩ (c.symm i)),rfl⟩

theorem blockPullback_eq_range :
    fusionPhysicalBlockPullback (relabelSubgroup (chart H x hw c).symm H) =
      (pairHom H x hw c).range := by
  ext p
  constructor
  · intro hp
    change Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) p ∈
      H.map (chart H x hw c).symm.permCongrHom.toMonoidHom at hp
    obtain ⟨g,hg,he⟩ := hp
    refine ⟨⟨g,hg⟩,?_⟩
    apply Equiv.Perm.sumCongrHom_injective
    exact (chart_conjugate_pair H x hw c ⟨g,hg⟩).symm.trans he
  · rintro ⟨g,rfl⟩
    change Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw c g) ∈
      H.map (chart H x hw c).symm.permCongrHom.toMonoidHom
    exact ⟨g,g.property,chart_conjugate_pair H x hw c g⟩

/-- Literal first projection, conjugated by an original permutation. -/
theorem projection_eq :
    (fusionPhysicalBlockPullback (relabelSubgroup (chart H x hw c).symm H)).map
      (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w)))) =
        MulAut.conj c • FusionActualOrbitCharts.chartAction H x hw := by
  rw [blockPullback_eq_range, MonoidHom.map_range]
  change (c.permCongrHom.toMonoidHom.comp (firstHom H x hw)).range = _
  rw [MonoidHom.range_comp, FusionActualOrbitCharts.chartAction_eq_range]
  rw [Subgroup.pointwise_smul_def]
  congr 1

/-- Relabelling the orbit does not alter the actual set of orbit points. -/
theorem chart_first_range :
    Set.range (fun i : Fin w => chart H x hw c (Sum.inl i)) = MulAction.orbit H x := by
  rw [← FusionActualOrbitCharts.chart_first_range H x hw]
  ext y
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨c.symm i,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨c i,?_⟩
    change FusionActualOrbitCharts.chart H x hw (Sum.inl (c.symm (c i))) = _
    rw [Equiv.symm_apply_apply]

/-- Every actual binary orbit enters one chosen original action family.
This is an unmarked cover; no point or chart is counted as an extra label. -/
theorem exists_canonicalFamily {h : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = 2*h)
    (hP : IsPGroup 2 (orbitImage H x)) (hn : 2*h ≤ n) :
    ∃ i : BinaryTransitiveActionClass (Fin (2*h)),
      H ∈ FusionCanonicalFamily i.representative hn (fun _ => True) := by
  obtain ⟨i,c,hc⟩ := BinaryTransitiveActionClass.representative_cover
    (FusionActualOrbitCharts.chartAction H x hw)
    (chartAction_isPGroup H x hw 2 hP) (chartAction_transitive H x hw)
  refine ⟨i, fusionCanonicalFamily_of_chart i.representative hn H
    (chart H x hw c) (chart_preserves H x hw c) ?_ (fun _ => True) trivial⟩
  exact (projection_eq H x hw c).trans hc

end SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts

end
