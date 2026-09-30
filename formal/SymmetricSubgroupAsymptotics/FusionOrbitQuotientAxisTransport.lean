import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeAxis
import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

/-!
# Transport from a quotient-orbit chart to the actual witness axis

An exact chart on a quotient orbit need not be the canonical chart attached
to a chosen point of that orbit.  This file chooses the matching complete
complement chart and transports the selected Goursat axis back to the actual
witness axis.  The statement is independent of any carrier menu.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.FusionOrbitQuotientAxisTransport

open SymmetricSubgroupAsymptotics
open FusionOrbitRepresentativeAxis

variable {n w : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin n)))
variable (x : Fin n)
variable (hw : Nat.card (MulAction.orbit H x) = w)

/-- Any exact chart on the quotient orbit of `x` admits a compatible complete
complement chart.  Under the induced equivalence of local action groups, its
selected deleted axis maps exactly to the actual witness axis. -/
theorem quotientLocalDeletedAxisTransport
    {o : OrbitProfileFromOrbits.Orbit H}
    (hpoint : (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H) = o)
    (eO : Fin w ≃ o.orbit)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H o) :
    ∃ (eC : Fin (n-w) ≃
        ↥((FusionOrbitProfileChart.orbitSubaction H o)ᶜ))
      (E : U ≃* FusionOrbitRepresentativeAxis.ActualAction H x hw),
      ((fusionDeletedModel U
          (relabelSubgroup
            (FusionOrbitProfileChart.chart H o eO eC).symm H)).goursatFst).map
            E.toMonoidHom =
        (FusionOrbitRepresentativeAxis.actualDeletedModel H x hw).goursatFst := by
  subst o
  let eC : Fin (n-w) ≃
      ↥((FusionOrbitProfileChart.orbitSubaction H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H))ᶜ) :=
    FusionActualOrbitCharts.complementEquiv H x hw
  let E : U ≃* FusionOrbitRepresentativeAxis.ActualAction H x hw :=
    (localActionEquiv H x hw eO U himage).symm
  refine ⟨eC,E,?_⟩
  have hchart :
      FusionOrbitProfileChart.chart H
          (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H) eO eC =
        FusionOrbitRepresentativeCharts.chart H x hw
          (chartConjugator H x hw eO) := by
    apply Equiv.ext
    intro z
    rcases z with z | z
    · change (eO z : Fin n) =
        FusionOrbitRepresentativeCharts.chart H x hw
          (chartConjugator H x hw eO) (Sum.inl z)
      exact (representativeChart_chartConjugator_inl H x hw eO z).symm
    · rfl
  rw [hchart]
  exact localDeletedAxis_map_symm_eq H x hw eO U himage

/-- Type-valued form of `quotientLocalDeletedAxisTransport`, suitable for
constructing a routed slot without eliminating an existential proof into
data. -/
structure TransportData
    {o : OrbitProfileFromOrbits.Orbit H}
    (eO : Fin w ≃ o.orbit)
    (U : Subgroup (Equiv.Perm (Fin w))) where
  eC : Fin (n-w) ≃
    ↥((FusionOrbitProfileChart.orbitSubaction H o)ᶜ)
  E : U ≃* FusionOrbitRepresentativeAxis.ActualAction H x hw
  axis_eq :
    ((fusionDeletedModel U
        (relabelSubgroup
          (FusionOrbitProfileChart.chart H o eO eC).symm H)).goursatFst).map
          E.toMonoidHom =
      (FusionOrbitRepresentativeAxis.actualDeletedModel H x hw).goursatFst

/-- The canonical transport data.  The complement chart and local-action
equivalence are the explicit ones used in
`quotientLocalDeletedAxisTransport`; no opaque choice is retained.  This is
auxiliary proof data and does not decorate the subgroup being counted. -/
def transportData
    {o : OrbitProfileFromOrbits.Orbit H}
    (hpoint : (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H) = o)
    (eO : Fin w ≃ o.orbit)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H o) :
    TransportData H x hw eO U := by
  subst o
  let eC : Fin (n-w) ≃
      ↥((FusionOrbitProfileChart.orbitSubaction H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H))ᶜ) :=
    FusionActualOrbitCharts.complementEquiv H x hw
  let E : U ≃* FusionOrbitRepresentativeAxis.ActualAction H x hw :=
    (localActionEquiv H x hw eO U himage).symm
  refine ⟨eC,E,?_⟩
  have hchart :
      FusionOrbitProfileChart.chart H
          (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H) eO eC =
        FusionOrbitRepresentativeCharts.chart H x hw
          (chartConjugator H x hw eO) := by
    apply Equiv.ext
    intro z
    rcases z with z | z
    · change (eO z : Fin n) =
        FusionOrbitRepresentativeCharts.chart H x hw
          (chartConjugator H x hw eO) (Sum.inl z)
      exact (representativeChart_chartConjugator_inl H x hw eO z).symm
    · rfl
  rw [hchart]
  exact localDeletedAxis_map_symm_eq H x hw eO U himage

end SymmetricSubgroupAsymptotics.FusionOrbitQuotientAxisTransport

end
