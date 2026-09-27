import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly
import SymmetricSubgroupAsymptotics.OrbitProfileOrbitCriterion

/-!
# A necessary original-orbit criterion for odd criticality

Every subgroup in the complete odd critical family has, on each literal
orbit, one of the six original odd critical actions: the singleton, the
natural `S_3` action, or one of the four binary critical actions.  This is
the forward criterion needed to exclude a retained noncritical residual
orbit from the odd critical family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion

theorem orbit_image {N : ℕ} (H : OddCriticalSubgroups N)
    (o : OrbitProfileFromOrbits.Orbit H.val) :
    ∃ i : OddCriticalActionKind,
      ∃ e : oddCriticalActionPoints i ≃ o.orbit,
        relabelSubgroup e (oddCriticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage H.val o := by
  obtain ⟨p,e,L,hL,hLK⟩ := H.property
  have h0 : OrbitProfileFullOn oddCriticalActionSubgroup (Equiv.refl _) L :=
    (orbitProfileFullOn_iff _ _ _).mpr hL
  have hOn : OrbitProfileFullOn oddCriticalActionSubgroup e H.val := by
    rw [← hLK]
    simpa only [Equiv.refl_trans] using h0.relabel e
  obtain ⟨i,j,c,hc⟩ := hOn.orbit_image_chart oddCriticalAction_transitive o
  exact ⟨i,c,hc⟩

end SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion

end
