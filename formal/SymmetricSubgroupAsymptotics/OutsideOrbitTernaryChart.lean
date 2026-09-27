import SymmetricSubgroupAsymptotics.OutsideOrbitDegreeThree
import SymmetricSubgroupAsymptotics.C1PhysicalWeight

/-!
# The residual degree-three orbit in the c=1 model

The degree-three outside orbit is transported from its literal `A₃` chart
to the regular `C₃` action used by the surviving-character and
inverse-complement counting theorems.  No abstract group replacement is
made: the conclusion is equality of the relabelled permutation subgroups.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-- A fixed identification of the regular ternary point set with `Fin 3`. -/
def ternaryFinEquiv : TernaryCyclic ≃ Fin 3 :=
  Fintype.equivOfCardEq (by simp [TernaryCyclic])

/-- Under the fixed point identification, the regular `C₃` action is the
literal alternating subgroup of `S₃`. -/
theorem relabel_ternaryRegularAction_eq_alternating :
    relabelSubgroup ternaryFinEquiv ternaryRegularAction =
      alternatingGroup (Fin 3) := by
  let A : Subgroup (Equiv.Perm (Fin 3)) :=
    relabelSubgroup ternaryFinEquiv ternaryRegularAction
  have htrans0 : PermutationSubgroupTransitive ternaryRegularAction := by
    intro x y
    obtain ⟨g,hg⟩ := ternaryRegularAction_transitive x y
    exact ⟨g,g.property,hg⟩
  have htrans : PermutationSubgroupTransitive A :=
    permutationSubgroupTransitive_relabel ternaryFinEquiv ternaryRegularAction htrans0
  have hproper : A ≠ ⊤ := by
    intro htop
    have hcard : Nat.card A = Nat.card ternaryRegularAction := by
      dsimp [A,relabelSubgroup]
      exact Subgroup.card_map_of_injective ternaryFinEquiv.permCongrHom.injective
    rw [htop,Subgroup.card_top,ternaryRegularAction_card] at hcard
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hcard
  exact transitive_proper_degreeThree_eq_alternating A htrans hproper

/-- Every degree-three outside orbit has the exact regular `C₃` chart used
by the c=1 physical counting interfaces. -/
theorem outsideOrbit_degree_three_ternary_chart {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (o : OutsideOrbit H)
    (hcard : Nat.card o.1.orbit = 3) :
    ∃ e : TernaryCyclic ≃ o.1.orbit,
      relabelSubgroup e ternaryRegularAction =
        OrbitProfileFromOrbits.orbitImage H o.1 := by
  obtain ⟨e,he⟩ := outsideOrbit_degree_three_chart H o hcard
  refine ⟨ternaryFinEquiv.trans e, ?_⟩
  calc
    relabelSubgroup (ternaryFinEquiv.trans e) ternaryRegularAction =
        relabelSubgroup e (relabelSubgroup ternaryFinEquiv ternaryRegularAction) :=
      (relabelSubgroup_trans ternaryFinEquiv e ternaryRegularAction).symm
    _ = relabelSubgroup e (alternatingGroup (Fin 3)) := by
      rw [relabel_ternaryRegularAction_eq_alternating]
    _ = OrbitProfileFromOrbits.orbitImage H o.1 := he

end SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

end
