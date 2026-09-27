import SymmetricSubgroupAsymptotics.OutsideOrbitTernaryChart
import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart
import SymmetricSubgroupAsymptotics.OrdinaryRemainderNaturality

/-!
# Physical installation of the residual C3 orbit

Every marked degree-three outside orbit is installed in one fixed
original-weight regular-`C₃` fusion family.  The whole complementary action
and the literal ordinary-remainder condition are retained.  This is the
physical bridge needed before splitting the local subgroup into its direct
axis and surviving-character branches.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-- Fixed physical labels for one ternary orbit and its full complement. -/
def c3OutsidePointEquiv (n : ℕ) (hn : 3 ≤ n) :
    TernaryCyclic ⊕ Fin (n-3) ≃ Fin n :=
  (Equiv.sumCongr ternaryFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

/-- The complete ordinary-remainder predicate on the fixed ternary chart. -/
def c3OutsideOrdinaryPredicate (n : ℕ) (hn : 3 ≤ n)
    (L : Subgroup (ternaryRegularAction × Equiv.Perm (Fin (n-3)))) : Prop :=
  ¬ IsCriticalSubgroup n
    (relabelSubgroup (c3OutsidePointEquiv n hn)
      (L.map (fusionOrbitAction ternaryRegularAction)))

theorem c3OutsideOrdinaryPredicate_natural (n : ℕ) (hn : 3 ≤ n) :
    FusionOrbitNatural ternaryRegularAction
      (c3OutsideOrdinaryPredicate n hn) :=
  fusionOrbitNatural_of_relabel_invariant ternaryRegularAction
    (c3OutsidePointEquiv n hn) (fun H => ¬ IsCriticalSubgroup n H)
    (fun e H => ordinaryRemainder_relabel_iff n e H)

/-- The one-orbit physical family on the fixed labels `Fin n`. -/
def C3OutsidePhysicalFamily (n : ℕ) (hn : 3 ≤ n) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  FusionRelabelledFamily (c3OutsidePointEquiv n hn)
    (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (c3OutsideOrdinaryPredicate n hn)))

/-- A literal marked outside orbit of degree three enters the fixed physical
family.  No point or chart multiplicity is charged in this membership
statement. -/
theorem outsideOrbit_degree_three_mem_physical {n : ℕ}
    (H : OrdinaryRemainderSubgroups n) (o : OutsideOrbit H.1)
    (hcard : Nat.card o.1.orbit = 3) :
    H.1 ∈ C3OutsidePhysicalFamily n (by
      have horbit : Nat.card o.1.orbit ≤ Nat.card (Fin n) :=
        Nat.card_le_card_of_injective
          (Subtype.val : o.1.orbit → Fin n) Subtype.val_injective
      simpa only [hcard,Nat.card_fin] using horbit) := by
  let hn : 3 ≤ n := by
    have horbit : Nat.card o.1.orbit ≤ Nat.card (Fin n) :=
      Nat.card_le_card_of_injective
        (Subtype.val : o.1.orbit → Fin n) Subtype.val_injective
    simpa only [hcard,Nat.card_fin] using horbit
  let hnlit : 3 ≤ n := hn
  obtain ⟨eO,heO⟩ := outsideOrbit_degree_three_ternary_chart H.1 o hcard
  have hsplit := PermutationCharacterRankSplit.card_split
    (FusionOrbitProfileChart.orbitSubaction H.1 o.1)
  have hcomp : Nat.card ↥((FusionOrbitProfileChart.orbitSubaction H.1 o.1)ᶜ) = n-3 := by
    change Nat.card o.1.orbit +
      Nat.card ↥((FusionOrbitProfileChart.orbitSubaction H.1 o.1)ᶜ) =
        Nat.card (Fin n) at hsplit
    rw [hcard,Nat.card_fin] at hsplit
    omega
  let eC : Fin (n-3) ≃
      ↥((FusionOrbitProfileChart.orbitSubaction H.1 o.1)ᶜ) :=
    (Finite.equivFinOfCardEq hcomp).symm
  let e := FusionOrbitProfileChart.chart H.1 o.1 eO eC
  let K : Subgroup (Equiv.Perm (TernaryCyclic ⊕ Fin (n-3))) :=
    relabelSubgroup e.symm H.1
  have hblock := FusionOrbitProfileChart.chart_preserves H.1 o.1 eO eC
  have hprojection := FusionOrbitProfileChart.chart_projection_eq
    H.1 o.1 ternaryRegularAction eO eC heO
  have hlocal : c3OutsideOrdinaryPredicate n hnlit
      (fusionDeletedModel ternaryRegularAction K) := by
    have hrec := fusionDeletedModel_recovers ternaryRegularAction K hblock hprojection
    unfold c3OutsideOrdinaryPredicate
    rw [hrec]
    change ¬ IsCriticalSubgroup n
      (relabelSubgroup (c3OutsidePointEquiv n hnlit)
        (relabelSubgroup e.symm H.1))
    rw [relabelSubgroup_trans]
    exact (ordinaryRemainder_relabel_iff n
      (e.symm.trans (c3OutsidePointEquiv n hnlit)) H.1).mpr H.2
  have hm : K ∈ FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (c3OutsideOrdinaryPredicate n hnlit)) :=
    fusionDeletedModel_mem_family ternaryRegularAction K hblock hprojection
      (c3OutsideOrdinaryPredicate n hnlit) hlocal
  have hr := fusionRelabelledFamily_of_chart
    (FusionOrbitModel ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (c3OutsideOrdinaryPredicate n hnlit)))
    e (c3OutsidePointEquiv n hnlit) K hm
  change H.1 ∈ C3OutsidePhysicalFamily n hnlit
  have he : relabelSubgroup e K = H.1 := by
    dsimp only [K]
    exact relabelSubgroup_symm e.symm H.1
  rw [← he]
  exact hr

end SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

end
