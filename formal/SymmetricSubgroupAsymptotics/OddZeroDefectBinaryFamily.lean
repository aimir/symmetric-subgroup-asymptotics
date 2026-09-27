import SymmetricSubgroupAsymptotics.NoncriticalBinaryOddSingleton
import SymmetricSubgroupAsymptotics.OddMarkerPairIntrinsicIncidence
import SymmetricSubgroupAsymptotics.OddMarkerBinaryErrorTransfer
import SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion

/-!
# The complete physical binary zero-defect family in odd degree

The singleton extension and natural `S_3` sectors are literal subgroup
families on the same labelled set.  The first has a global fixed point;
the second has none, so their images are disjoint.  Their exact physical
counts therefore add without a presentation multiplicity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.OddZeroDefectBinaryFamily

open BinaryFourPairIntrinsicTarget BinaryFourPairIntrinsicCoverage

abbrev SingletonSector (N : ℕ) := NoncriticalBinaryOddSingleton.Family N
abbrev NaturalSector (N : ℕ) :=
  OddMarkerPairIntrinsicIncidence.NaturalMarkerFamily N
abbrev SectorSum (N : ℕ) := SingletonSector N ⊕ NaturalSector N

local instance naturalSectorFinite (N : ℕ) : Finite (NaturalSector N) :=
  Finite.of_injective
    (fun H : NaturalSector N => (H.val : Set (Equiv.Perm (Fin (2*N+1)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

def subgroup (N : ℕ) :
    SectorSum N → Subgroup (Equiv.Perm (Fin (2*N+1)))
  | .inl H => H.val
  | .inr H => H.val

theorem natural_hasNoFixedPoints (N : ℕ) (H : NaturalSector N) :
    HasNoFixedPoints H.val := by
  obtain ⟨t,e,K,hK,hKH⟩ := H.property
  have h0 : OrbitProfileFullOn
      (OddMarkerPairModelEquiv.OddAction
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
        (OddMarkerPairIntrinsicIncidence.ExteriorAction N))
      (Equiv.refl _) K :=
    (orbitProfileFullOn_iff _ _ _).mpr hK
  have hOn : OrbitProfileFullOn
      (OddMarkerPairModelEquiv.OddAction
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
        (OddMarkerPairIntrinsicIncidence.ExteriorAction N)) e H.val := by
    rw [← hKH]
    simpa only [Equiv.refl_trans] using h0.relabel e
  apply hOn.hasNoFixedPoints
  intro i x
  cases i with
  | inl i =>
      cases i
      change Fin 3 at x
      letI : Nontrivial (Fin 3) := inferInstance
      obtain ⟨y,hy⟩ := exists_ne x
      obtain ⟨u,hu⟩ := oddMarker_transitive x y
      exact ⟨u,fun hx => hy (hu.symm.trans hx)⟩
  | inr i => exact fullAction_moves_point N i x

/-- The retained occupied noncritical residual orbit excludes every literal
member of the complete odd critical family. -/
theorem natural_ne_oddCritical (N : ℕ) (H : NaturalSector N)
    (J : OddCriticalSubgroups N) : H.val ≠ J.val := by
  obtain ⟨t,e,K,hK,hKH⟩ := H.property
  have h0 : OrbitProfileFullOn
      (OddMarkerPairModelEquiv.OddAction
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
        (OddMarkerPairIntrinsicIncidence.ExteriorAction N))
      (Equiv.refl _) K :=
    (orbitProfileFullOn_iff _ _ _).mpr hK
  have hOn : OrbitProfileFullOn
      (OddMarkerPairModelEquiv.OddAction
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
        (OddMarkerPairIntrinsicIncidence.ExteriorAction N)) e H.val := by
    rw [← hKH]
    simpa only [Equiv.refl_trans] using h0.relabel e
  obtain ⟨a,ha,hpos⟩ :=
    OddMarkerPairIntrinsicIncidence.selector_noncritical N t.val t.property
  let j : Fin (OddMarkerPairProfileUnion.oddMultiplicity t.val
      (.inr (.inr (.inr a)))) := ⟨0,hpos⟩
  let x : BinaryResidualOrbitMenu.points (2*N) a := Classical.choice inferInstance
  have htrans : ∀ i
      (x y : OddMarkerPairModelEquiv.OddPoints
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) i),
      ∃ u : OddMarkerPairModelEquiv.OddAction
          (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
          (OddMarkerPairIntrinsicIncidence.ExteriorAction N) i,
        (u : Equiv.Perm _) x = y :=
    RepeatedOddMarkerPhysicalProfile.action_transitive
      (OddMarkerPairModelEquiv.BasePoints
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N))
      (OddMarkerPairModelEquiv.BaseAction
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
        (OddMarkerPairIntrinsicIncidence.ExteriorAction N))
      (fullAction_transitive N)
  obtain ⟨o,c,hc⟩ := hOn.selected_orbit_image htrans
    (.inr (.inr (.inr a))) j x
  intro hHJ
  obtain ⟨q,d,L,hL,hLJ⟩ := J.property
  have hL0 : OrbitProfileFullOn oddCriticalActionSubgroup (Equiv.refl _) L :=
    (orbitProfileFullOn_iff _ _ _).mpr hL
  have hCrit : OrbitProfileFullOn oddCriticalActionSubgroup d H.val := by
    rw [hHJ,← hLJ]
    simpa only [Equiv.refl_trans] using hL0.relabel d
  obtain ⟨i,k,b,hb⟩ := hCrit.orbit_image_chart oddCriticalAction_transitive o
  cases i with
  | fixed =>
      have he : BinaryResidualOrbitMenu.points (2*N) a ≃ Fin 1 :=
        c.trans b.symm
      have hcard := Fintype.card_congr he
      have hgt : 2 < Fintype.card (BinaryResidualOrbitMenu.points (2*N) a) := a.1.2
      simp only [Fintype.card_fin] at hcard
      omega
  | marker =>
      have he : BinaryResidualOrbitMenu.points (2*N) a ≃ Fin 3 :=
        c.trans b.symm
      have hcard : Fintype.card (BinaryResidualOrbitMenu.points (2*N) a) = 3 := by
        simpa only [Fintype.card_fin] using Fintype.card_congr he
      have hne := RepeatedOddMarkerPhysicalBinary.exteriorDegree_ne_three
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))
        (BinaryResidualOrbitMenu.action_isPGroup (2*N))
        (BinaryResidualOrbitMenu.action_transitive (2*N)) a
      exact hne hcard
  | binary i =>
      change relabelSubgroup b (criticalActionSubgroup i) =
        OrbitProfileFromOrbits.orbitImage H.val o at hb
      apply ha
      refine ⟨i,b.trans c.symm,?_⟩
      calc
        relabelSubgroup (b.trans c.symm) (criticalActionSubgroup i) =
            relabelSubgroup c.symm
              (relabelSubgroup b (criticalActionSubgroup i)) :=
          (relabelSubgroup_trans b c.symm _).symm
        _ = relabelSubgroup c.symm
              (OrbitProfileFromOrbits.orbitImage H.val o) := by rw [hb]
        _ = BinaryResidualOrbitMenu.action (2*N) a := by
          rw [← hc]
          exact relabelSubgroup_symm c _

theorem subgroup_injective (N : ℕ) : Function.Injective (subgroup N) := by
  intro H K h
  cases H with
  | inl H =>
      cases K with
      | inl K =>
          exact congrArg Sum.inl (Subtype.ext h)
      | inr K =>
          exfalso
          change H.val = K.val at h
          obtain ⟨x,hx⟩ := SingletonExtension.finFamily_has_fixed_point
            (2*N) (fun H : NoncriticalBinarySubgroups N => H.val) H
          obtain ⟨g,hg⟩ := natural_hasNoFixedPoints N K x
          apply hg
          apply hx g.val
          rw [h]
          exact g.property
  | inr H =>
      cases K with
      | inl K =>
          exfalso
          change H.val = K.val at h
          obtain ⟨x,hx⟩ := SingletonExtension.finFamily_has_fixed_point
            (2*N) (fun H : NoncriticalBinarySubgroups N => H.val) K
          obtain ⟨g,hg⟩ := natural_hasNoFixedPoints N H x
          apply hg
          apply hx g.val
          rw [← h]
          exact g.property
      | inr K =>
          exact congrArg Sum.inr (Subtype.ext h)

/-- The literal union of the two zero-defect sectors, with duplicate
subgroups forgotten.  Injectivity above proves that nothing is lost. -/
abbrev Family (N : ℕ) := Set.range (subgroup N)

def sectorEquiv (N : ℕ) : SectorSum N ≃ Family N :=
  Equiv.ofInjective (subgroup N) (subgroup_injective N)

theorem card_eq (N : ℕ) :
    Nat.card (Family N) = Nat.card (SingletonSector N) + Nat.card (NaturalSector N) := by
  rw [← Nat.card_sum,Nat.card_congr (sectorEquiv N)]

/-- Exact complete physical binary zero-defect identity. -/
theorem normalized_card (N : ℕ) :
    (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) =
      MarkerZeroDefect.alpha N * binaryErrorRatio N +
        MarkerZeroDefect.beta N * BinaryPairMomentNormalized.pairErrorMomentRatio N := by
  rw [card_eq,Nat.cast_add,add_div,
    NoncriticalBinaryOddSingleton.normalized_card,
    OddMarkerPairIntrinsicIncidence.normalized_card]

/-- The completed numerical zero-defect row, now attached to the actual
two-sector physical family. -/
theorem normalized_card_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) ≤
      OddMarkerBinaryErrorTransfer.currentCoefficient N * binaryErrorRatio N +
        OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient N *
          binaryErrorRatio (N-1) := by
  rw [normalized_card]
  exact OddMarkerBinaryErrorTransfer.binary_error_transfer N hN

end SymmetricSubgroupAsymptotics.OddZeroDefectBinaryFamily

end
