import SymmetricSubgroupAsymptotics.NoncriticalBinaryOddSingleton
import SymmetricSubgroupAsymptotics.OddMarkerPairIntrinsicIncidence
import SymmetricSubgroupAsymptotics.OddMarkerBinaryErrorTransfer
import SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion
import SymmetricSubgroupAsymptotics.SingletonExtensionOrbits
import SymmetricSubgroupAsymptotics.PGroupTransitiveDegree
import SymmetricSubgroupAsymptotics.OddCriticalLiteral

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

/-- Adding the singleton preserves the source's noncritical moving orbit
and its exact restriction image.  That orbit cannot become the singleton,
the natural `S_3` action, or one of the four critical binary actions. -/
theorem singleton_ne_oddCritical (N : ℕ) (H : SingletonSector N)
    (J : OddCriticalSubgroups N) : H.val ≠ J.val := by
  obtain ⟨x,K,hKH⟩ := H.property
  obtain ⟨o,ho⟩ :=
    (CriticalOrbitCriterion.not_isEvenCritical_iff N K.val).mp K.property.2
  let e : Fin (2*N+1) ≃ Option (Fin (2*N)) := finSuccEquiv' x
  let O := SingletonExtension.extendedOrbit e K.val o
  obtain ⟨q,d,L,hL,hLJ⟩ := J.property
  have hL0 : OrbitProfileFullOn oddCriticalActionSubgroup (Equiv.refl _) L :=
    (orbitProfileFullOn_iff _ _ _).mpr hL
  intro hHJ
  have hCrit : OrbitProfileFullOn oddCriticalActionSubgroup d
      (K.val.map (SingletonExtension.extensionHom e)) := by
    rw [hKH,hHJ,← hLJ]
    simpa only [Equiv.refl_trans] using hL0.relabel d
  obtain ⟨i,j,c,hc⟩ := hCrit.orbit_image_chart oddCriticalAction_transitive O
  let φ := SingletonExtension.orbitEquiv e K.val o
  cases i with
  | fixed =>
      have he : o.orbit ≃ Fin 1 := φ.trans c.symm
      have hcard : Nat.card o.orbit = 1 := by
        simpa only [Nat.card_fin] using Nat.card_congr he
      exact BinaryFourPairIntrinsicCoverage.orbit_card_ne_one N K o hcard
  | marker =>
      have he : o.orbit ≃ Fin 3 := φ.trans c.symm
      have hcard : Nat.card o.orbit = 3 := by
        simpa only [Nat.card_fin] using Nat.card_congr he
      let z : o.orbit := ⟨o.out,by
        rw [o.orbit_eq_orbit_out Quotient.out_eq']
        exact MulAction.mem_orbit_self o.out⟩
      have hne : Nat.card o.orbit ≠ 3 :=
        binary_transitive_degree_ne_three K.property.1.1 z
          (fun y => MulAction.exists_smul_eq K.val z y)
      exact hne hcard
  | binary i =>
      apply ho
      have hc' : relabelSubgroup c (criticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage
            (K.val.map (SingletonExtension.extensionHom e)) O := hc
      refine ⟨i,c.trans φ.symm,?_⟩
      calc
        relabelSubgroup (c.trans φ.symm) (criticalActionSubgroup i) =
            relabelSubgroup φ.symm
              (relabelSubgroup c (criticalActionSubgroup i)) :=
          (relabelSubgroup_trans c φ.symm _).symm
        _ = relabelSubgroup φ.symm
              (OrbitProfileFromOrbits.orbitImage
                (K.val.map (SingletonExtension.extensionHom e)) O) := by rw [hc']
        _ = OrbitProfileFromOrbits.orbitImage K.val o := by
          rw [← SingletonExtension.relabel_orbitImage e K.val o]
          exact relabelSubgroup_symm φ _

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

/-- Both zero-defect sectors lie in the literal complement of the complete
odd critical family. -/
theorem subgroup_notCritical (N : ℕ) (H : SectorSum N) :
    ¬ IsCriticalSubgroup (2*N+1) (subgroup N H) := by
  intro hcrit
  obtain ⟨J,hJ⟩ := (isCriticalSubgroup_odd_iff N (subgroup N H)).mp hcrit
  cases H with
  | inl H => exact singleton_ne_oddCritical N H J hJ.symm
  | inr H => exact natural_ne_oddCritical N H J hJ.symm

/-- The literal union of the two zero-defect sectors, with duplicate
subgroups forgotten.  Injectivity above proves that nothing is lost. -/
abbrev Family (N : ℕ) := Set.range (subgroup N)

def sectorEquiv (N : ℕ) : SectorSum N ≃ Family N :=
  Equiv.ofInjective (subgroup N) (subgroup_injective N)

/-- The completed physical family embeds without multiplicity into the
actual ordinary remainder used by T1. -/
def ordinaryRemainderEmbedding (N : ℕ) :
    Family N ↪ OrdinaryRemainderSubgroups (2*N+1) where
  toFun H := ⟨H.val,by
    obtain ⟨S,hS⟩ := H.property
    rw [← hS]
    exact subgroup_notCritical N S⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg
      (fun L : OrdinaryRemainderSubgroups (2*N+1) => L.val) h

theorem card_le_ordinaryRemainder (N : ℕ) :
    Nat.card (Family N) ≤ Nat.card (OrdinaryRemainderSubgroups (2*N+1)) :=
  Nat.card_le_card_of_injective (ordinaryRemainderEmbedding N)
    (ordinaryRemainderEmbedding N).injective

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

theorem normalized_card_le_ordinaryRemainderRatio (N : ℕ) :
    (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) ≤
      ordinaryRemainderRatio (2*N+1) := by
  unfold ordinaryRemainderRatio
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast card_le_ordinaryRemainder N)
    (exactBenchmark_pos _).le

end SymmetricSubgroupAsymptotics.OddZeroDefectBinaryFamily

end
