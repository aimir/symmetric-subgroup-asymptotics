import SymmetricSubgroupAsymptotics.BinaryS16DirectCertifiedOrbitProfile
import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitAxisBridge
import SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedRetention

/-!
# Joint S16 orbit data from one certified choice

The point action, orbit chart, numerical parameter and routed carrier seed must
all come from the same orbit certificate.  Choosing those components in
separate functions would permit a proof-irrelevant colour witness to disagree
with the Type-valued routed slot.  Here the literal orbit quotient itself is
the label type, and every component is projected from the single direct
certificate chosen in `BinaryS16DirectCertifiedOrbitProfile.profile`.

The resulting `OrbitProfileFromOrbits.Data` has singleton label fibres.  Its
parameter sum is exactly the ambient half-degree, while its direct old-support
sum is the literal sum attached to these same certificates.  The final local
geometric obligation is isolated as `AxisRouting`: transport the route stored
by the same certificate to the canonical product axis of its occurrence.

This direct old-support function is intentionally kept distinct from the
older `checkedProfile` support.  They arise from two different classical
choices; using the older fixed-support partition therefore still requires an
explicit equality theorem, or else that partition should be rebuilt from the
direct support below.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryS16JointOrbitData

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierCertifiedRetention
open BinaryCarrierRetentionNumerics
open BinaryS16CanonicalCarrierProfile
open BinaryS16DirectCertifiedOrbitProfile

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

/-! ## Exact charts transported with their orbit index -/

/-- A point action together with its exact chart onto one literal orbit. -/
structure ExactOrbitChart (o : Orbit H) (P : Type)
    (U : Subgroup (Equiv.Perm P)) where
  pointEquiv : P ≃ o.orbit
  image_eq : relabelSubgroup pointEquiv U =
    OrbitProfileFromOrbits.orbitImage H o

/-- Transport an exact chart along equality of quotient orbits. -/
def ExactOrbitChart.transport
    {q o : Orbit H} {P : Type} {U : Subgroup (Equiv.Perm P)}
    (h : q = o) (C : ExactOrbitChart H q P U) :
    ExactOrbitChart H o P U := by
  subst o
  exact C

/-- The selected physical witness action is exactly the restriction image on
its own quotient orbit. -/
theorem smallWitness_image_eq
    {w : ℕ} (W : SmallOrbitWitness w H) :
    relabelSubgroup
        (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card)
        W.action =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' W.point : Orbit H) := by
  let c := FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card
  change relabelSubgroup c
      (FusionActualOrbitCharts.chartAction H W.point W.orbit_card) = _
  rw [FusionActualOrbitCharts.chartAction_eq_map]
  exact relabelSubgroup_symm c.symm _

/-- The same exact chart for a degree-eight physical witness. -/
theorem witnessEight_image_eq
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H) :
    relabelSubgroup
        (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card)
        W.action =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' W.point : Orbit H) := by
  change relabelSubgroup
      (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card)
      (FusionActualOrbitCharts.chartAction H W.point W.orbit_card) = _
  rw [FusionActualOrbitCharts.chartAction_eq_map]
  exact relabelSubgroup_symm
    (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card).symm _

/-- The same exact chart for a degree-sixteen physical witness. -/
theorem witnessSixteen_image_eq
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H) :
    relabelSubgroup
        (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card)
        W.action =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' W.point : Orbit H) := by
  change relabelSubgroup
      (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card)
      (FusionActualOrbitCharts.chartAction H W.point W.orbit_card) = _
  rw [FusionActualOrbitCharts.chartAction_eq_map]
  exact relabelSubgroup_symm
    (FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card).symm _

/-! ## One joint local model per literal orbit -/

/-- The local point type, action and exact orbit chart extracted in one match
from one Type-valued certificate. -/
structure LocalModel (o : Orbit H) where
  Points : Type
  pointsFintype : Fintype Points
  action : Subgroup (Equiv.Perm Points)
  chart : ExactOrbitChart H o Points action

/-- Construct the local action model without making another choice. -/
def certificateLocalModel {o : Orbit H}
    (C : OrbitCertificate H o) : LocalModel H o := by
  cases C with
  | c2 e he =>
      exact { Points := criticalActionPoints .c2
              pointsFintype := inferInstance
              action := criticalActionSubgroup .c2
              chart := ⟨e,he⟩ }
  | v4 e he =>
      exact { Points := criticalActionPoints .v4
              pointsFintype := inferInstance
              action := criticalActionSubgroup .v4
              chart := ⟨e,he⟩ }
  | d8 e he =>
      exact { Points := criticalActionPoints .d8
              pointsFintype := inferInstance
              action := criticalActionSubgroup .d8
              chart := ⟨e,he⟩ }
  | e8 e he =>
      exact { Points := criticalActionPoints .e8
              pointsFintype := inferInstance
              action := criticalActionSubgroup .e8
              chart := ⟨e,he⟩ }
  | cyclicFour W hpoint _ =>
      exact { Points := Fin 4
              pointsFintype := inferInstance
              action := W.action
              chart := (ExactOrbitChart.transport H hpoint
                ⟨FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card,
                  smallWitness_image_eq H W⟩) }
  | carrier8 W hpoint _ =>
      exact { Points := Fin 8
              pointsFintype := inferInstance
              action := W.action
              chart := (ExactOrbitChart.transport H hpoint
                ⟨FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card,
                  witnessEight_image_eq H W⟩) }
  | carrier16 W hpoint _ =>
      exact { Points := Fin 16
              pointsFintype := inferInstance
              action := W.action
              chart := (ExactOrbitChart.transport H hpoint
                ⟨FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card,
                  witnessSixteen_image_eq H W⟩) }

variable (hH : ResidualSector H)

include hH in
/-- The single local model selected by the single direct certificate. -/
def localModel (o : Orbit H) : LocalModel H o :=
  certificateLocalModel H
    (BinaryS16DirectCertifiedOrbitProfile.profile H hH o)

include hH in
abbrev Points (o : Orbit H) : Type := (localModel H hH o).Points

include hH in
instance pointsFintype (o : Orbit H) : Fintype (Points H hH o) :=
  (localModel H hH o).pointsFintype

include hH in
def action (o : Orbit H) : Subgroup (Equiv.Perm (Points H hH o)) :=
  (localModel H hH o).action

include hH in
/-- The simultaneous orbit data uses the literal quotient orbit as its own
  label.  Hence no second colour/profile choice is present. -/
def data : OrbitProfileFromOrbits.Data H (action H hH) where
  label := fun o ↦ o
  pointEquiv := fun o ↦ (localModel H hH o).chart.pointEquiv
  image_eq := fun o ↦ (localModel H hH o).chart.image_eq

/-! ## Numerical functions from the same certificate -/

def certificateParameter {o : Orbit H} : OrbitCertificate H o → ℕ
  | .c2 _ _ => 1
  | .v4 _ _ => 2
  | .d8 _ _ => 2
  | .e8 _ _ => 4
  | .cyclicFour _ _ _ => 2
  | .carrier8 _ _ _ => 4
  | .carrier16 _ _ _ => 8

def certificateOldSupport {o : Orbit H} : OrbitCertificate H o → ℕ
  | .c2 _ _ | .v4 _ _ | .d8 _ _ | .e8 _ _ => 0
  | .cyclicFour _ _ _ => 2
  | .carrier8 _ _ _ => 4
  | .carrier16 _ _ _ => 8

include hH in
def parameter (o : Orbit H) : ℕ :=
  certificateParameter H
    (BinaryS16DirectCertifiedOrbitProfile.profile H hH o)

include hH in
def oldSupportAt (o : Orbit H) : ℕ :=
  certificateOldSupport H
    (BinaryS16DirectCertifiedOrbitProfile.profile H hH o)

include hH in
def oldSupport : ℕ := ∑ o : Orbit H, oldSupportAt H hH o

include hH in
/-- Positivity stated directly for the same Type-valued profile used by the
  joint action and route data. -/
def HasPositiveOrbit : Prop :=
  ∃ o : Orbit H, 0 < oldSupportAt H hH o

/-- The direct positive-orbit predicate is exactly positivity of the direct
old-support sum. -/
theorem hasPositiveOrbit_iff_oldSupport_pos :
    HasPositiveOrbit H hH ↔ 0 < oldSupport H hH := by
  constructor
  · rintro ⟨o,ho⟩
    unfold oldSupport
    apply Finset.sum_pos'
    · intro i hi
      exact Nat.zero_le _
    · exact ⟨o,Finset.mem_univ o,ho⟩
  · intro hsum
    by_contra hpositive
    have hz : ∀ o : Orbit H, oldSupportAt H hH o = 0 := by
      intro o
      apply Nat.eq_zero_of_not_pos
      intro ho
      exact hpositive ⟨o,ho⟩
    have : oldSupport H hH = 0 := by
      unfold oldSupport
      apply Finset.sum_eq_zero
      intro o ho
      exact hz o
    omega

/-- With the direct profile, the zero-support alternative already supplies
literal critical charts on every orbit.  This is the direct replacement for
the older checked-profile ownership dichotomy. -/
theorem hasPositiveOrbit_or_allCritical :
    HasPositiveOrbit H hH ∨ CriticalOrbitCriterion.AllCriticalOrbits H := by
  by_cases hp : HasPositiveOrbit H hH
  · exact Or.inl hp
  · right
    intro o
    generalize hC :
      BinaryS16DirectCertifiedOrbitProfile.profile H hH o = C
    have hn : ¬ 0 < certificateOldSupport H C := by
      intro ho
      apply hp
      refine ⟨o,?_⟩
      unfold oldSupportAt
      rw [hC]
      exact ho
    change ∃ i : CriticalActionKind,
      ∃ e : criticalActionPoints i ≃ o.orbit,
        relabelSubgroup e (criticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage H o
    cases C with
    | c2 e he => exact ⟨.c2,e,he⟩
    | v4 e he => exact ⟨.v4,e,he⟩
    | d8 e he => exact ⟨.d8,e,he⟩
    | e8 e he => exact ⟨.e8,e,he⟩
    | cyclicFour W hpoint S =>
        exact False.elim (hn (by simp [certificateOldSupport]))
    | carrier8 W hpoint S =>
        exact False.elim (hn (by simp [certificateOldSupport]))
    | carrier16 W hpoint S =>
        exact False.elim (hn (by simp [certificateOldSupport]))

/-- Even-degree form of the direct ownership dichotomy. -/
theorem hasPositiveOrbit_or_isEvenCritical {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : ResidualSector H) :
    HasPositiveOrbit H hH ∨ IsEvenCriticalSubgroup N H := by
  rcases hasPositiveOrbit_or_allCritical H hH with hp | hc
  · exact Or.inl hp
  · exact Or.inr ((CriticalOrbitCriterion.isEvenCritical_iff N H).2 hc)

/-- Each local parameter is exactly half the size of its literal orbit. -/
theorem two_mul_parameter_eq_orbit_card (o : Orbit H) :
    2 * parameter H hH o = Nat.card o.orbit := by
  let C := BinaryS16DirectCertifiedOrbitProfile.profile H hH o
  change 2 * certificateParameter H C = Nat.card o.orbit
  cases C with
  | c2 e he =>
      rw [← Nat.card_congr e]
      norm_num [certificateParameter, criticalActionDegree,
        Nat.card_eq_fintype_card,
        criticalAction_point_card]
  | v4 e he =>
      rw [← Nat.card_congr e]
      norm_num [certificateParameter, criticalActionDegree,
        Nat.card_eq_fintype_card,
        criticalAction_point_card]
  | d8 e he =>
      rw [← Nat.card_congr e]
      norm_num [certificateParameter, criticalActionDegree,
        Nat.card_eq_fintype_card,
        criticalAction_point_card]
  | e8 e he =>
      rw [← Nat.card_congr e]
      norm_num [certificateParameter, criticalActionDegree,
        Nat.card_eq_fintype_card,
        criticalAction_point_card]
  | cyclicFour W hpoint S =>
      have hc := congrArg (fun q : Orbit H ↦ Nat.card q.orbit) hpoint
      have hmk : Nat.card
          (MulAction.orbitRel.Quotient.orbit
            (Quotient.mk'' W.point : Orbit H)) = 4 := by
        simpa only [MulAction.orbitRel.Quotient.orbit_mk] using W.orbit_card
      have ho : Nat.card o.orbit = 4 := hc.symm.trans hmk
      simpa [certificateParameter] using ho.symm
  | carrier8 W hpoint S =>
      have hc := congrArg (fun q : Orbit H ↦ Nat.card q.orbit) hpoint
      have hmk : Nat.card
          (MulAction.orbitRel.Quotient.orbit
            (Quotient.mk'' W.point : Orbit H)) = 8 := by
        simpa only [MulAction.orbitRel.Quotient.orbit_mk] using W.orbit_card
      have ho : Nat.card o.orbit = 8 := hc.symm.trans hmk
      simpa [certificateParameter] using ho.symm
  | carrier16 W hpoint S =>
      have hc := congrArg (fun q : Orbit H ↦ Nat.card q.orbit) hpoint
      have hmk : Nat.card
          (MulAction.orbitRel.Quotient.orbit
            (Quotient.mk'' W.point : Orbit H)) = 16 := by
        simpa only [MulAction.orbitRel.Quotient.orbit_mk] using W.orbit_card
      have ho : Nat.card o.orbit = 16 := hc.symm.trans hmk
      simpa [certificateParameter] using ho.symm

/-! ## Singleton multiplicities and exact sums -/

/-- Each literal orbit labels itself, so every label fibre is a singleton. -/
def fiberEquivPUnit (o : Orbit H) :
    (data H hH).Fiber o ≃ PUnit.{1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ ⟨o,rfl⟩
  left_inv := by
    intro q
    apply Subtype.ext
    simpa [data] using q.property.symm
  right_inv := by
    intro q
    cases q
    rfl

@[simp] theorem multiplicity_eq_one (o : Orbit H) :
    (data H hH).multiplicity o = 1 := by
  exact (Fintype.card_congr (fiberEquivPUnit H hH o)).trans
    (by simp)

/-- The sole occurrence of a literal-orbit label is that same orbit.  This is
the equality used to align a certificate's retained `W` and `hpoint` with the
occurrence seen by the canonical word. -/
@[simp] theorem orbitIndex_eq_fst
    (q : Σ o, Fin ((data H hH).multiplicity o)) :
    (data H hH).orbitIndex q = q.1 := by
  change ((data H hH).occurrence q.1 q.2).1 = q.1
  simpa [data] using ((data H hH).occurrence q.1 q.2).2

/-- For an action on `Fin (2*N)`, the exact parameter sum is `N`. -/
theorem parameter_sum {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : ResidualSector H) :
    ∑ o : Orbit H, parameter H hH o = N := by
  have horbits :
      (∑ o : Orbit H, Nat.card o.orbit) = Nat.card (Fin (2 * N)) := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr
      (MulAction.selfEquivSigmaOrbits' H (Fin (2 * N))).symm
  have hdouble : 2 * (∑ o : Orbit H, parameter H hH o) = 2 * N := by
    calc
      2 * (∑ o : Orbit H, parameter H hH o) =
          ∑ o : Orbit H, 2 * parameter H hH o := by
        rw [Finset.mul_sum]
      _ = ∑ o : Orbit H, Nat.card o.orbit := by
        apply Finset.sum_congr rfl
        intro o ho
        exact two_mul_parameter_eq_orbit_card H hH o
      _ = Nat.card (Fin (2 * N)) := horbits
      _ = 2 * N := by simp
  omega

/-- The grouped profile multiplicity sum has the same exact parameter. -/
theorem multiplicity_parameter_sum {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : ResidualSector H) :
    ∑ o : Orbit H, (data H hH).multiplicity o * parameter H hH o = N := by
  simpa using parameter_sum H hH

/-- The grouped profile multiplicity sum has exactly the canonical old
support selected by the same Type-valued profile. -/
theorem multiplicity_oldSupport_sum :
    ∑ o : Orbit H, (data H hH).multiplicity o * oldSupportAt H hH o =
      oldSupport H hH := by
  simp [oldSupport]

/-- Equivalently, summing over literal occurrences gives the exact ambient
half-degree. -/
theorem occurrence_parameter_sum {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : ResidualSector H) :
    ∑ q : Σ o, Fin ((data H hH).multiplicity o), parameter H hH q.1 = N := by
  rw [Fintype.sum_sigma]
  simpa [Finset.sum_const, nsmul_eq_mul] using
    multiplicity_parameter_sum H hH

/-- The corresponding literal-occurrence old-support sum is exact as well. -/
theorem occurrence_oldSupport_sum :
    ∑ q : Σ o, Fin ((data H hH).multiplicity o), oldSupportAt H hH q.1 =
      oldSupport H hH := by
  rw [Fintype.sum_sigma]
  simpa [Finset.sum_const, nsmul_eq_mul] using
    multiplicity_oldSupport_sum H hH

/-- The direct old support never exceeds the ambient half-degree. -/
theorem oldSupport_le_halfDegree {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2 * N))))
    (hH : ResidualSector H) :
    oldSupport H hH ≤ N := by
  calc
    oldSupport H hH = ∑ o : Orbit H, oldSupportAt H hH o := rfl
    _ ≤ ∑ o : Orbit H, parameter H hH o := by
      apply Finset.sum_le_sum
      intro o ho
      let C := BinaryS16DirectCertifiedOrbitProfile.profile H hH o
      change certificateOldSupport H C ≤ certificateParameter H C
      cases C <;> simp [certificateOldSupport, certificateParameter]
    _ = N := parameter_sum H hH

/-! ## The single remaining per-occurrence geometric interface -/

include hH in
/-- A completed joint profile supplies, for each literal occurrence, a slot
  on the canonical product axis with the parameter and old support read from
  the very same certificate that defined its action and chart.

For critical certificates this is the quotient-identity critical slot on the
canonical axis.  For positive certificates it is the stored certified slot,
transported along `canonicalAxis_eq_fusionDeletedAxis`; the required selected
chart is built from the certificate's retained `W` and `hpoint`. -/
abbrev AxisRouting :=
  ∀ q : Σ o, Fin ((data H hH).multiplicity o),
    CertifiedSlot
      (CanonicalOrbitWord.axis (Points H hH) (action H hH) H (data H hH) q)
      (parameter H hH q.1) (oldSupportAt H hH q.1)

end SymmetricSubgroupAsymptotics.BinaryS16JointOrbitData

end
