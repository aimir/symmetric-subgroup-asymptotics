import SymmetricSubgroupAsymptotics.BinaryDegree16PhysicalAnalyticClosure
import SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge
import SymmetricSubgroupAsymptotics.BinaryMenuSmallCoverage
import SymmetricSubgroupAsymptotics.CriticalOrbitCriterion
import SymmetricSubgroupAsymptotics.SmallOriginalOrbitCharts

/-!
# The canonical retained-background profile below width sixteen

This is the structural all-orbit split used by the retained-background
sector `S16`.  The source subgroup is fixed-point-free and binary, every
literal orbit has size at most sixteen, and the already counted direct
families in degrees eight and sixteen have been removed.

No arbitrary hypothesis about non-eight-point orbits is used.  Binaryity and
fixed-point-freeness force the exact list of widths `2,4,8,16`.  Width sixteen
is routed by the checked all-witness carrier theorem; width eight is routed by
the checked supported-or-E8 theorem; widths two and four use the complete
small action registry and quotient-identity mixture slots.

The structure `SmallRegistryMixtureEquations` isolates the four finite literal
equalities identifying the checked small registry rows with C2, C4, V4 and
D8.  The concrete value `smallRegistryMixtureEquations` below proves those
equalities from explicit point relabellings and the existing finite Cayley
certificates.  Thus the final dichotomy has no classification premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryS16CanonicalCarrierProfile

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierMenuSlots
open BinaryDegreeEightPhysicalAnalyticClosure

namespace D8
abbrev carrierResidualFamily :=
  BinaryDegreeEightNormalizerSaturatedDirect.carrierResidualFamily
end D8

namespace D16
abbrev carrierResidualFamily :=
  BinaryDegree16PhysicalAnalyticClosure.carrierResidualFamily
end D16

/-! ## The finite small-registry bridge -/

/-- The intended mixture colour of each of the three checked four-point
registry rows: regular C4, regular V4, and natural D8. -/
def smallKind4 : Fin 3 → MixtureKind
  | 0 => .inr none
  | 1 => .inl .v4
  | 2 => .inl .d8

/-- Literal point relabellings connecting the already checked width-two and
width-four registries to the completed mixture alphabet.  These are four
finite equations, not a classification assumption: completeness remains the
proved theorem `BinaryMenuSmallCoverage.width2_complete/width4_complete`. -/
structure SmallRegistryMixtureEquations where
  point2 : mixturePoints (.inl .c2) ≃ Fin 2
  image2 :
    relabelSubgroup point2 (mixtureAction (.inl .c2)) =
      Subgroup.closure (Set.range BinaryMenuCayley2T1.generators)
  point4 : ∀ k : Fin 3, mixturePoints (smallKind4 k) ≃ Fin 4
  image4 : ∀ k : Fin 3,
    relabelSubgroup (point4 k) (mixtureAction (smallKind4 k)) =
      BinaryMenuSmallCoverage.actions4 k

/-! The concrete point charts for the four small original actions. -/

def c2PointEquiv : mixturePoints (.inl .c2) ≃ Fin 2 :=
  Fintype.equivOfCardEq
    ((criticalAction_point_card .c2).trans (Fintype.card_fin 2).symm)

def cyclicFourPointEquiv : mixturePoints (.inr none) ≃ Fin 4 :=
  (ZMod.finEquiv 4).toEquiv.symm

def v4PointToFin (x : mixturePoints (.inl .v4)) : Fin 4 := by
  letI : DecidableEq (ZMod 2) := ZMod.decidableEq 2
  exact if x 0 = 0 then
    if x 1 = 0 then 0 else 2
  else if x 1 = 0 then 1 else 3

def finToV4Point (i : Fin 4) : mixturePoints (.inl .v4) :=
  (#[![0,0],![1,0],![0,1],![1,1]] :
    Array (criticalActionPoints .v4))[i]

def v4PointEquiv : mixturePoints (.inl .v4) ≃ Fin 4 where
  toFun := v4PointToFin
  invFun := finToV4Point
  left_inv := by
    intro x
    change (finToV4Point (v4PointToFin x) : Fin 2 → ZMod 2) = x
    fin_cases x
    all_goals
      apply funext
      intro j
      fin_cases j <;> native_decide
  right_inv := by native_decide

def d8PointToFin (x : mixturePoints (.inl .d8)) : Fin 4 := by
  letI : DecidableEq (ZMod 2) := ZMod.decidableEq 2
  exact if x.1 0 = 0 then
    if x.2 = 0 then 0 else 2
  else if x.2 = 0 then 1 else 3

def finToD8Point (i : Fin 4) : mixturePoints (.inl .d8) :=
  (#[(fun _ => 0,0),(fun _ => 1,0),(fun _ => 0,1),(fun _ => 1,1)] :
    Array (criticalActionPoints .d8))[i]

def d8PointEquiv : mixturePoints (.inl .d8) ≃ Fin 4 where
  toFun := d8PointToFin
  invFun := finToD8Point
  left_inv := by
    intro x
    change (finToD8Point (d8PointToFin x) :
      (Fin 1 → ZMod 2) × ZMod 2) = x
    fin_cases x
    all_goals
      apply Prod.ext
      · apply funext
        intro j
        fin_cases j <;> native_decide
      · native_decide
  right_inv := by native_decide

private theorem cyclicFour_generator_image (j : Fin 1) :
    cyclicFourPointEquiv.permCongr
        (BinaryCarrierOriginalCyclicFourHall.cyclicFourAction
          (Multiplicative.ofAdd 1)) =
      BinaryMenuCayley4T1.generators j := by
  revert j
  decide +kernel

private def v4Generators : Fin 2 → Multiplicative (Fin 2 → ZMod 2)
  | 0 => Multiplicative.ofAdd ![1,1]
  | 1 => Multiplicative.ofAdd ![1,0]

private theorem v4_generator_image (j : Fin 2) :
    v4PointEquiv.permCongr (regularBinaryAction 2 (v4Generators j)) =
      BinaryMenuCayley4T2.generators j := by
  apply Equiv.ext
  intro x
  revert x j
  decide +kernel

private def d8Generators : Fin 2 → BinaryHeisenberg 1
  | 0 => ⟨(fun _ => 1),(fun _ => 1),0⟩
  | 1 => ⟨(fun _ => 0),(fun _ => 1),1⟩

private theorem d8_generator_image (j : Fin 2) :
    d8PointEquiv.permCongr (BinaryHeisenberg.action 1 (d8Generators j)) =
      BinaryMenuCayley4T3.generators j := by
  apply Equiv.ext
  intro x
  revert x j
  decide +kernel

theorem cyclicFour_relabel_eq_registry :
    relabelSubgroup cyclicFourPointEquiv (mixtureAction (.inr none)) =
      Subgroup.closure (Set.range BinaryMenuCayley4T1.generators) := by
  change relabelSubgroup cyclicFourPointEquiv
      BinaryCarrierOriginalCyclicFourHall.CyclicFourOriginal = _
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    rw [← cyclicFour_generator_image j]
    exact ⟨BinaryCarrierOriginalCyclicFourHall.cyclicFourAction
      (Multiplicative.ofAdd 1),⟨Multiplicative.ofAdd 1,rfl⟩,rfl⟩
  · have hleft : Nat.card (relabelSubgroup cyclicFourPointEquiv
        BinaryCarrierOriginalCyclicFourHall.CyclicFourOriginal) = 4 := by
      let E := BinaryCarrierOriginalCyclicFourHall.CyclicFourOriginal.equivMapOfInjective
        cyclicFourPointEquiv.permCongrHom.toMonoidHom
          cyclicFourPointEquiv.permCongrHom.injective
      change Nat.card (BinaryCarrierOriginalCyclicFourHall.CyclicFourOriginal.map
        cyclicFourPointEquiv.permCongrHom.toMonoidHom) = 4
      calc
        _ = Nat.card BinaryCarrierOriginalCyclicFourHall.CyclicFourOriginal :=
          (Nat.card_congr E.toEquiv).symm
        _ = Nat.card (Multiplicative (ZMod 4)) :=
          (Nat.card_congr
            BinaryCarrierOriginalCyclicFourHall.cyclicFourEquiv.toEquiv).symm
        _ = 4 := by norm_num
    rw [hleft,BinaryMenuCayley4T1.exact_card]

theorem v4_relabel_eq_registry :
    relabelSubgroup v4PointEquiv (mixtureAction (.inl .v4)) =
      Subgroup.closure (Set.range BinaryMenuCayley4T2.generators) := by
  change relabelSubgroup v4PointEquiv (criticalActionSubgroup .v4) = _
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    rw [← v4_generator_image j]
    exact ⟨regularBinaryAction 2 (v4Generators j),⟨v4Generators j,rfl⟩,rfl⟩
  · have hleft : Nat.card
        (relabelSubgroup v4PointEquiv (criticalActionSubgroup .v4)) = 4 := by
      let E := (criticalActionSubgroup .v4).equivMapOfInjective
        v4PointEquiv.permCongrHom.toMonoidHom
          v4PointEquiv.permCongrHom.injective
      change Nat.card ((criticalActionSubgroup .v4).map
        v4PointEquiv.permCongrHom.toMonoidHom) = 4
      calc
        _ = Nat.card (criticalActionSubgroup .v4) :=
          (Nat.card_congr E.toEquiv).symm
        _ = 4 := by simpa [criticalActionOrder] using
          criticalAction_group_card .v4
    rw [hleft,BinaryMenuCayley4T2.exact_card]

theorem d8_relabel_eq_registry :
    relabelSubgroup d8PointEquiv (mixtureAction (.inl .d8)) =
      Subgroup.closure (Set.range BinaryMenuCayley4T3.generators) := by
  change relabelSubgroup d8PointEquiv (criticalActionSubgroup .d8) = _
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    rw [← d8_generator_image j]
    exact ⟨BinaryHeisenberg.action 1 (d8Generators j),⟨d8Generators j,rfl⟩,rfl⟩
  · have hleft : Nat.card
        (relabelSubgroup d8PointEquiv (criticalActionSubgroup .d8)) = 8 := by
      let E := (criticalActionSubgroup .d8).equivMapOfInjective
        d8PointEquiv.permCongrHom.toMonoidHom
          d8PointEquiv.permCongrHom.injective
      change Nat.card ((criticalActionSubgroup .d8).map
        d8PointEquiv.permCongrHom.toMonoidHom) = 8
      calc
        _ = Nat.card (criticalActionSubgroup .d8) :=
          (Nat.card_congr E.toEquiv).symm
        _ = 8 := by simpa [criticalActionOrder] using
          criticalAction_group_card .d8
    rw [hleft,BinaryMenuCayley4T3.exact_card]

/-- The small-registry-to-mixture bridge has a concrete checked value. -/
def smallRegistryMixtureEquations : SmallRegistryMixtureEquations where
  point2 := c2PointEquiv
  image2 := by
    change relabelSubgroup c2PointEquiv (criticalActionSubgroup .c2) = _
    rw [SmallOriginalOrbitCharts.critical_pair_eq_top]
    have hregistry : Subgroup.closure
        (Set.range BinaryMenuCayley2T1.generators) = ⊤ := by
      apply (Subgroup.closure
        (Set.range BinaryMenuCayley2T1.generators)).eq_top_of_card_eq
      rw [BinaryMenuCayley2T1.exact_card,Nat.card_eq_fintype_card,
        Fintype.card_perm]
      norm_num
    rw [hregistry]
    exact (relabelSubgroup c2PointEquiv).map_top
  point4
    | 0 => cyclicFourPointEquiv
    | 1 => v4PointEquiv
    | 2 => d8PointEquiv
  image4 := by
    intro k
    fin_cases k
    · simpa [BinaryMenuSmallCoverage.actions4] using
        cyclicFour_relabel_eq_registry
    · simpa [BinaryMenuSmallCoverage.actions4] using
        v4_relabel_eq_registry
    · simpa [BinaryMenuSmallCoverage.actions4] using
        d8_relabel_eq_registry

/-! ## Complete physical models on small actual orbits -/

/-- A literal orbit of width `w`, retaining binaryity of its faithful image.
The intended uses below are only `w=2` and `w=4`. -/
structure SmallOrbitWitness (w : ℕ) {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) where
  point : Fin n
  orbit_card : Nat.card (MulAction.orbit H point) = w
  binary : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H point)

namespace SmallOrbitWitness

variable {w n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
  (W : SmallOrbitWitness w H)

def chart : Fin w ⊕ Fin (n-w) ≃ Fin n :=
  FusionActualOrbitCharts.chart H W.point W.orbit_card

def action : Subgroup (Equiv.Perm (Fin w)) :=
  FusionActualOrbitCharts.chartAction H W.point W.orbit_card

def pulled : Subgroup (Equiv.Perm (Fin w ⊕ Fin (n-w))) :=
  relabelSubgroup W.chart.symm H

def model : Subgroup (W.action × Equiv.Perm (Fin (n-w))) :=
  fusionDeletedModel W.action W.pulled

theorem action_binary : IsPGroup 2 W.action :=
  FusionActualOrbitCharts.chartAction_isPGroup H W.point W.orbit_card 2 W.binary

instance action_pretransitive : MulAction.IsPretransitive W.action (Fin w) :=
  FusionActualOrbitCharts.chartAction_transitive H W.point W.orbit_card

theorem pulled_preserves :
    ∀ k ∈ W.pulled,
      Set.MapsTo k (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w)))
        (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w))) :=
  FusionActualOrbitCharts.chart_preserves H W.point W.orbit_card

theorem first_projection :
    (fusionPhysicalBlockPullback W.pulled).map
      (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w)))) = W.action :=
  rfl

theorem model_full :
    W.model.map (MonoidHom.fst W.action (Equiv.Perm (Fin (n-w)))) = ⊤ :=
  fusionDeletedModel_full W.action W.pulled W.first_projection

def axis : Subgroup W.action := W.model.goursatFst

instance axis_normal : W.axis.Normal :=
  Subgroup.normal_goursatFst (by
    intro u
    have hu : u ∈ W.model.map
        (MonoidHom.fst W.action (Equiv.Perm (Fin (n-w)))) := by
      rw [W.model_full]
      trivial
    obtain ⟨x,hx,he⟩ := hu
    exact ⟨⟨x,hx⟩,he⟩)

/-- Relabel one small orbit by an original mixture colour and keep its exact
Goursat axis as the quotient kernel of a one-cell identity slot. -/
def quotientIdentityAxisSlot (g : MixtureKind)
    (e : mixturePoints g ≃ Fin w)
    (he : relabelSubgroup e (mixtureAction g) = W.action) :
    AxisSlot W.action W.axis := by
  let E : mixtureAction g ≃* W.action :=
    ((mixtureAction g).equivMapOfInjective e.permCongrHom.toMonoidHom
      e.permCongrHom.injective).trans (MulEquiv.subgroupCongr he)
  let M : Subgroup (mixtureAction g) := W.axis.map E.symm.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ E.symm.surjective
  exact {
    slot := quotientIdentitySlot g M
    sourceEquiv := E.symm
    kernel := (quotientIdentitySlot_alpha_ker g M).symm }

/-- A critical mixture relabelling on the chart action gives the exact
critical chart on the original literal orbit. -/
theorem criticalOrbit_of_relabel (i : CriticalActionKind)
    (e : criticalActionPoints i ≃ Fin w)
    (he : relabelSubgroup e (criticalActionSubgroup i) = W.action) :
    ∃ c : criticalActionPoints i ≃ MulAction.orbit H W.point,
      relabelSubgroup c (criticalActionSubgroup i) =
        OrbitProfileFromOrbits.orbitImage H
          (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) := by
  let c := FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card
  refine ⟨e.trans c,?_⟩
  calc
    relabelSubgroup (e.trans c) (criticalActionSubgroup i) =
        relabelSubgroup c (relabelSubgroup e (criticalActionSubgroup i)) :=
      (relabelSubgroup_trans e c _).symm
    _ = relabelSubgroup c W.action := by rw [he]
    _ = OrbitProfileFromOrbits.orbitImage H
          (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) := by
      change relabelSubgroup c
          (FusionActualOrbitCharts.chartAction H W.point W.orbit_card) = _
      rw [FusionActualOrbitCharts.chartAction_eq_map]
      exact relabelSubgroup_symm c.symm _

/-- The same chart stated on the literal quotient-orbit fibre.  The
`orbit_mk` simplification is the dependent-type bridge used by the canonical
all-orbit profile. -/
theorem criticalOrbit_of_relabel_quotient (i : CriticalActionKind)
    (e : criticalActionPoints i ≃ Fin w)
    (he : relabelSubgroup e (criticalActionSubgroup i) = W.action) :
    ∃ c : criticalActionPoints i ≃
        MulAction.orbitRel.Quotient.orbit
          (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H),
      relabelSubgroup c (criticalActionSubgroup i) =
        OrbitProfileFromOrbits.orbitImage H
          (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) := by
  simpa only [MulAction.orbitRel.Quotient.orbit_mk] using
    W.criticalOrbit_of_relabel i e he

end SmallOrbitWitness

/-! ## Literal-orbit witnesses and the exact width split -/

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

abbrev Orbit := OrbitProfileFromOrbits.Orbit H

/-- Transport a critical chart along equality in the literal orbit quotient.
Writing the dependent motive explicitly avoids asking `rw` to invent a type
correct motive for the orbit subtype and its restriction image at once. -/
theorem criticalChart_transport (i : CriticalActionKind)
    {q o : Orbit H} (h : q = o)
    (hc : ∃ e : criticalActionPoints i ≃ q.orbit,
      relabelSubgroup e (criticalActionSubgroup i) =
        OrbitProfileFromOrbits.orbitImage H q) :
    ∃ e : criticalActionPoints i ≃ o.orbit,
      relabelSubgroup e (criticalActionSubgroup i) =
        OrbitProfileFromOrbits.orbitImage H o :=
  Eq.ndrec (motive := fun r : Orbit H =>
    ∃ e : criticalActionPoints i ≃ r.orbit,
      relabelSubgroup e (criticalActionSubgroup i) =
        OrbitProfileFromOrbits.orbitImage H r) hc h

def smallWitness (hbinary : IsPGroup 2 H) (w : ℕ) (o : Orbit H)
    (hw : Nat.card o.orbit = w) : SmallOrbitWitness w H where
  point := o.out
  orbit_card := by
    rw [← o.orbit_eq_orbit_out Quotient.out_eq']
    exact hw
  binary := PermutationCharacterRankSplit.image_isPGroup
    (FusionActualOrbitCharts.orbitSet H o.out) 2 hbinary

def witness8 (hbinary : IsPGroup 2 H) (o : Orbit H)
    (hw : Nat.card o.orbit = 8) :
    BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H where
  point := o.out
  orbit_card := by
    rw [← o.orbit_eq_orbit_out Quotient.out_eq']
    exact hw
  binary := PermutationCharacterRankSplit.image_isPGroup
    (FusionActualOrbitCharts.orbitSet H o.out) 2 hbinary

def witness16 (hbinary : IsPGroup 2 H) (o : Orbit H)
    (hw : Nat.card o.orbit = 16) :
    BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H where
  point := o.out
  orbit_card := by
    rw [← o.orbit_eq_orbit_out Quotient.out_eq']
    exact hw
  binary := PermutationCharacterRankSplit.image_isPGroup
    (FusionActualOrbitCharts.orbitSet H o.out) 2 hbinary

/-- Fixed-point-free binary orbits below width sixteen have exactly one of
the four possible widths. -/
theorem orbit_card_cases (hbinary : IsPGroup 2 H)
    (hnofixed : HasNoFixedPoints H) (o : Orbit H)
    (hle : Nat.card o.orbit ≤ 16) :
    Nat.card o.orbit = 2 ∨ Nat.card o.orbit = 4 ∨
      Nat.card o.orbit = 8 ∨ Nat.card o.orbit = 16 := by
  obtain ⟨k,hk⟩ := hbinary.card_orbit o.out
  have horbit : Nat.card o.orbit = 2^k := by
    rw [o.orbit_eq_orbit_out Quotient.out_eq']
    exact hk
  have hone : Nat.card o.orbit ≠ 1 := by
    intro hcard
    have hfixed : o.out ∈ MulAction.fixedPoints H (Fin n) :=
      MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
        simpa only [Fintype.card_eq_nat_card, ← o.orbit_eq_orbit_out Quotient.out_eq']
          using hcard)
    obtain ⟨g,hg⟩ := hnofixed o.out
    exact hg (MulAction.mem_fixedPoints.mp hfixed g)
  have hkpos : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst k
    exact hone (by simpa using horbit)
  have hkfour : k ≤ 4 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [horbit, show (2:ℕ)^4 = 16 from rfl] using hle
  interval_cases k <;> simp_all

/-! ## Quotient-identity routes in widths two and four -/

/-- Conjugating a checked small registry row back to the chart action gives
one literal mixture relabelling of that chart action. -/
theorem small_relabel_of_registry
    {w : ℕ} (W : SmallOrbitWitness w H)
    (g : Equiv.Perm (Fin w))
    {U : Subgroup (Equiv.Perm (Fin w))}
    (hg : MulAut.conj g • W.action = U)
    {c : MixtureKind} (e : mixturePoints c ≃ Fin w)
    (he : relabelSubgroup e (mixtureAction c) = U) :
    relabelSubgroup (e.trans g.symm) (mixtureAction c) = W.action := by
  change relabelSubgroup g W.action = U at hg
  calc
    relabelSubgroup (e.trans g.symm) (mixtureAction c) =
        relabelSubgroup g.symm (relabelSubgroup e (mixtureAction c)) :=
      (relabelSubgroup_trans e g.symm _).symm
    _ = relabelSubgroup g.symm U := by rw [he]
    _ = relabelSubgroup g.symm (relabelSubgroup g W.action) := by rw [hg]
    _ = W.action := relabelSubgroup_symm g W.action

/-- The unique two-point row is retained as the C2 quotient-identity colour,
and its original orbit is already a critical C2 orbit. -/
theorem width2_identitySlot_and_critical
    (B : SmallRegistryMixtureEquations) (hbinary : IsPGroup 2 H)
    (o : Orbit H) (hcard : Nat.card o.orbit = 2) :
    let W := smallWitness H hbinary 2 o hcard
    Nonempty (AxisSlot W.action W.axis) ∧
      ∃ e : criticalActionPoints .c2 ≃ o.orbit,
        relabelSubgroup e (criticalActionSubgroup .c2) =
          OrbitProfileFromOrbits.orbitImage H o := by
  let W := smallWitness H hbinary 2 o hcard
  have htrans : PermutationSubgroupTransitive W.action := by
    intro x y
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq W.action x y
    exact ⟨u,u.property,hu⟩
  obtain ⟨_,g,hg⟩ := BinaryMenuSmallCoverage.width2_complete
    W.action W.action_binary htrans
  let e := B.point2.trans g.symm
  have he : relabelSubgroup e (mixtureAction (.inl .c2)) = W.action :=
    small_relabel_of_registry H W g hg B.point2 B.image2
  refine ⟨⟨W.quotientIdentityAxisSlot (.inl .c2) e he⟩,?_⟩
  have hc := W.criticalOrbit_of_relabel_quotient .c2 e he
  have hpoint : Quotient.mk'' W.point = o := by
    dsimp [W,smallWitness]
    exact Quotient.out_eq' o
  exact criticalChart_transport H .c2 hpoint hc

/-- The complete four-point registry yields either the positive regular-C4
identity slot or one of the two critical identity slots V4 and D8. -/
theorem width4_supported_or_critical
    (B : SmallRegistryMixtureEquations) (hbinary : IsPGroup 2 H)
    (o : Orbit H) (hcard : Nat.card o.orbit = 4) :
    let W := smallWitness H hbinary 4 o hcard
    Nonempty {S : AxisSlot W.action W.axis // S.HasNoncritical} ∨
      (∃ i : CriticalActionKind,
        ∃ e : criticalActionPoints i ≃ o.orbit,
          relabelSubgroup e (criticalActionSubgroup i) =
            OrbitProfileFromOrbits.orbitImage H o) := by
  let W := smallWitness H hbinary 4 o hcard
  have htrans : PermutationSubgroupTransitive W.action := by
    intro x y
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq W.action x y
    exact ⟨u,u.property,hu⟩
  obtain ⟨k,g,hg⟩ := BinaryMenuSmallCoverage.width4_complete
    W.action W.action_binary htrans
  let e := (B.point4 k).trans g.symm
  have he : relabelSubgroup e (mixtureAction (smallKind4 k)) = W.action :=
    small_relabel_of_registry H W g hg (B.point4 k) (B.image4 k)
  fin_cases k
  · left
    let S := W.quotientIdentityAxisSlot (.inr none) e he
    refine ⟨⟨S,?_⟩⟩
    change ∃ c : Fin 1, ∃ t, (smallKind4 0) = .inr t
    exact ⟨0,none,rfl⟩
  · right
    refine ⟨.v4,?_⟩
    have hc := W.criticalOrbit_of_relabel_quotient .v4 e he
    have hpoint : Quotient.mk'' W.point = o := by
      dsimp [W,smallWitness]
      exact Quotient.out_eq' o
    exact criticalChart_transport H .v4 hpoint hc
  · right
    refine ⟨.d8,?_⟩
    have hc := W.criticalOrbit_of_relabel_quotient .d8 e he
    have hpoint : Quotient.mk'' W.point = o := by
      dsimp [W,smallWitness]
      exact Quotient.out_eq' o
    exact criticalChart_transport H .d8 hpoint hc

/-! ## The canonical all-orbit profile -/

/-- The seven structural colours in the retained `S16` background.  The
first four are earlier critical owners; the last three have positive mixture
support. -/
inductive OrbitColor
  | c2 | v4 | d8 | e8
  | cyclicFour | carrier8 | carrier16
  deriving DecidableEq, Fintype

def OrbitColor.IsPositive : OrbitColor → Prop
  | .cyclicFour | .carrier8 | .carrier16 => True
  | _ => False

/-- Exact physical meaning of a colour on one literal orbit.  Carrier colours
retain an actual orbit witness and a positive exact-axis slot. -/
inductive Realizes (o : Orbit H) : OrbitColor → Prop
  | c2 (e : criticalActionPoints .c2 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .c2) =
        OrbitProfileFromOrbits.orbitImage H o) : Realizes o .c2
  | v4 (e : criticalActionPoints .v4 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .v4) =
        OrbitProfileFromOrbits.orbitImage H o) : Realizes o .v4
  | d8 (e : criticalActionPoints .d8 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .d8) =
        OrbitProfileFromOrbits.orbitImage H o) : Realizes o .d8
  | e8 (e : criticalActionPoints .e8 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .e8) =
        OrbitProfileFromOrbits.orbitImage H o) : Realizes o .e8
  | cyclicFour (W : SmallOrbitWitness 4 H)
      (hpoint : Quotient.mk'' W.point = o)
      (S : AxisSlot W.action W.axis) (hs : S.HasNoncritical) :
      Realizes o .cyclicFour
  | carrier8
      (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
      (hpoint : Quotient.mk'' W.point = o)
      (S : AxisSlot W.action W.axis) (hs : S.HasNoncritical) :
      Realizes o .carrier8
  | carrier16
      (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
      (hpoint : Quotient.mk'' W.point = o)
      (S : AxisSlot W.action W.axis) (hs : S.HasNoncritical) :
      Realizes o .carrier16

/-- The exact retained-background assumptions, with direct ownership removed
intrinsically at the family level. -/
structure ResidualSector : Prop where
  binary : IsPGroup 2 H
  noFixedPoints : HasNoFixedPoints H
  orbit_le : ∀ o : Orbit H, Nat.card o.orbit ≤ 16
  noDirect8 : H ∉ BinaryDegreeEightNormalizerSaturatedDirect.directFamily n
  noDirect16 : H ∉ BinaryDegree16PhysicalAnalyticClosure.directFamily n

/-- Every literal orbit in the retained background has one of the seven exact
physical realizations. -/
theorem exists_realization (B : SmallRegistryMixtureEquations)
    (hH : ResidualSector H) (o : Orbit H) :
    ∃ c : OrbitColor, Realizes H o c := by
  rcases orbit_card_cases H hH.binary hH.noFixedPoints o (hH.orbit_le o) with
    h2 | h4 | h8 | h16
  · obtain ⟨_,e,he⟩ := width2_identitySlot_and_critical H B hH.binary o h2
    exact ⟨.c2,Realizes.c2 e he⟩
  · rcases width4_supported_or_critical H B hH.binary o h4 with hs | hc
    · let W := smallWitness H hH.binary 4 o h4
      let S := Classical.choice hs
      exact ⟨.cyclicFour,Realizes.cyclicFour W (by
        dsimp [W,smallWitness]
        exact Quotient.out_eq' o) S.1 S.2⟩
    · obtain ⟨i,e,he⟩ := hc
      cases i with
      | c2 => exact ⟨.c2,Realizes.c2 e he⟩
      | v4 => exact ⟨.v4,Realizes.v4 e he⟩
      | d8 => exact ⟨.d8,Realizes.d8 e he⟩
      | e8 => exact ⟨.e8,Realizes.e8 e he⟩
  · let W := witness8 H hH.binary o h8
    have hres : H ∈ D8.carrierResidualFamily n := ⟨⟨W⟩,hH.noDirect8⟩
    rcases
        SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge.carrierResidual_supportedSlot_or_isE8Orbit
          hres W with hs | he8
    · let S := Classical.choice hs
      exact ⟨.carrier8,Realizes.carrier8 W (by
        dsimp [W,witness8]
        exact Quotient.out_eq' o) S.1 S.2⟩
    · obtain ⟨e,he⟩ := he8
      have hpoint : Quotient.mk'' W.point = o := by
        dsimp [W,witness8]
        exact Quotient.out_eq' o
      simpa only [hpoint] using (show ∃ c : OrbitColor, Realizes H
        (Quotient.mk'' W.point) c from ⟨.e8,Realizes.e8 e he⟩)
  · let W := witness16 H hH.binary o h16
    have hres : H ∈ D16.carrierResidualFamily n := ⟨⟨W⟩,hH.noDirect16⟩
    let S := Classical.choice
      (BinaryDegree16PhysicalAnalyticClosure.carrierResidual_all_supported_slots hres W)
    exact ⟨.carrier16,Realizes.carrier16 W (by
      dsimp [W,witness16]
      exact Quotient.out_eq' o) S.1 S.2⟩

/-- Canonical finite colour profile on the literal orbit quotient.  Choice is
used only to define a deterministic profile; it is not attached as a mark to
the subgroup being counted. -/
noncomputable def profile (B : SmallRegistryMixtureEquations)
    (hH : ResidualSector H) : Orbit H → OrbitColor :=
  fun o => Classical.choose (exists_realization H B hH o)

theorem profile_realizes (B : SmallRegistryMixtureEquations)
    (hH : ResidualSector H) (o : Orbit H) :
    Realizes H o (profile H B hH o) :=
  Classical.choose_spec (exists_realization H B hH o)

def HasPositiveSupport (B : SmallRegistryMixtureEquations)
    (hH : ResidualSector H) : Prop :=
  ∃ o : Orbit H, (profile H B hH o).IsPositive

/-- A nonpositive realization is exactly a critical original orbit. -/
theorem critical_of_realizes_not_positive {o : Orbit H} {c : OrbitColor}
    (hc : Realizes H o c) (hn : ¬ c.IsPositive) :
    ∃ i : CriticalActionKind,
      ∃ e : criticalActionPoints i ≃ o.orbit,
        relabelSubgroup e (criticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage H o := by
  cases hc with
  | c2 e he => exact ⟨.c2,e,he⟩
  | v4 e he => exact ⟨.v4,e,he⟩
  | d8 e he => exact ⟨.d8,e,he⟩
  | e8 e he => exact ⟨.e8,e,he⟩
  | cyclicFour _ _ _ _ => exact False.elim (hn trivial)
  | carrier8 _ _ _ _ => exact False.elim (hn trivial)
  | carrier16 _ _ _ _ => exact False.elim (hn trivial)

/-- The retained background either contains a positive routed occurrence or
every literal orbit is already one of the four critical actions. -/
theorem hasPositiveSupport_or_allCritical
    (B : SmallRegistryMixtureEquations) (hH : ResidualSector H) :
    HasPositiveSupport H B hH ∨ CriticalOrbitCriterion.AllCriticalOrbits H := by
  by_cases hp : ∃ o : Orbit H, (profile H B hH o).IsPositive
  · exact Or.inl hp
  · right
    intro o
    exact critical_of_realizes_not_positive H
      (profile_realizes H B hH o) (fun ho => hp ⟨o,ho⟩)

/-- On the even physical set, the zero-support branch is exactly the already
counted complete critical owner. -/
theorem hasPositiveSupport_or_isEvenCritical {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2*N))))
    (B : SmallRegistryMixtureEquations) (hH : ResidualSector H) :
    HasPositiveSupport H B hH ∨ IsEvenCriticalSubgroup N H := by
  rcases hasPositiveSupport_or_allCritical H B hH with hp | hc
  · exact Or.inl hp
  · exact Or.inr ((CriticalOrbitCriterion.isEvenCritical_iff N H).2 hc)

/-- Assumption-free checked profile, using the exported finite small-registry
equations above. -/
abbrev checkedProfile (hH : ResidualSector H) : Orbit H → OrbitColor :=
  profile H smallRegistryMixtureEquations hH

/-- Final structural dichotomy for the actual retained `S16` background. -/
theorem checked_hasPositiveSupport_or_allCritical (hH : ResidualSector H) :
    HasPositiveSupport H smallRegistryMixtureEquations hH ∨
      CriticalOrbitCriterion.AllCriticalOrbits H :=
  hasPositiveSupport_or_allCritical H smallRegistryMixtureEquations hH

/-- Even-degree form consumed by the earlier-owner partition. -/
theorem checked_hasPositiveSupport_or_isEvenCritical {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2*N)))) (hH : ResidualSector H) :
    HasPositiveSupport H smallRegistryMixtureEquations hH ∨
      IsEvenCriticalSubgroup N H :=
  hasPositiveSupport_or_isEvenCritical H smallRegistryMixtureEquations hH

end SymmetricSubgroupAsymptotics.BinaryS16CanonicalCarrierProfile

end
