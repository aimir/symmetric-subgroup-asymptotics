import SymmetricSubgroupAsymptotics.BinaryExceptional16CyclicOwner
import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles

/-!
# The reversible 16T1086 carrier is an original physical profile

The four literal restriction images of the proper 16T1086 carrier are one
regular cyclic-four action and three copies of the critical degree-four
dihedral action.  The carrier remains the actual proper subdirect subgroup;
it is never replaced by the product of its restriction images.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryExceptional16PhysicalProfile

open SymmetricSubgroupAsymptotics
open BinaryCarrierOriginalCyclicFourHall

local instance : Inhabited (criticalActionPoints .d8) := ⟨(0,0)⟩

/-- Natural labels on the regular cyclic-four action. -/
def cyclicPointEquiv : ZMod 4 ≃ Fin 4 :=
  (ZMod.finEquiv 4).toEquiv.symm

/-- Labels under which the canonical critical D8 action has the literal
generator closure appearing on each of the last three carrier blocks. -/
def dihedralPointEquiv : criticalActionPoints .d8 ≃ Fin 4 where
  toFun x :=
    if x.1 0 = 0 then
      if x.2 = 0 then 0 else 2
    else
      if x.2 = 0 then 1 else 3
  invFun i :=
    (#[
      ((fun _ => 0), 0),
      ((fun _ => 1), 0),
      ((fun _ => 0), 1),
      ((fun _ => 1), 1)
    ] : Array (criticalActionPoints .d8))[i.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The first literal block is the existing original C4 color, with an
explicit point relabelling. -/
theorem cyclic_relabel_eq :
    relabelSubgroup cyclicPointEquiv CyclicFourOriginal =
      Subgroup.closure (Set.range BinaryChart16T1086.block0BaseGenerators) := by
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have hj : cyclicPointEquiv.permCongr
        (cyclicFourAction (Multiplicative.ofAdd 1)) =
          BinaryChart16T1086.block0BaseGenerators j := by
      revert j
      decide +kernel
    change BinaryChart16T1086.block0BaseGenerators j ∈
      relabelSubgroup cyclicPointEquiv CyclicFourOriginal
    rw [← hj]
    exact ⟨cyclicFourAction (Multiplicative.ofAdd 1),
      ⟨Multiplicative.ofAdd 1,rfl⟩,rfl⟩
  · have hleft : Nat.card (relabelSubgroup cyclicPointEquiv CyclicFourOriginal)=4 := by
      let E := CyclicFourOriginal.equivMapOfInjective
        cyclicPointEquiv.permCongrHom.toMonoidHom cyclicPointEquiv.permCongrHom.injective
      change Nat.card (CyclicFourOriginal.map
        cyclicPointEquiv.permCongrHom.toMonoidHom)=4
      rw [← Nat.card_congr E.toEquiv,← Nat.card_congr cyclicFourEquiv.toEquiv]
      norm_num
    rw [hleft,BinaryChart16T1086.block0_base_card]

private def dihedralGenerators : Fin 2 → BinaryHeisenberg 1
  | 0 => ⟨(fun _ => 1),(fun _ => 1),0⟩
  | 1 => ⟨(fun _ => 0),(fun _ => 1),1⟩

private theorem dihedral_generator_image (j : Fin 2) :
    dihedralPointEquiv.permCongr
        (BinaryHeisenberg.action 1 (dihedralGenerators j)) =
      BinaryChart16T1086.block1BaseGenerators j := by
  revert j
  decide +kernel

private theorem dihedral_relabel_eq_block1 :
    relabelSubgroup dihedralPointEquiv (criticalActionSubgroup .d8) =
      Subgroup.closure (Set.range BinaryChart16T1086.block1BaseGenerators) := by
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change BinaryChart16T1086.block1BaseGenerators j ∈
      relabelSubgroup dihedralPointEquiv (criticalActionSubgroup .d8)
    rw [← dihedral_generator_image j]
    exact ⟨BinaryHeisenberg.action 1 (dihedralGenerators j),
      ⟨dihedralGenerators j,rfl⟩,rfl⟩
  · have hleft : Nat.card
        (relabelSubgroup dihedralPointEquiv (criticalActionSubgroup .d8))=8 := by
      let E := (criticalActionSubgroup .d8).equivMapOfInjective
        dihedralPointEquiv.permCongrHom.toMonoidHom
          dihedralPointEquiv.permCongrHom.injective
      change Nat.card ((criticalActionSubgroup .d8).map
        dihedralPointEquiv.permCongrHom.toMonoidHom)=8
      rw [← Nat.card_congr E.toEquiv,criticalAction_group_card]
      rfl
    rw [hleft,BinaryChart16T1086.block1_base_card]

private theorem block1_block2_generators :
    BinaryChart16T1086.block1BaseGenerators =
      BinaryChart16T1086.block2BaseGenerators := by
  funext j
  apply Equiv.ext
  intro x
  revert x j
  decide +kernel

private theorem block1_block3_generators :
    BinaryChart16T1086.block1BaseGenerators =
      BinaryChart16T1086.block3BaseGenerators := by
  funext j
  apply Equiv.ext
  intro x
  revert x j
  decide +kernel

theorem dihedral_relabel_eq_block2 :
    relabelSubgroup dihedralPointEquiv (criticalActionSubgroup .d8) =
      Subgroup.closure (Set.range BinaryChart16T1086.block2BaseGenerators) := by
  rw [← block1_block2_generators]
  exact dihedral_relabel_eq_block1

theorem dihedral_relabel_eq_block3 :
    relabelSubgroup dihedralPointEquiv (criticalActionSubgroup .d8) =
      Subgroup.closure (Set.range BinaryChart16T1086.block3BaseGenerators) := by
  rw [← block1_block3_generators]
  exact dihedral_relabel_eq_block1

/-- A surjective literal block restriction is exactly one full coordinate
of an orbit profile.  This lemma retains the original ambient subgroup,
so different block coordinates may remain arbitrarily correlated. -/
theorem block_maps
    {X Y Ω ι : Type*} {s : ι → Equiv.Perm X}
    (C : PermutationBlockChart (Y := Y) s)
    (U : Subgroup (Equiv.Perm Ω)) (e : Ω ≃ Y)
    (he : relabelSubgroup e U=C.hom.range)
    (h : Subgroup.closure (Set.range s)) :
    ∃ u : U, ∀ x : Ω,
      (h : Equiv.Perm X) (C.embedding (e x)) =
        C.embedding (e ((u : Equiv.Perm Ω) x)) := by
  have hp : C.hom h ∈ relabelSubgroup e U := by
    rw [he]
    exact ⟨h,rfl⟩
  have hu : e.symm.permCongr (C.hom h) ∈ U :=
    (mem_relabelSubgroup e U (C.hom h)).mp hp
  refine ⟨⟨e.symm.permCongr (C.hom h),hu⟩,fun x => ?_⟩
  rw [C.hom_intertwine]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,
    Equiv.apply_symm_apply]

theorem block_full
    {X Y Ω ι : Type*} {s : ι → Equiv.Perm X}
    (C : PermutationBlockChart (Y := Y) s)
    (U : Subgroup (Equiv.Perm Ω)) (e : Ω ≃ Y)
    (he : relabelSubgroup e U=C.hom.range)
    (u : U) :
    ∃ h : Subgroup.closure (Set.range s), ∀ x : Ω,
      (h : Equiv.Perm X) (C.embedding (e x)) =
        C.embedding (e ((u : Equiv.Perm Ω) x)) := by
  have hp : e.permCongr (u : Equiv.Perm Ω) ∈ C.hom.range := by
    rw [← he]
    apply (mem_relabelSubgroup e U _).mpr
    have hh : e.symm.permCongr (e.permCongr (u : Equiv.Perm Ω))=
        (u : Equiv.Perm Ω) := by
      apply Equiv.ext
      intro x
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,
        Equiv.symm_apply_apply]
    rw [hh]
    exact u.property
  obtain ⟨h,hh⟩ := hp
  refine ⟨h,fun x => ?_⟩
  rw [C.hom_intertwine,hh]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]

/-- Every transported element acts through the same original block image;
the exterior coordinate is left untouched. -/
theorem transport_block_maps
    {Y Ω : Type*} {E : Type} [Group E]
    (C : PermutationBlockChart (Y := Y) BinaryChart16T1086.betaGenerators)
    (U : Subgroup (Equiv.Perm Ω)) (e : Ω ≃ Y)
    (he : relabelSubgroup e U=C.hom.range)
    (H : Subgroup (BinaryNormalTransport16T1086.chart.source×E))
    (z : BinaryNormalTransport16T1086.chart.transport H) :
    ∃ u : U, ∀ x : Ω,
      (z.1.1 : Equiv.Perm (Fin 16)) (C.embedding (e x)) =
        C.embedding (e ((u : Equiv.Perm Ω) x)) := by
  exact block_maps C U e he z.1.1

/-- Fullness of the transported carrier supplies a lift of every prescribed
local block action while retaining its arbitrary exterior correlation. -/
theorem transport_block_full
    {Y Ω : Type*} {E : Type} [Group E]
    (C : PermutationBlockChart (Y := Y) BinaryChart16T1086.betaGenerators)
    (U : Subgroup (Equiv.Perm Ω)) (e : Ω ≃ Y)
    (he : relabelSubgroup e U=C.hom.range)
    (H : Subgroup (BinaryNormalTransport16T1086.chart.source×E))
    (hfull : ∀ y : BinaryNormalTransport16T1086.chart.carrier,
      ∃ a : E, (y,a)∈BinaryNormalTransport16T1086.chart.transport H)
    (u : U) :
    ∃ z : BinaryNormalTransport16T1086.chart.transport H, ∀ x : Ω,
      (z.1.1 : Equiv.Perm (Fin 16)) (C.embedding (e x)) =
        C.embedding (e ((u : Equiv.Perm Ω) x)) := by
  obtain ⟨y,hy⟩ := block_full C U e he u
  obtain ⟨a,ha⟩ := hfull y
  exact ⟨⟨(y,a),ha⟩,hy⟩

namespace ExactProfile

open BinaryCarrierSmallSupportProfiles BinaryCarrierSmallSupportPhysical

/-- Three critical D8 orbits consume critical half-rank six. -/
def critical : CriticalProfile := ⟨0,0,3,0⟩

/-- The sole noncritical color is one original regular C4 occurrence. -/
def carrierMultiplicity : BinaryCarrierOriginalCyclicFourHall.Target → ℕ
  | none => 1
  | some _ => 0

theorem critical_mem : critical ∈ criticalProfiles 6 := by
  simp [critical,CriticalProfile.rank]

theorem carrier_support : support carrierMultiplicity=2 := by
  simp [carrierMultiplicity,support,BinaryCarrierOriginalSmallSupport.halfSupport,
    BinaryCarrierOriginalActions.scale]

def index : BinaryCarrierSmallSupportPhysical.ProfileIndex 6 2 :=
  ⟨⟨critical,critical_mem⟩,
    ⟨carrierMultiplicity,(mem_profilesAtSupport 2 carrierMultiplicity).mpr carrier_support⟩⟩

theorem carrier_parameters :
    carrierMultiplicity none=1 ∧
      BinaryCarrierOriginalActions.scale (fun t => carrierMultiplicity (some t))=0 := by
  constructor
  · rfl
  · simp [carrierMultiplicity,BinaryCarrierOriginalActions.scale]

/-- The same literal profile in the parameter coordinates used by the
complete mixture union: one C4 occurrence and no large carrier. -/
def parameterIndex : BinaryCarrierParameterProfiles.ProfileIndex 6 1 0 :=
  ⟨⟨critical,critical_mem⟩,
    ⟨carrierMultiplicity,
      (BinaryCarrierParameterProfiles.mem_profilesAtParameters 1 0
        carrierMultiplicity).mpr carrier_parameters⟩⟩

abbrev multiplicity : CriticalActionKind ⊕
    BinaryCarrierOriginalCyclicFourHall.Target → ℕ := fun i => match i with
  | Sum.inl .c2 => 0
  | Sum.inl .v4 => 0
  | Sum.inl .d8 => 3
  | Sum.inl .e8 => 0
  | Sum.inr none => 1
  | Sum.inr (some _) => 0

abbrev pointFamily : CriticalActionKind ⊕
    BinaryCarrierOriginalCyclicFourHall.Target → Type :=
  BinaryCarrierMixedProfile.points BinaryCarrierOriginalCyclicFourHall.points

abbrev actionFamily : (i : CriticalActionKind ⊕
    BinaryCarrierOriginalCyclicFourHall.Target) →
      Subgroup (Equiv.Perm (pointFamily i)) :=
  BinaryCarrierMixedProfile.action BinaryCarrierOriginalCyclicFourHall.points
    BinaryCarrierOriginalCyclicFourHall.action

local instance (i : CriticalActionKind ⊕
    BinaryCarrierOriginalCyclicFourHall.Target) : DecidableEq (pointFamily i) := by
  rcases i with i|t
  · rcases i with _|_|_|_ <;> dsimp [pointFamily,BinaryCarrierMixedProfile.points]
    <;> infer_instance
  · rcases t with _|t
    · dsimp [pointFamily,BinaryCarrierMixedProfile.points,
        BinaryCarrierOriginalCyclicFourHall.points]
      infer_instance
    · rcases t with t|m <;>
        dsimp [pointFamily,BinaryCarrierMixedProfile.points,
          BinaryCarrierOriginalCyclicFourHall.points,
          BinaryCarrierOriginalActions.points] <;> infer_instance

abbrev ModelPoints := OrbitProfilePoints pointFamily multiplicity

def cyclicModelPoint (x : Fin 4) : ModelPoints :=
  ⟨Sum.inr none,0,cyclicPointEquiv.symm x⟩

def dihedralModelPoint (j : Fin 3) (x : Fin 4) : ModelPoints :=
  ⟨Sum.inl .d8,j,dihedralPointEquiv.symm x⟩

local instance : Inhabited ModelPoints := ⟨cyclicModelPoint 0⟩

def chartFun : ModelPoints → Fin 16
  | ⟨Sum.inl .c2,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inl .v4,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inl .d8,j,x⟩ =>
      if h0 : j.val=0 then BinaryChart16T1086.block1.embedding (dihedralPointEquiv x)
      else if h1 : j.val=1 then
        BinaryChart16T1086.block2.embedding (dihedralPointEquiv x)
      else BinaryChart16T1086.block3.embedding (dihedralPointEquiv x)
  | ⟨Sum.inl .e8,j,_⟩ => Fin.elim0 j
  | ⟨Sum.inr none,_,x⟩ => BinaryChart16T1086.block0.embedding (cyclicPointEquiv x)
  | ⟨Sum.inr (some _),j,_⟩ => Fin.elim0 j

private def inverseTable : Array ModelPoints := #[
  cyclicModelPoint 0, cyclicModelPoint 3, cyclicModelPoint 2, cyclicModelPoint 1,
  dihedralModelPoint 0 0, dihedralModelPoint 0 3,
  dihedralModelPoint 0 1, dihedralModelPoint 0 2,
  dihedralModelPoint 1 0, dihedralModelPoint 1 3,
  dihedralModelPoint 1 1, dihedralModelPoint 1 2,
  dihedralModelPoint 2 0, dihedralModelPoint 2 3,
  dihedralModelPoint 2 1, dihedralModelPoint 2 2
]

def chart : ModelPoints ≃ Fin 16 where
  toFun := chartFun
  invFun x := inverseTable[x.val]!
  left_inv := by
    rintro ⟨i,j,x⟩
    rcases i with i|t
    · rcases i with _|_|_|_
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · obtain ⟨y,rfl⟩ := dihedralPointEquiv.symm.surjective x
        revert y j
        decide +kernel
      · exact Fin.elim0 j
    · rcases t with _|t
      · revert x j
        decide +kernel
      · exact Fin.elim0 j
  right_inv := by
    intro x
    revert x
    decide +kernel

@[simp] theorem chart_cyclic (x : ZMod 4) :
    chart ⟨Sum.inr none,0,x⟩ =
      BinaryChart16T1086.block0.embedding (cyclicPointEquiv x) := rfl

@[simp] theorem chart_dihedral_zero (x : criticalActionPoints .d8) :
    chart ⟨Sum.inl .d8,0,x⟩ =
      BinaryChart16T1086.block1.embedding (dihedralPointEquiv x) := by
  rfl

@[simp] theorem chart_dihedral_one (x : criticalActionPoints .d8) :
    chart ⟨Sum.inl .d8,1,x⟩ =
      BinaryChart16T1086.block2.embedding (dihedralPointEquiv x) := by
  rfl

@[simp] theorem chart_dihedral_two (x : criticalActionPoints .d8) :
    chart ⟨Sum.inl .d8,2,x⟩ =
      BinaryChart16T1086.block3.embedding (dihedralPointEquiv x) := by
  rfl

theorem indexed_multiplicity :
    BinaryCarrierSmallSupportPhysical.profileMultiplicity 6 2 index = multiplicity := by
  funext i
  rcases i with i|t
  · rcases i with _|_|_|_ <;> rfl
  · rcases t with _|t <;> rfl

theorem parameter_indexed_multiplicity :
    BinaryCarrierParameterProfiles.profileMultiplicity 6 1 0 parameterIndex = multiplicity := by
  funext i
  rcases i with i|t
  · rcases i with _|_|_|_ <;> rfl
  · rcases t with _|t <;> rfl

/-- The actual proper carrier is full on one original C4 block and three
critical D8 blocks.  Fullness is coordinatewise; no independence of the
four projections is asserted or used. -/
theorem carrier_full : OrbitProfileFullOn actionFamily chart
    BinaryNormalTransport16T1086.chart.carrier := by
  constructor
  · intro h i j
    rcases i with i|t
    · rcases i with _|_|_|_
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · fin_cases j
        · simpa only [chart_dihedral_zero] using
            block_maps BinaryChart16T1086.block1 (criticalActionSubgroup .d8)
              dihedralPointEquiv
              (dihedral_relabel_eq_block1.trans BinaryChart16T1086.block1_range.symm) h
        · simpa only [chart_dihedral_one] using
            block_maps BinaryChart16T1086.block2 (criticalActionSubgroup .d8)
              dihedralPointEquiv
              (dihedral_relabel_eq_block2.trans BinaryChart16T1086.block2_range.symm) h
        · simpa only [chart_dihedral_two] using
            block_maps BinaryChart16T1086.block3 (criticalActionSubgroup .d8)
              dihedralPointEquiv
              (dihedral_relabel_eq_block3.trans BinaryChart16T1086.block3_range.symm) h
      · exact Fin.elim0 j
    · rcases t with _|t
      · simpa only [chart_cyclic] using
          block_maps BinaryChart16T1086.block0 CyclicFourOriginal cyclicPointEquiv
            (cyclic_relabel_eq.trans BinaryChart16T1086.block0_range.symm) h
      · exact Fin.elim0 j
  · intro i j u
    rcases i with i|t
    · rcases i with _|_|_|_
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · fin_cases j
        · simpa only [chart_dihedral_zero] using
            block_full BinaryChart16T1086.block1 (criticalActionSubgroup .d8)
              dihedralPointEquiv
              (dihedral_relabel_eq_block1.trans BinaryChart16T1086.block1_range.symm) u
        · simpa only [chart_dihedral_one] using
            block_full BinaryChart16T1086.block2 (criticalActionSubgroup .d8)
              dihedralPointEquiv
              (dihedral_relabel_eq_block2.trans BinaryChart16T1086.block2_range.symm) u
        · simpa only [chart_dihedral_two] using
            block_full BinaryChart16T1086.block3 (criticalActionSubgroup .d8)
              dihedralPointEquiv
              (dihedral_relabel_eq_block3.trans BinaryChart16T1086.block3_range.symm) u
      · exact Fin.elim0 j
    · rcases t with _|t
      · simpa only [chart_cyclic] using
          block_full BinaryChart16T1086.block0 CyclicFourOriginal cyclicPointEquiv
            (cyclic_relabel_eq.trans BinaryChart16T1086.block0_range.symm) u
      · exact Fin.elim0 j

/-- The orbit-profile fullness statement on a reversibly transported
subgroup.  Its elements still contain their exterior coordinate, so this
records the mixed case rather than just the isolated carrier. -/
structure TransportProfileFull {E : Type} [Group E]
    (H : Subgroup (BinaryNormalTransport16T1086.chart.source×E)) : Prop where
  maps : ∀ z : BinaryNormalTransport16T1086.chart.transport H,
    ∀ i (j : Fin (multiplicity i)), ∃ u : actionFamily i, ∀ x,
      (z.1.1 : Equiv.Perm (Fin 16)) (chart ⟨i,j,x⟩) =
        chart ⟨i,j,(u : Equiv.Perm (pointFamily i)) x⟩
  full : ∀ i (j : Fin (multiplicity i)) (u : actionFamily i),
    ∃ z : BinaryNormalTransport16T1086.chart.transport H, ∀ x,
      (z.1.1 : Equiv.Perm (Fin 16)) (chart ⟨i,j,x⟩) =
        chart ⟨i,j,(u : Equiv.Perm (pointFamily i)) x⟩

/-- Reversible transport of every full original source preserves the entire
one-C4/three-D8 physical profile, with arbitrary exterior correlations. -/
theorem transport_profile_full {E : Type} [Group E]
    (H : Subgroup (BinaryNormalTransport16T1086.chart.source×E))
    (hfull : ∀ x : BinaryNormalTransport16T1086.chart.source,
      ∃ a : E, (x,a)∈H) : TransportProfileFull H := by
  have hc := BinaryNormalTransport16T1086.chart.transport_full_carrier H hfull
  constructor
  · intro z i j
    exact carrier_full.maps z.1.1 i j
  · intro i j u
    obtain ⟨y,hy⟩ := carrier_full.full i j u
    obtain ⟨a,ha⟩ := hc y
    exact ⟨⟨(y,a),ha⟩,hy⟩

/-- The catalogue's typed exceptional owner therefore carries the complete
physical profile through every later continuation, not only its C4 mark. -/
theorem _root_.SymmetricSubgroupAsymptotics.BinaryExceptional16CyclicOwner.AxisOwner.physicalProfile
    {N : Subgroup BinaryPairBinding16T1086.Original}
    (O : BinaryExceptional16CyclicOwner.AxisOwner N)
    {E : Type} [Group E]
    (H : Subgroup (BinaryNormalTransport16T1086.chart.source×E))
    (hfull : ∀ x : BinaryNormalTransport16T1086.chart.source,
      ∃ a : E, (x,a)∈H) : TransportProfileFull H := by
  exact transport_profile_full H hfull

/-- The proper carrier itself is already a literal member of the complete
physical family in the `(R,C)=(6,2)` bin. -/
private theorem assembledWitnessOfMultiplicityEq
    {m : CriticalActionKind ⊕ BinaryCarrierOriginalCyclicFourHall.Target → ℕ}
    (hm : m=multiplicity) :
    ∃ e : OrbitProfilePoints pointFamily m ≃ Fin 16, ∃ K,
      OrbitProfileFull (m := m) actionFamily 1 K ∧
        relabelSubgroup e K=BinaryNormalTransport16T1086.chart.carrier := by
  subst m
  let K := relabelSubgroup chart.symm BinaryNormalTransport16T1086.chart.carrier
  refine ⟨chart,K,?_,?_⟩
  · apply (orbitProfileFullOn_iff actionFamily 1 K).mp
    simpa only [Equiv.self_trans_symm] using carrier_full.relabel chart.symm
  · exact relabelSubgroup_symm chart.symm _

def carrierPhysicalFamily :
    BinaryCarrierSmallSupportPhysical.PhysicalFamily 6 2 (Fin 16) := by
  refine ⟨BinaryNormalTransport16T1086.chart.carrier,?_⟩
  refine ⟨index,?_⟩
  simpa only [BinaryCarrierSmallSupportPhysical.profilePredicate] using
    assembledWitnessOfMultiplicityEq indexed_multiplicity

/-- Parameter-bin form of the same membership, so the carrier enters the
final all-parameter physical union without a change of action or weight. -/
def carrierParameterPhysicalFamily :
    BinaryCarrierParameterProfiles.PhysicalFamily 6 1 0 (Fin 16) := by
  refine ⟨BinaryNormalTransport16T1086.chart.carrier,?_⟩
  refine ⟨parameterIndex,?_⟩
  simpa only [BinaryCarrierParameterProfiles.profilePredicate] using
    assembledWitnessOfMultiplicityEq parameter_indexed_multiplicity

end ExactProfile

end SymmetricSubgroupAsymptotics.BinaryExceptional16PhysicalProfile
