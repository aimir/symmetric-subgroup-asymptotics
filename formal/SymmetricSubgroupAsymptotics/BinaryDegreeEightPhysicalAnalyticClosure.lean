import SymmetricSubgroupAsymptotics.BinaryDegreeEightBaseRoutes
import SymmetricSubgroupAsymptotics.BinaryFiniteEntryCoverage8
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginal

/-!
# Physical analytic closure in degree eight

Every normal axis in every transitive binary permutation action of degree
eight reaches one of the two consumers used by the final recurrence.  Pair
and character certificates are direct original-weight owners.  The eight
base actions become unchanged source-alphabet slots, with the actual normal
pulled back through the displayed point relabelling.  The remaining carrier
branches retain one of the three checked reversible charts, including its
literal source and ambient axis equations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalAnalyticClosure

open SymmetricSubgroupAsymptotics
open BinaryActionRegistry8
open BinaryNormalCoverage8
open BinaryDegreeEightBaseRoutes
open BinaryCarrierProfileTransport
open BinaryCarrierMenuSlots
open BinaryCarrierWordClosure

/-! ## The unchanged base actions -/

/-- The displayed point relabelling is an equivalence from the literal
mixture colour to the corresponding degree-eight registry action. -/
def baseActionEquiv (b : Base) :
    mixtureAction (baseKind b) ≃* actions (baseIndex b) :=
  ((mixtureAction (baseKind b)).equivMapOfInjective
      (basePointEquiv b).permCongrHom.toMonoidHom
      (basePointEquiv b).permCongrHom.injective).trans
    (MulEquiv.subgroupCongr (base_action_eq b))

/-- Pull an actual transported normal axis back to the unchanged mixture
colour.  This is the normal used by its quotient-identity source slot. -/
def baseAlphabetAxis {U : Subgroup (Equiv.Perm (Fin 8))}
    (b : Base) (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • U = actions (baseIndex b))
    (N : Subgroup U) : Subgroup (mixtureAction (baseKind b)) :=
  (actionConjugacyNormal g hg N).map (baseActionEquiv b).symm.toMonoidHom

instance baseAlphabetAxis_normal {U : Subgroup (Equiv.Perm (Fin 8))}
    (b : Base) (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • U = actions (baseIndex b))
    (N : Subgroup U) [N.Normal] : (baseAlphabetAxis b g hg N).Normal :=
  Subgroup.Normal.map inferInstance _ (baseActionEquiv b).symm.surjective

/-- Forward transport recovers the exact conjugated original normal. -/
theorem baseAlphabetAxis_map {U : Subgroup (Equiv.Perm (Fin 8))}
    (b : Base) (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • U = actions (baseIndex b))
    (N : Subgroup U) [N.Normal] :
    (baseAlphabetAxis b g hg N).map (baseActionEquiv b).toMonoidHom =
      actionConjugacyNormal g hg N := by
  rw [baseAlphabetAxis,Subgroup.map_map]
  simpa using Subgroup.map_id (actionConjugacyNormal g hg N)

/-- The eight omitted indices are exactly the images of `Base`. -/
theorem mem_baseIndices_iff (i : Fin 26) :
    i ∈ baseIndices ↔ ∃ b : Base, baseIndex b = i := by
  revert i
  decide +kernel

/-! ## Uniform exact-axis slots -/

/-- A local carrier slot together with an equivalence from an original
action and the exact equality between the transported normal and the slot
quotient kernel.  This is the interface consumed by a simultaneous source
word; it adds no marked data to the subgroup being counted. -/
structure AxisSlot (A : Type) [Group A] (N : Subgroup A) where
  slot : Slot.{0,0,0}
  sourceEquiv : A ≃* slot.Source
  kernel : N.map sourceEquiv.toMonoidHom = slot.alpha.ker

namespace AxisSlot

/-- A routed slot displays at least one noncritical original-action colour.
This is the exact positivity guard required by the completed mixture. -/
def HasNoncritical {A : Type} [Group A] {N : Subgroup A}
    (S : AxisSlot A N) : Prop :=
  ∃ c : S.slot.Cells, ∃ t, S.slot.color c = .inr t

/-- Every displayed cell is the sole critical base colour which can survive
without positive mixture support. -/
def IsPureE8 {A : Type} [Group A] {N : Subgroup A}
    (S : AxisSlot A N) : Prop :=
  ∀ c : S.slot.Cells, S.slot.color c = .inl .e8

/-- Pull an exact-axis slot back through an equivalence of original source
groups. -/
def pullback {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (N : Subgroup A)
    (S : AxisSlot B (N.map e.toMonoidHom)) : AxisSlot A N where
  slot := S.slot
  sourceEquiv := e.trans S.sourceEquiv
  kernel := by
    change N.map (S.sourceEquiv.toMonoidHom.comp e.toMonoidHom) = S.slot.alpha.ker
    rw [← Subgroup.map_map]
    exact S.kernel

end AxisSlot

/-- A base owner is literally the quotient-identity slot on its pulled-back
normal axis. -/
def baseAxisSlot {U : Subgroup (Equiv.Perm (Fin 8))}
    (b : Base) (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • U = actions (baseIndex b))
    (N : Subgroup U) [N.Normal] :
    AxisSlot (actions (baseIndex b)) (actionConjugacyNormal g hg N) where
  slot := quotientIdentitySlot (baseKind b) (baseAlphabetAxis b g hg N)
  sourceEquiv := (baseActionEquiv b).symm
  kernel := by
    change baseAlphabetAxis b g hg N =
      (quotientIdentitySlot (baseKind b) (baseAlphabetAxis b g hg N)).alpha.ker
    exact (quotientIdentitySlot_alpha_ker
      (baseKind b) (baseAlphabetAxis b g hg N)).symm

/-- Every base slot is either visibly noncritical or the unique critical E8
identity slot. -/
theorem baseAxisSlot_classified {U : Subgroup (Equiv.Perm (Fin 8))}
    (b : Base) (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • U = actions (baseIndex b))
    (N : Subgroup U) [N.Normal] :
    (baseAxisSlot b g hg N).HasNoncritical ∨
      (baseAxisSlot b g hg N).IsPureE8 := by
  cases b with
  | t18 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t18 = .inr t
      exact ⟨0,some (.degree8 .t18),rfl⟩
  | e8 =>
      right
      change ∀ c : Fin 1, baseKind .e8 = .inl .e8
      exact fun _ => rfl
  | t26 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t26 = .inr t
      exact ⟨0,some (.degree8 .t26),rfl⟩
  | t27 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t27 = .inr t
      exact ⟨0,some (.degree8 .t27),rfl⟩
  | t28 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t28 = .inr t
      exact ⟨0,some (.degree8 .t28),rfl⟩
  | t29 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t29 = .inr t
      exact ⟨0,some (.degree8 .t29),rfl⟩
  | t31 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t31 = .inr t
      exact ⟨0,some (.degree8 .t31),rfl⟩
  | t35 =>
      left
      change ∃ c : Fin 1, ∃ t, baseKind .t35 = .inr t
      exact ⟨0,some (.degree8 .t35),rfl⟩

/-- The three finite-entry carrier labels in source-alphabet notation. -/
def exceptionalKind : Fin 3 → Exceptional
  | 0 => .t16
  | 1 => .t20
  | 2 => .t21

/-- Transport a kernel through a group equivalence.  This is the generic
kernel bridge used by every checked carrier chart, independently of its
physical degree. -/
theorem AxisSlot.map_equiv_eq_ker_of_comp_ker
    {A B Q : Type*} [Group A] [Group B] [Group Q]
    (e : A ≃* B) (α : B →* Q) (M : Subgroup A)
    (hker : (α.comp e.toMonoidHom).ker = M) :
    M.map e.toMonoidHom = α.ker := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    change α (e a) = 1
    have ha' : a ∈ (α.comp e.toMonoidHom).ker := hker.symm ▸ ha
    exact ha'
  · intro hb
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    rw [← hker]
    change α (e (e.symm b)) = 1
    simpa using hb

/-- The `8T16` transport is an exact source-alphabet slot. -/
def t16AxisSlot (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T16.Source = actions i)
    (M : Subgroup (actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T16.chart.axis =
      M.map (actions i).subtype) : AxisSlot (actions i) M where
  slot := t16Slot
  sourceEquiv := (MulEquiv.subgroupCongr source).symm
  kernel := by
    exact AxisSlot.map_equiv_eq_ker_of_comp_ker
      (BinaryExceptional8ProfileCarriers.T16.chart.originalSourceEquiv source)
      BinaryExceptional8ProfileCarriers.T16.alpha M
      (BinaryExceptional8ProfileCarriers.T16.chart.originalAlpha_kernel
        source M axis)

/-- The `8T20` transport is an exact source-alphabet slot. -/
def t20AxisSlot (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T20.Source = actions i)
    (M : Subgroup (actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T20.chart.axis =
      M.map (actions i).subtype) : AxisSlot (actions i) M where
  slot := t20Slot
  sourceEquiv := (MulEquiv.subgroupCongr source).symm
  kernel := by
    exact AxisSlot.map_equiv_eq_ker_of_comp_ker
      (BinaryExceptional8ProfileCarriers.T20.chart.originalSourceEquiv source)
      BinaryExceptional8ProfileCarriers.T20.alpha M
      (BinaryExceptional8ProfileCarriers.T20.chart.originalAlpha_kernel
        source M axis)

/-- The `8T21` transport is an exact source-alphabet slot. -/
def t21AxisSlot (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T21.Source = actions i)
    (M : Subgroup (actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T21.chart.axis =
      M.map (actions i).subtype) : AxisSlot (actions i) M where
  slot := t21Slot
  sourceEquiv := (MulEquiv.subgroupCongr source).symm
  kernel := by
    exact AxisSlot.map_equiv_eq_ker_of_comp_ker
      (BinaryExceptional8ProfileCarriers.T21.chart.originalSourceEquiv source)
      BinaryExceptional8ProfileCarriers.T21.alpha M
      (BinaryExceptional8ProfileCarriers.T21.chart.originalAlpha_kernel
        source M axis)

theorem t16AxisSlot_hasNoncritical (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T16.Source = actions i)
    (M : Subgroup (actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T16.chart.axis =
      M.map (actions i).subtype) :
    (t16AxisSlot i source M axis).HasNoncritical :=
  exceptional_has_noncritical .t16

theorem t20AxisSlot_hasNoncritical (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T20.Source = actions i)
    (M : Subgroup (actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T20.chart.axis =
      M.map (actions i).subtype) :
    (t20AxisSlot i source M axis).HasNoncritical :=
  exceptional_has_noncritical .t20

theorem t21AxisSlot_hasNoncritical (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T21.Source = actions i)
    (M : Subgroup (actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T21.chart.axis =
      M.map (actions i).subtype) :
    (t21AxisSlot i source M axis).HasNoncritical :=
  exceptional_has_noncritical .t21

/-! ## The complete owner split -/

/-- Direct original-weight degree-eight owners.  The same ambient
conjugation transports both the action and its literal normal axis. -/
inductive DirectOwner
    (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] : Prop
  | pair (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions i)
      (certificate : Nonempty (BinaryPhysicalPairCertificate (actions i)
        (actionConjugacyNormal g hg N)))
  | character (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions i)
      (criterion : Nonempty (BinaryNormalCharacterCriterion
        (actions i ⧸ actionConjugacyNormal g hg N) 8))

/-- Carrier-mixture degree-eight owners.  A base owner supplies an unchanged
source-alphabet colour and its exact pulled-back normal.  An exceptional
owner retains the checked source and ambient-axis equations verbatim. -/
inductive CarrierOwner
    (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] : Prop
  | base (b : Base) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions (baseIndex b))
  | exceptional (i : Fin 26) (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • U = actions i) (e : Fin 3)
      (source : (binaryEightTransportChart e).source = actions i)
      (axis : (binaryEightTransportChart e).axis =
        (actionConjugacyNormal g hg N).map (actions i).subtype)

/-- A carrier owner rewritten in the uniform exact-axis slot interface. -/
structure RoutedCarrier
    (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] where
  index : Fin 26
  conjugator : Equiv.Perm (Fin 8)
  conjugated : MulAut.conj conjugator • U = actions index
  axisSlot : AxisSlot (actions index)
    (actionConjugacyNormal conjugator conjugated N)

/-- The routed slot pulled back to the actual original degree-eight action. -/
def RoutedCarrier.originalAxisSlot
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal] (O : RoutedCarrier U N) : AxisSlot U N :=
  O.axisSlot.pullback (actionConjugacyEquiv O.conjugator O.conjugated) N

/-- Both base and exceptional carrier owners produce an exact source slot;
the quotient kernel is the transported literal original normal. -/
theorem CarrierOwner.routed
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal] (O : CarrierOwner U N) :
    Nonempty (RoutedCarrier U N) := by
  rcases O with ⟨b,g,hg⟩ | ⟨i,g,hg,e,hsource,haxis⟩
  · exact ⟨{
      index := baseIndex b
      conjugator := g
      conjugated := hg
      axisSlot := baseAxisSlot b g hg N }⟩
  · fin_cases e
    · exact ⟨{
        index := i
        conjugator := g
        conjugated := hg
        axisSlot := t16AxisSlot i hsource
          (actionConjugacyNormal g hg N) haxis }⟩
    · exact ⟨{
        index := i
        conjugator := g
        conjugated := hg
        axisSlot := t20AxisSlot i hsource
          (actionConjugacyNormal g hg N) haxis }⟩
    · exact ⟨{
        index := i
        conjugator := g
        conjugated := hg
        axisSlot := t21AxisSlot i hsource
          (actionConjugacyNormal g hg N) haxis }⟩

/-- A degree-eight carrier owner retains its exact slot together with the
complete support classification: positive noncritical support, or pure E8. -/
theorem CarrierOwner.classifiedAxisSlot
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal] (O : CarrierOwner U N) :
    Nonempty {S : AxisSlot U N // S.HasNoncritical ∨ S.IsPureE8} := by
  rcases O with ⟨b,g,hg⟩ | ⟨i,g,hg,e,hsource,haxis⟩
  · let S := baseAxisSlot b g hg N
    refine ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,?_⟩⟩
    exact baseAxisSlot_classified b g hg N
  · fin_cases e
    · let S := t16AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      exact ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,
        Or.inl (t16AxisSlot_hasNoncritical i hsource _ haxis)⟩⟩
    · let S := t20AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      exact ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,
        Or.inl (t20AxisSlot_hasNoncritical i hsource _ haxis)⟩⟩
    · let S := t21AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      exact ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,
        Or.inl (t21AxisSlot_hasNoncritical i hsource _ haxis)⟩⟩

/-- The two analytic destinations used by the global degree-eight assembly. -/
abbrev AnalyticOwner
    (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] : Prop :=
  DirectOwner U N ∨ CarrierOwner U N

/-- Complete finite and analytic closure for every literal normal axis of
every transitive binary degree-eight action. -/
theorem complete_axis_analytic
    (U : Subgroup (Equiv.Perm (Fin 8))) (hU : IsPGroup 2 U)
    (ht : PermutationSubgroupTransitive U)
    (N : Subgroup U) [N.Normal] : AnalyticOwner U N := by
  obtain ⟨i,g,hg,howner,_hweight⟩ :=
    BinaryFiniteEntryCoverage8.complete U hU ht N
  rcases howner with hbase | hentry
  · obtain ⟨b,hb⟩ := (mem_baseIndices_iff i).mp hbase
    subst i
    exact Or.inr (.base b g hg)
  · rcases hentry with hpair | hrest
    · exact Or.inl (.pair i g hg hpair)
    · rcases hrest with hcharacter | hcarrier
      · exact Or.inl (.character i g hg hcharacter)
      · obtain ⟨e,hsource,haxis⟩ := hcarrier
        exact Or.inr (.exceptional i g hg e hsource haxis)

/-- Counting-ready form: every degree-eight axis is either direct or already
packaged as one exact routed carrier slot. -/
theorem complete_axis_direct_or_routed
    (U : Subgroup (Equiv.Perm (Fin 8))) (hU : IsPGroup 2 U)
    (ht : PermutationSubgroupTransitive U)
    (N : Subgroup U) [N.Normal] :
    DirectOwner U N ∨ Nonempty (RoutedCarrier U N) := by
  rcases complete_axis_analytic U hU ht N with hdirect | hcarrier
  · exact Or.inl hdirect
  · exact Or.inr hcarrier.routed

/-- Final local interface on the unchanged original action. -/
theorem complete_axis_direct_or_slot
    (U : Subgroup (Equiv.Perm (Fin 8))) (hU : IsPGroup 2 U)
    (ht : PermutationSubgroupTransitive U)
    (N : Subgroup U) [N.Normal] :
    DirectOwner U N ∨ Nonempty (AxisSlot U N) := by
  rcases complete_axis_direct_or_routed U hU ht N with hdirect | hrouted
  · exact Or.inl hdirect
  · obtain ⟨R⟩ := hrouted
    exact Or.inr ⟨R.originalAxisSlot⟩

/-- Final support-sensitive degree-eight interface. -/
theorem complete_axis_direct_or_classified_slot
    (U : Subgroup (Equiv.Perm (Fin 8))) (hU : IsPGroup 2 U)
    (ht : PermutationSubgroupTransitive U)
    (N : Subgroup U) [N.Normal] :
    DirectOwner U N ∨
      Nonempty {S : AxisSlot U N // S.HasNoncritical ∨ S.IsPureE8} := by
  rcases complete_axis_analytic U hU ht N with hdirect | hcarrier
  · exact Or.inl hdirect
  · exact Or.inr hcarrier.classifiedAxisSlot

end SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalAnalyticClosure
