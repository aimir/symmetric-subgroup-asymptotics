import SymmetricSubgroupAsymptotics.BinaryDegree16SplitAnalyticClosure
import SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalAnalyticClosure

/-!
# Exact carrier routing for degree sixteen

Both surviving degree-sixteen carrier branches enter the same exact-axis
slot interface used by the degree-eight closure.  The proper 16T1086 branch
uses its checked four-cell reversible carrier.  The 16T1332 branch is already
one literal noncritical colour of the completed original-action alphabet, so
it uses the quotient-identity slot on its transported normal.

The resulting local theorem has only the two consumers needed by the global
recurrence: a direct original-weight owner or an exact reversible slot on the
unchanged original action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegree16CarrierRouting

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitAnalyticClosure
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryCarrierMenuSlots

/-! ## The proper 16T1086 route -/

/-- The checked 16T1086 chart, rewritten as an exact source-axis slot on its
literal original action. -/
def t1086AxisSlot
    (M : Subgroup BinaryPairBinding16T1086.Original) [M.Normal]
    (O : BinaryExceptional16CyclicOwner.AxisOwner M) :
    AxisSlot BinaryPairBinding16T1086.Original M where
  slot := E1086.slot
  sourceEquiv :=
    BinaryNormalTransport16T1086.chart.originalSourceEquiv O.source_eq
  kernel := by
    exact AxisSlot.map_equiv_eq_ker_of_comp_ker
      (BinaryNormalTransport16T1086.chart.originalSourceEquiv O.source_eq)
      BinaryExceptional16ProfileCarrier.alpha M
      (BinaryNormalTransport16T1086.chart.originalAlpha_kernel
        O.source_eq M O.axis_eq)

theorem t1086AxisSlot_hasNoncritical
    (M : Subgroup BinaryPairBinding16T1086.Original) [M.Normal]
    (O : BinaryExceptional16CyclicOwner.AxisOwner M) :
    (t1086AxisSlot M O).HasNoncritical := by
  exact exceptional_has_noncritical .t1086

/-! ## The unchanged 16T1332 colour -/

/-- The literal completed-alphabet colour occupied by 16T1332. -/
abbrev t1332Kind : BinaryCarrierProfileTransport.MixtureKind :=
  .inr (some (.degree16 .t1332))

/-- The selected catalogue action is definitionally the original action of
the 16T1332 alphabet colour. -/
def t1332ActionEquiv :
    BinarySelectedCatalogue16T1332.Original ≃*
      BinaryCarrierProfileTransport.mixtureAction t1332Kind :=
  MulEquiv.refl _

/-- An arbitrary literal 16T1332 normal is an unchanged source-alphabet
slot.  Its quotient kernel is exactly the transported normal. -/
def t1332AxisSlot
    (M : Subgroup BinarySelectedCatalogue16T1332.Original) [M.Normal] :
    AxisSlot BinarySelectedCatalogue16T1332.Original M := by
  let L : Subgroup (BinaryCarrierProfileTransport.mixtureAction t1332Kind) :=
    M.map t1332ActionEquiv.toMonoidHom
  letI : L.Normal := Subgroup.Normal.map inferInstance _ t1332ActionEquiv.surjective
  refine {
    slot := quotientIdentitySlot t1332Kind L
    sourceEquiv := t1332ActionEquiv
    kernel := ?_ }
  exact (quotientIdentitySlot_alpha_ker t1332Kind L).symm

theorem t1332AxisSlot_hasNoncritical
    (M : Subgroup BinarySelectedCatalogue16T1332.Original) [M.Normal] :
    (t1332AxisSlot M).HasNoncritical := by
  change ∃ c : Fin 1, ∃ t, t1332Kind = .inr t
  exact ⟨0,some (.degree16 .t1332),rfl⟩

/-! ## Uniform local closure -/

/-- Every degree-sixteen carrier owner supplies an exact slot on the original
action.  Catalogue conjugation is incorporated into the slot equivalence and
does not become counted marking data. -/
theorem CarrierOwner.axisSlot
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal] (O : CarrierOwner U N) :
    Nonempty (AxisSlot U N) := by
  rcases O with ⟨g,hg,owner,_physical⟩ |
      ⟨g,hg,_row,_physical⟩
  · obtain ⟨owner⟩ := owner
    exact ⟨(t1086AxisSlot (actionConjugacyNormal g hg N) owner).pullback
      (actionConjugacyEquiv g hg) N⟩
  · exact ⟨(t1332AxisSlot (actionConjugacyNormal g hg N)).pullback
      (actionConjugacyEquiv g hg) N⟩

/-- Every degree-sixteen carrier route supplies positive noncritical support
as well as the exact original-axis slot. -/
theorem CarrierOwner.supportedAxisSlot
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal] (O : CarrierOwner U N) :
    Nonempty {S : AxisSlot U N // S.HasNoncritical} := by
  rcases O with ⟨g,hg,owner,_physical⟩ |
      ⟨g,hg,_row,_physical⟩
  · obtain ⟨owner⟩ := owner
    let S := t1086AxisSlot (actionConjugacyNormal g hg N) owner
    refine ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,?_⟩⟩
    exact t1086AxisSlot_hasNoncritical _ owner
  · let S := t1332AxisSlot (actionConjugacyNormal g hg N)
    refine ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,?_⟩⟩
    exact t1332AxisSlot_hasNoncritical _

/-- Final degree-sixteen local interface: direct continuation or one exact
reversible carrier slot on the unchanged original action. -/
theorem complete_axis_direct_or_slot
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] :
    DirectOwner U N ∨ Nonempty (AxisSlot U N) := by
  rcases (complete_axis_analytic U hU N).direct_or_carrier with
      hdirect | hcarrier
  · exact Or.inl hdirect
  · exact Or.inr (CarrierOwner.axisSlot hcarrier)

/-- Strengthened local interface with the positive-support witness retained. -/
theorem complete_axis_direct_or_supported_slot
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] :
    DirectOwner U N ∨
      Nonempty {S : AxisSlot U N // S.HasNoncritical} := by
  rcases (complete_axis_analytic U hU N).direct_or_carrier with
      hdirect | hcarrier
  · exact Or.inl hdirect
  · exact Or.inr (CarrierOwner.supportedAxisSlot hcarrier)

end SymmetricSubgroupAsymptotics.BinaryDegree16CarrierRouting
