import SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedRetention
import SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge
import SymmetricSubgroupAsymptotics.BinaryDegree16PhysicalAnalyticClosure

/-!
# Numerically certified positive axis routing below width sixteen

The earlier routing theorems intentionally expose only an `AxisSlot` and a
positive-cell witness.  The retained-bin producer also needs the original
half-degree of that slot.  This file strengthens the owner-level routing
before the finite route constructor is erased.

In degree eight, a carrier owner gives a certified `(4,4)` slot unless it is
the genuine critical E8 action.  In degree sixteen, the two carrier owners
give certified `(8,2)` and `(8,8)` slots respectively.  Pullback through the
catalogue conjugacy changes no displayed cell, so the certificates remain on
the literal original action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS16CertifiedAxisRouting

open SymmetricSubgroupAsymptotics
open BinaryActionRegistry8
open BinaryCarrierCertifiedRetention
open BinaryCarrierS16RouteLocalCertificates
open BinaryDegreeEightBaseRoutes
open BinaryDegreeEightCarrierSourceBridge
open BinaryDegreeEightPhysicalAnalyticClosure

/-! ## Degree eight -/

/-- A degree-eight carrier owner still remembers enough finite-route data to
return either a certified positive slot on the literal action or the genuine
critical E8 action. -/
theorem degreeEightCarrierOwner_certified_or_e8
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal]
    (O : BinaryDegreeEightPhysicalAnalyticClosure.CarrierOwner U N) :
    Nonempty (CertifiedPositiveAxisSlot N 4) ∨ IsE8Action U := by
  rcases O with ⟨b,g,hg⟩ | ⟨i,g,hg,e,hsource,haxis⟩
  · by_cases hb : b = .e8
    · subst b
      right
      refine ⟨(basePointEquiv .e8).trans g.symm,?_⟩
      change relabelSubgroup g U = actions (baseIndex .e8) at hg
      calc
        relabelSubgroup ((basePointEquiv .e8).trans g.symm)
            (criticalActionSubgroup .e8) =
            relabelSubgroup g.symm
              (relabelSubgroup (basePointEquiv .e8)
                (criticalActionSubgroup .e8)) :=
          (relabelSubgroup_trans (basePointEquiv .e8) g.symm _).symm
        _ = relabelSubgroup g.symm (actions (baseIndex .e8)) := by
          exact congrArg (relabelSubgroup g.symm) (base_action_eq .e8)
        _ = relabelSubgroup g.symm (relabelSubgroup g U) := by rw [hg]
        _ = U := relabelSubgroup_symm g U
    · left
      obtain ⟨t,ht⟩ := (base_noncritical_or_e8 b).resolve_right hb
      let S := baseAxisSlot b g hg N
      refine ⟨CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)⟩
      · change S.HasNoncritical
        change ∃ c : Fin 1, ∃ t, baseKind b = .inr t
        exact ⟨0,t,ht⟩
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (degreeEightBase_certificate b hb g hg N)
  · left
    fin_cases e
    · let S := t16AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      refine ⟨CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)⟩
      · change S.HasNoncritical
        exact t16AxisSlot_hasNoncritical i hsource _ haxis
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t16AxisSlot_certificate i hsource _ haxis)
    · let S := t20AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      refine ⟨CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)⟩
      · change S.HasNoncritical
        exact t20AxisSlot_hasNoncritical i hsource _ haxis
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t20AxisSlot_certificate i hsource _ haxis)
    · let S := t21AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      refine ⟨CertifiedPositiveAxisSlot.ofCertificate
        (old := 4) (retained := 4)
        (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)⟩
      · change S.HasNoncritical
        exact t21AxisSlot_hasNoncritical i hsource _ haxis
      · exact Certificate.pullback (actionConjugacyEquiv g hg) S
          (t21AxisSlot_certificate i hsource _ haxis)

/-- Strengthened complete degree-eight interface: direct continuation,
certified positive carrier, or the critical E8 owner. -/
theorem degreeEight_complete_direct_or_certified_or_e8
    (U : Subgroup (Equiv.Perm (Fin 8))) (hU : IsPGroup 2 U)
    (ht : PermutationSubgroupTransitive U)
    (N : Subgroup U) [N.Normal] :
    BinaryDegreeEightPhysicalAnalyticClosure.DirectOwner U N ∨
      Nonempty (CertifiedPositiveAxisSlot N 4) ∨ IsE8Action U := by
  rcases BinaryDegreeEightPhysicalAnalyticClosure.complete_axis_analytic
      U hU ht N with hdirect | hcarrier
  · exact Or.inl hdirect
  · exact Or.inr (degreeEightCarrierOwner_certified_or_e8 hcarrier)

/-- On the unmarked degree-eight residual, every actual eligible orbit has a
certified positive slot or is intrinsically a critical E8 orbit. -/
theorem degreeEightCarrierResidual_certified_or_isE8Orbit
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ BinaryDegreeEightNormalizerSaturatedDirect.carrierResidualFamily n)
    (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H) :
    Nonempty (CertifiedPositiveAxisSlot W.axis 4) ∨
      IsE8Orbit W := by
  rcases degreeEightCarrierOwner_certified_or_e8
      (BinaryDegreeEightNormalizerSaturatedDirect.carrierResidual_all_witnesses
        hH W) with hslot | hE8
  · exact Or.inl hslot
  · exact Or.inr (isE8Orbit_of_isE8Action W hE8)

/-! ## Degree sixteen -/

/-- A degree-sixteen carrier owner produces a positive slot of half-degree
eight.  Its retained support is two on `16T1086` and eight on `16T1332`. -/
theorem degreeSixteenCarrierOwner_certified
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]
    (O : BinaryDegree16SplitAnalyticClosure.CarrierOwner U N) :
    Nonempty (CertifiedPositiveAxisSlot N 8) := by
  rcases O with ⟨g,hg,owner,_physical⟩ | ⟨g,hg,_row,_physical⟩
  · obtain ⟨owner⟩ := owner
    let S := BinaryDegree16CarrierRouting.t1086AxisSlot
      (actionConjugacyNormal g hg N) owner
    refine ⟨CertifiedPositiveAxisSlot.ofCertificate
      (old := 8) (retained := 2)
      (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)⟩
    · change S.HasNoncritical
      exact BinaryDegree16CarrierRouting.t1086AxisSlot_hasNoncritical _ owner
    · exact Certificate.pullback (actionConjugacyEquiv g hg) S
        (t1086AxisSlot_certificate _ owner)
  · let S := BinaryDegree16CarrierRouting.t1332AxisSlot
      (actionConjugacyNormal g hg N)
    letI : (actionConjugacyNormal g hg N).Normal :=
      actionConjugacyNormal_normal g hg N
    letI : (N.map (actionConjugacyEquiv g hg).toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ (actionConjugacyEquiv g hg).surjective
    refine ⟨CertifiedPositiveAxisSlot.ofCertificate
      (old := 8) (retained := 8)
      (S.pullback (actionConjugacyEquiv g hg) N) ?_ ?_ (by omega) (by omega)⟩
    · change S.HasNoncritical
      exact BinaryDegree16CarrierRouting.t1332AxisSlot_hasNoncritical _
    · exact Certificate.pullback (actionConjugacyEquiv g hg) S
        (t1332AxisSlot_certificate _)

/-- Strengthened complete degree-sixteen interface: direct continuation or a
numerically certified positive carrier slot. -/
theorem degreeSixteen_complete_direct_or_certified
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] :
    BinaryDegree16SplitAnalyticClosure.DirectOwner U N ∨
      Nonempty (CertifiedPositiveAxisSlot N 8) := by
  rcases
      (BinaryDegree16SplitAnalyticClosure.complete_axis_analytic U hU N).direct_or_carrier
      with hdirect | hcarrier
  · exact Or.inl hdirect
  · exact Or.inr (degreeSixteenCarrierOwner_certified hcarrier)

/-- On the unmarked degree-sixteen residual, every eligible orbit supplies a
numerically certified positive slot. -/
theorem degreeSixteenCarrierResidual_all_certified
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ BinaryDegree16PhysicalAnalyticClosure.carrierResidualFamily n)
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H) :
    Nonempty (CertifiedPositiveAxisSlot W.axis 8) :=
  degreeSixteenCarrierOwner_certified
    (BinaryDegree16PhysicalAnalyticClosure.carrierResidual_all_witnesses hH W)

end SymmetricSubgroupAsymptotics.BinaryCarrierS16CertifiedAxisRouting

end
