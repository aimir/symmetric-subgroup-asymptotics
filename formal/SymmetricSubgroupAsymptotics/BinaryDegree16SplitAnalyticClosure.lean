import SymmetricSubgroupAsymptotics.BinaryDegree16SplitCatalogueOwners
import SymmetricSubgroupAsymptotics.BinaryCarrierMixtureCompletion

/-!
# Analytic closure of the degree-sixteen split frontier

Every catalogue branch now terminates in one of the two analytic consumers
used by the binary recurrence: a direct accepted entry, or the complete
original-action carrier-mixture family.  The 16T1086 branch retains its
typed reversible-axis owner, while the 16T1332 branch retains its normal-row
master envelope.  No catalogue identifier is used as a counting premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegree16SplitAnalyticClosure

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitFrontier
open BinaryDegree16SplitCatalogueOwners
open FullSubdirectGoursat JointCapacityRow BinaryCarrierMasterMenu
open BinaryCarrierMasterEnvelopes

/-- The proper 16T1086 carrier in the final all-parameter mixture union. -/
def t1086MixtureFamily : BinaryCarrierMixtureCompletion.Family 8 := by
  let b : BinaryCarrierParameterUnion.bins 8 (fun _ _ => True) :=
    ⟨(1,0),by simp [BinaryCarrierParameterUnion.mem_bins]⟩
  refine ⟨BinaryNormalTransport16T1086.chart.carrier,b,
    BinaryExceptional16PhysicalProfile.ExactProfile.carrierParameterPhysicalFamily,?_⟩
  rfl

/-- Any literal 16T1332 profile certificate in its `(R,a,T)=(0,0,2)`
bin enters the final all-parameter mixture union. -/
def t1332MixtureFamily
    (P : BinaryCarrierParameterProfiles.PhysicalFamily 0 0 2 (Fin 16)) :
    BinaryCarrierMixtureCompletion.Family 8 := by
  let b : BinaryCarrierParameterUnion.bins 8 (fun _ _ => True) :=
    ⟨(0,2),by simp [BinaryCarrierParameterUnion.mem_bins]⟩
  refine ⟨P.1,b,P,?_⟩
  rfl

/-- Counting-ready endpoint for an original degree-sixteen normal axis.
The direct constructors retain the actual conjugacy and transported normal.
The carrier constructors retain the exact physical subgroup occurring in
the globally negligible mixture family. -/
inductive AnalyticOwner
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop
  | accepted (owner : AcceptedAxis U N)
  | direct1098 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1098.Original)
      (entry : Nonempty (AcceptedEntry BinaryPairBinding16T1098.Original
        (actionConjugacyNormal g hg N)))
  | direct1086 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1086.Original)
      (entry : Nonempty (AcceptedEntry BinaryPairBinding16T1086.Original
        (actionConjugacyNormal g hg N)))
  | carrier1086 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1086.Original)
      (owner : Nonempty (BinaryExceptional16CyclicOwner.AxisOwner
        (actionConjugacyNormal g hg N)))
      (physical : ∃ H : BinaryCarrierMixtureCompletion.Family 8,
        H.1=BinaryNormalTransport16T1086.chart.carrier)
  | carrier1332 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinarySelectedCatalogue16T1332.Original)
      (row : ∃ label : Label,
        (BinaryCarrierWord.actualRow
          (A := BinaryCarrierMasterEnvelopeCoverage16T1332.factor)
          ⟨actionConjugacyNormal g hg N,
            actionConjugacyNormal_normal g hg N⟩).EffectivelyBoundedBy
              (envelope label))
      (physical : ∃ H : BinaryCarrierMixtureCompletion.Family 8, H.1=U)

/-- The three constructors which feed a strict original-weight continuation
row.  Catalogue conjugacies and transported literal normals remain part of
the certificate. -/
inductive DirectOwner
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop
  | accepted (owner : AcceptedAxis U N)
  | t1098 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1098.Original)
      (entry : Nonempty (AcceptedEntry BinaryPairBinding16T1098.Original
        (actionConjugacyNormal g hg N)))
  | t1086 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1086.Original)
      (entry : Nonempty (AcceptedEntry BinaryPairBinding16T1086.Original
        (actionConjugacyNormal g hg N)))

/-- The two constructors which feed the completed finite-alphabet carrier
mixture.  The 16T1086 branch retains its reversible-axis certificate and the
16T1332 branch retains its effective master-envelope row. -/
inductive CarrierOwner
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop
  | t1086 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1086.Original)
      (owner : Nonempty (BinaryExceptional16CyclicOwner.AxisOwner
        (actionConjugacyNormal g hg N)))
      (physical : ∃ H : BinaryCarrierMixtureCompletion.Family 8,
        H.1=BinaryNormalTransport16T1086.chart.carrier)
  | t1332 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinarySelectedCatalogue16T1332.Original)
      (row : ∃ label : Label,
        (BinaryCarrierWord.actualRow
          (A := BinaryCarrierMasterEnvelopeCoverage16T1332.factor)
          ⟨actionConjugacyNormal g hg N,
            actionConjugacyNormal_normal g hg N⟩).EffectivelyBoundedBy
              (envelope label))
      (physical : ∃ H : BinaryCarrierMixtureCompletion.Family 8, H.1=U)

/-- The analytic five-way result is exactly the disjoint pair of consumers
needed by the final assembly: direct continuation or carrier mixture. -/
theorem AnalyticOwner.direct_or_carrier
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]
    (O : AnalyticOwner U N) : DirectOwner U N ∨ CarrierOwner U N := by
  rcases O with accepted | ⟨g,hg,entry⟩ | ⟨g,hg,entry⟩ |
      ⟨g,hg,owner,physical⟩ | ⟨g,hg,row,physical⟩
  · exact Or.inl (.accepted accepted)
  · exact Or.inl (.t1098 g hg entry)
  · exact Or.inl (.t1086 g hg entry)
  · exact Or.inr (.t1086 g hg owner physical)
  · exact Or.inr (.t1332 g hg row physical)

/-- The catalogue alternatives all have exact analytic destinations. -/
theorem of_completeOwner
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]
    (O : CompleteOwner U N) : AnalyticOwner U N := by
  rcases O with accepted | catalogue
  · exact .accepted accepted
  · rcases catalogue with ⟨g,hg,entry⟩ | ⟨g,hg,owner⟩ |
      ⟨g,hg,row,profile,profile_eq⟩
    · exact .direct1098 g hg entry
    · rcases owner with direct | carrier
      · exact .direct1086 g hg direct
      · exact .carrier1086 g hg carrier ⟨t1086MixtureFamily,rfl⟩
    · exact .carrier1332 g hg row ⟨t1332MixtureFamily profile,profile_eq⟩

/-- Complete finite closure for every literal normal axis of every
transitive binary degree-sixteen action. -/
theorem complete_axis_analytic
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] : AnalyticOwner U N :=
  of_completeOwner (complete_axis_owner U hU N)

end SymmetricSubgroupAsymptotics.BinaryDegree16SplitAnalyticClosure
