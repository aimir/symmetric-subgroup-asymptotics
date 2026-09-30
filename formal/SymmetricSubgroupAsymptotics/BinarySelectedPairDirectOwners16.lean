import SymmetricSubgroupAsymptotics.BinaryPhysicalPairAcceptedEntry16
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotAcceptance16T1086
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotAcceptance16T1098
import SymmetricSubgroupAsymptotics.BinaryNormalTransport16

/-!
# Direct owners for the selected degree-sixteen pair actions

The property-preserving finite selector retains even top-cover degree.
Consequently every 16T1098 axis and every nonexceptional 16T1086 axis is a
direct recurrence entry.  The only surviving 16T1086 alternative is the
literal checked reversible carrier.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySelectedPairDirectOwners16

open BinaryDegree16SplitFrontier

namespace T1098
open BinaryPairBinding16T1098

/-- Every normal axis has a physical certificate whose chosen top cover is
even.  The nominal exceptional predicate for this registry is empty. -/
theorem physical_pair_even (N : Subgroup Original) [N.Normal] :
    ∃ C : BinaryPhysicalPairCertificate Original N,
      Even C.localCertificate.coverDegree := by
  rcases BinaryPairAcceptance16T1098.accepted_or_exceptional_even N with
      ⟨C,hwidth,heven⟩ | ⟨i,hi,_⟩
  · exact ⟨BinaryPhysicalPairCertificate.ofLocal physicalFrame generators
      generators_full C (by simpa only [Nat.card_fin] using hwidth),heven⟩
  · have hfalse : False := by
      simpa [BinaryKernelGaps077.exceptionalAxis] using hi
    exact hfalse.elim

theorem accepted_entry (hU : IsPGroup 2 Original)
    (N : Subgroup Original) [N.Normal] :
    Nonempty (AcceptedEntry Original N) := by
  obtain ⟨C,heven⟩ := physical_pair_even N
  exact ⟨C.acceptedEntry16 hU heven⟩

end T1098

namespace T1086
open BinaryPairBinding16T1086

/-- Every normal axis is either an even-prefix direct entry or the exact
transport carrier, with its literal source and axis equalities retained. -/
theorem accepted_entry_or_transport (hU : IsPGroup 2 Original)
    (N : Subgroup Original) [N.Normal] :
    Nonempty (AcceptedEntry Original N) ∨
      (BinaryNormalTransport16T1086.chart.source=Original ∧
        BinaryNormalTransport16T1086.chart.axis=N.map Original.subtype) := by
  rcases BinaryPairAcceptance16T1086.accepted_or_exceptional_even N with
      ⟨C,hwidth,heven⟩ | ⟨i,hi,rfl⟩
  · let P := BinaryPhysicalPairCertificate.ofLocal physicalFrame generators
      generators_full C (by simpa only [Nat.card_fin] using hwidth)
    exact Or.inl ⟨P.acceptedEntry16 hU heven⟩
  · change i=2 at hi
    subst i
    exact Or.inr ⟨BinaryNormalTransport16T1086.source_eq,
      BinaryNormalTransport16T1086.axis_eq⟩

end T1086
end SymmetricSubgroupAsymptotics.BinarySelectedPairDirectOwners16
