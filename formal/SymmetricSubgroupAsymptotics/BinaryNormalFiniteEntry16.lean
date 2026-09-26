import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry
import SymmetricSubgroupAsymptotics.BinaryNormalTransport16

/-! The checked original 16T1086 action has a finite entry for every
original normal subgroup. Its sole carrier is the literal degree-sixteen
chart; this is not a claim covering every degree-sixteen action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

def binarySixteenTransportChart (_ : Fin 1) : CheckedPermutationCarrier 16 16 :=
  BinaryNormalTransport16T1086.chart

def BinaryFiniteEntry16 (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop :=
  BinaryFiniteEntry binarySixteenTransportChart U N

namespace BinaryNormalTransport16T1086
open BinaryPairBinding16T1086

/-- Exact all-normal installation for the original checked generator tuple.
The generic pair theorem supplies its actual cut/capacity gap; the other
branch retains the checked source, original axis and full carrier maps. -/
theorem finite_entry (N : Subgroup Original) [N.Normal] :
    BinaryFiniteEntry16 Original N := by
  rcases pair_or_transport N with ⟨C,hwidth⟩ | ⟨hs,ha⟩
  · exact Or.inl ⟨BinaryPhysicalPairCertificate.ofLocal physicalFrame generators
      generators_full C (by simpa only [Nat.card_fin] using hwidth)⟩
  · exact Or.inr (Or.inr ⟨0,hs,ha⟩)

end BinaryNormalTransport16T1086
end SymmetricSubgroupAsymptotics
