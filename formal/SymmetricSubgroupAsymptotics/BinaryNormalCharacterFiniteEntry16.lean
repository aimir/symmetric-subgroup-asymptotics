import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotAcceptance16T1184
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotAcceptance16T1391

/-! The two checked character routes install exact all-normal finite entries
for their original actions. The carrier family is arbitrary because these
two installations use only their physical pair or actual quotient character
branch. No additional character contexts or finite action coverage follow. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {q : ℕ} {κ : Type*} (carriers : κ → CheckedPermutationCarrier 16 q)

namespace BinaryPairAcceptance16T1184
open BinaryPairBinding16T1184

/-- The original 16T1184 affine-obstruction route resolves every normal. -/
theorem finite_entry (N : Subgroup Original) [N.Normal] :
    BinaryFiniteEntry carriers Original N := by
  rcases pair_or_character_criterion N with ⟨C,hwidth⟩ | hcharacter
  · exact Or.inl ⟨BinaryPhysicalPairCertificate.ofLocal physicalFrame generators
      generators_full C (by simpa only [Nat.card_fin] using hwidth)⟩
  · exact Or.inr (Or.inl hcharacter)

end BinaryPairAcceptance16T1184

namespace BinaryPairAcceptance16T1391
open BinaryPairBinding16T1391

/-- The original 16T1391 faithful-kernel-action route resolves every normal. -/
theorem finite_entry (N : Subgroup Original) [N.Normal] :
    BinaryFiniteEntry carriers Original N := by
  rcases pair_or_character_criterion N with ⟨C,hwidth⟩ | hcharacter
  · exact Or.inl ⟨BinaryPhysicalPairCertificate.ofLocal physicalFrame generators
      generators_full C (by simpa only [Nat.card_fin] using hwidth)⟩
  · exact Or.inr (Or.inl hcharacter)

end BinaryPairAcceptance16T1391
end SymmetricSubgroupAsymptotics
