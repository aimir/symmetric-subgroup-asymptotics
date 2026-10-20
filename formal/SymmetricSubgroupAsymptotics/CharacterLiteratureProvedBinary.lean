import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianizationProof

/-! The current character literature boundary contains two statements.
Both abelian-quotient fields in the original four-field internal API are
supplied by proved theorems, including all prime-power exponents. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The two remaining published class-number statements used by the
character template. Both Kovács--Praeger fields are proved internally. -/
structure PreE7CharacterPublishedInputs : Prop where
  garonziMaroti : GaronziMarotiConjugacyClassBound
  maroti : NilpotentConjugacyClassInput

/-- Fill the old internal interface with the proved binary theorem. -/
theorem PreE7CharacterPublishedInputs.toLiterature
    (h : PreE7CharacterPublishedInputs) : PreE7CharacterLiterature where
  garonziMaroti := h.garonziMaroti
  kovacsPraeger := KovacsPraegerAbelianizationProof.kovacsPraegerAbelianizationBound
  kovacsPraegerBinary :=
    PermutationAbelianQuotientOrderBound.kovacsPraegerBinaryAbelianQuotientBound
  maroti := h.maroti

end SymmetricSubgroupAsymptotics
