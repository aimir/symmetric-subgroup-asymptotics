import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianizationProof
import SymmetricSubgroupAsymptotics.NilpotentConjugacyClassProof

/-! The current character literature boundary contains one statement.
The two abelian-quotient fields and the nilpotent class-number field in
the original four-field internal API are supplied by proved theorems. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The remaining general permutation class-number statement. Both
Kovács--Praeger fields and the nilpotent class-number bound are proved. -/
structure PreE7CharacterPublishedInputs : Prop where
  garonziMaroti : GaronziMarotiConjugacyClassBound

/-- Fill the old internal interface with the three proved fields. -/
theorem PreE7CharacterPublishedInputs.toLiterature
    (h : PreE7CharacterPublishedInputs) : PreE7CharacterLiterature where
  garonziMaroti := h.garonziMaroti
  kovacsPraeger := KovacsPraegerAbelianizationProof.kovacsPraegerAbelianizationBound
  kovacsPraegerBinary :=
    PermutationAbelianQuotientOrderBound.kovacsPraegerBinaryAbelianQuotientBound
  maroti := NilpotentConjugacyClassProof.nilpotentConjugacyClassInput

end SymmetricSubgroupAsymptotics
