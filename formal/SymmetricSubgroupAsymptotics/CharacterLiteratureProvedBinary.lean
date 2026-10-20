import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

/-! The current character literature boundary contains three statements.
The binary abelian-quotient field in the original four-field internal API
is supplied by a proved theorem, including all higher binary exponents. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The remaining published statements used by the character template.
The ordinary mixed-prime Kovács--Praeger bound remains explicit. -/
structure PreE7CharacterPublishedInputs : Prop where
  garonziMaroti : GaronziMarotiConjugacyClassBound
  kovacsPraeger : KovacsPraegerAbelianizationBound
  maroti : NilpotentConjugacyClassInput

/-- Fill the old internal interface with the proved binary theorem. -/
theorem PreE7CharacterPublishedInputs.toLiterature
    (h : PreE7CharacterPublishedInputs) : PreE7CharacterLiterature where
  garonziMaroti := h.garonziMaroti
  kovacsPraeger := h.kovacsPraeger
  kovacsPraegerBinary :=
    PermutationAbelianQuotientOrderBound.kovacsPraegerBinaryAbelianQuotientBound
  maroti := h.maroti

end SymmetricSubgroupAsymptotics
