import SymmetricSubgroupAsymptotics.TernaryOddPartKernelAnchor
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-!
# A binary anchor in the original faithful character tuple

When a finite group's order has odd part exactly three, one member of any
jointly faithful irreducible tuple has binary kernel. The same conclusion
applies to the actual tuple selected by the Zmud literature input and to
its existing `CharacterQuotientCertificate`.

These statements retain the original representations and their literal
kernels. The cardinality condition and the socle-generator input must
still be established for any proposed exceptional pair quotient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- One of the displayed jointly faithful irreducible representations has
a binary kernel. Irreducibility is retained by the conclusion's reference
to the original tuple; the group-theoretic argument uses only faithfulness. -/
theorem faithfulIrreducibleTuple_exists_binary_kernel_of_ternaryOddPart
    {G : Type} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    {ι : Type*} (rho : ι → FiniteIrreducibleRepresentation ℂ G)
    (hfaithful : ∀ g : G, (∀ i, (rho i).action g = 1) → g = 1) :
    ∃ i, IsPGroup 2 (rho i).action.ker :=
  ternaryOddPart_exists_isPGroup_two_ker hcard
    (fun i ↦ (rho i).action) hfaithful

/-- A general-only faithful slot tuple contains a binary-kernel anchor
among its existing general slots. -/
theorem CharacterSlotTuple.exists_binary_general_kernel_of_ternaryOddPart
    {G : Type} [Group G] [Finite G] {a : ℕ}
    (T : CharacterSlotTuple G) (hcard : Nat.card G = 2 ^ a * 3)
    (hbinary : T.binaryCount = 0) (hlinear : T.linearCount = 0) :
    ∃ i, IsPGroup 2 (T.general i).action.ker := by
  apply faithfulIrreducibleTuple_exists_binary_kernel_of_ternaryOddPart
    hcard T.general
  intro g hg
  apply T.faithful g _ _ hg
  · intro i
    exact Fin.elim0 (Fin.cast hbinary i)
  · intro i
    exact Fin.elim0 (Fin.cast hlinear i)

/-- The binary anchor belongs to the displayed quotient certificate's
literal tuple; no new faithful tuple is selected. -/
theorem CharacterQuotientCertificate.exists_binary_general_kernel_of_ternaryOddPart
    {G : Type} [Group G] [Finite G] {a : ℕ}
    (c : CharacterQuotientCertificate G) (hcard : Nat.card G = 2 ^ a * 3)
    (hbinary : c.tuple.binaryCount = 0) (hlinear : c.tuple.linearCount = 0) :
    ∃ i, IsPGroup 2 (c.tuple.general i).action.ker :=
  c.tuple.exists_binary_general_kernel_of_ternaryOddPart hcard hbinary hlinear

namespace ZmudFaithfulCharacterTupleInput

/-- The general tuple already selected by Zmud's input has a binary
kernel among its `t` original irreducible positions. -/
theorem generalTuple_exists_binary_kernel_of_ternaryOddPart
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {a t : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (hgen : SocleNormalGeneratorBound G t) :
    ∃ i, IsPGroup 2 ((hZmud.generalTuple hgen).general i).action.ker :=
  (hZmud.generalTuple hgen).exists_binary_general_kernel_of_ternaryOddPart
    hcard rfl rfl

/-- The existing general quotient certificate retains the same binary
kernel anchor in its actual tuple. -/
theorem generalCertificate_exists_binary_kernel_of_ternaryOddPart
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {a t : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (hgen : SocleNormalGeneratorBound G t) :
    ∃ i, IsPGroup 2
      ((hZmud.generalCertificate hgen).tuple.general i).action.ker :=
  hZmud.generalTuple_exists_binary_kernel_of_ternaryOddPart hcard hgen

/-- A socle-generator bound gives a jointly faithful tuple together with
a binary kernel among those very same irreducible positions. -/
theorem exists_faithful_tuple_with_binary_kernel_of_ternaryOddPart
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {a t : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (hgen : SocleNormalGeneratorBound G t) :
    ∃ rho : Fin t → FiniteIrreducibleRepresentation ℂ G,
      (∀ g : G, (∀ i, (rho i).action g = 1) → g = 1) ∧
      ∃ i, IsPGroup 2 (rho i).action.ker := by
  obtain ⟨rho, hfaithful⟩ := hZmud G t hgen
  exact ⟨rho, hfaithful,
    faithfulIrreducibleTuple_exists_binary_kernel_of_ternaryOddPart
      hcard rho hfaithful⟩

end ZmudFaithfulCharacterTupleInput
end SymmetricSubgroupAsymptotics

end
