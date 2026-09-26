import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism

/-!
# The relative head of the original correlated pair kernel

The faithful kernel chart intertwines conjugation by the original group U
with its original action on the pair labels. The actual correlated image
is used as a U-subrepresentation; no descent of its head to the top image,
no enlarged flip product, and no split-extension premise are introduced.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type*} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) [MulAction U I]
    (hact : ∀ (u : U) (i : I), u • i = F.top u i)

include hact

/-- Literal conjugation on the original kernel is the function action on
its retained bits, with the same inverse coordinate convention. -/
theorem originalCoordinateAction_bits (u : U) (k : F.top.ker) :
    permutationFunctionRepresentation (ZMod 2) U I u (F.bits k) =
      F.bits (MulAut.conjNormal u k) := by
  funext i
  rw [permutationFunctionRepresentation_apply, hact, map_inv]
  exact (F.bits_conjNormal u k i).symm

/-- The full correlated kernel image is stable under the ORIGINAL group.
The coordinate submodule is exactly `F.kernelSpace`. -/
def kernelOriginalSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) U I) where
  toSubmodule := F.kernelSpace
  apply_mem_toSubmodule u v hv := by
    obtain ⟨k, rfl⟩ := hv
    change permutationFunctionRepresentation (ZMod 2) U I u (F.bits k.toMul) ∈
      F.kernelSpace
    rw [F.originalCoordinateAction_bits hact]
    exact ⟨Additive.ofMul (MulAut.conjNormal u k.toMul), rfl⟩

/-- The actual faithful chart identifies the full original-conjugation
invariant character space, not merely an upper bound on its dimension. -/
def kernelOriginalCharactersEquiv :
    primeActionCharacters 2
        (representationGroupAction (F.kernelOriginalSubrepresentation hact).toRepresentation)
      ≃ₗ[ZMod 2] primeRelativeCharacters 2 F.top.ker :=
  (primeActionCharacterCongr 2 F.kernelChart
    (normalChainSourceAction F.top.ker)
    (representationGroupAction (F.kernelOriginalSubrepresentation hact).toRepresentation)
    (by
      intro u k
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change F.bits (MulAut.conjNormal u k) =
        permutationFunctionRepresentation (ZMod 2) U I u (F.bits k)
      exact (F.originalCoordinateAction_bits hact u k).symm)).trans
    (normalChainSourceCharactersEquiv F.top.ker 2)

/-- Any actual element of the original group gives a cyclic-orbit bound
for the original kernel's relative head. -/
theorem kernel_relativeHead_le_cyclicOrbitCount [Finite I] (u : U) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 F.top.ker) ≤
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers u) I) := by
  rw [← (F.kernelOriginalCharactersEquiv hact).finrank_eq]
  exact permutation_subrepresentationCharacterHead_le_cyclicOrbitCount
    (F.kernelOriginalSubrepresentation hact) u

/-- The coarse bound also applies to a singleton pair-label set, supplying
the two-point base of a degree induction without a separate group catalogue. -/
theorem kernel_relativeHead_le_card [Finite I] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 F.top.ker) ≤ Nat.card I := by
  classical
  letI := Fintype.ofFinite I
  rw [← (F.kernelOriginalCharactersEquiv hact).finrank_eq]
  have h := subrepresentationCharacterHead_le_ambient_elementFixedSpace
    (permutationFunctionRepresentation (ZMod 2) U I)
    (F.kernelOriginalSubrepresentation hact) (1 : U)
  have h' := h.trans (Submodule.finrank_le
    (representationElementFixedSpace (permutationFunctionRepresentation (ZMod 2) U I) 1))
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h'

/-- A transitive nontrivial pair-label action gives the half-degree bound
for the entire original-conjugation invariant head of the literal kernel. -/
theorem kernel_relativeHead_le_half [Finite I] [Nontrivial I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 F.top.ker) ≤ Nat.card I / 2 := by
  rw [← (F.kernelOriginalCharactersEquiv hact).finrank_eq]
  exact pGroup_permutationSubrepresentationCharacterHead_le_div hU
    (F.kernelOriginalSubrepresentation hact)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
