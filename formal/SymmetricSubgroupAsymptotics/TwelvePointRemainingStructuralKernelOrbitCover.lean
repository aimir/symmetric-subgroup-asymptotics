import SymmetricSubgroupAsymptotics.BinaryPairNormalHead
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators

/-! Every original normal inside the correlated flip kernel has its own
literal stable coordinate space. A displayed cyclic point cover controls
that space directly, without enlarging its relative head to the whole
kernel head. Two cubic orbits give the signed-S4 six-pair capacity two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) [MulAction U I]
  (hact : ∀ (u : U) (i : I), u • i = F.top u i)

include hact in
theorem normal_kernel_relativeHead_le_orbitCover
    [Finite I] (u : U) {r : ℕ} (representative : Fin r → I)
    (hcover : ∀ x : I, ∃ (j : Fin r) (n : ℕ), u^n • representative j=x)
    (L : Subgroup U) [L.Normal] (hL : L ≤ F.top.ker) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) ≤ r := by
  classical
  letI := Fintype.ofFinite I
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U I) r :=
    permutationFunctionRepresentation_uniform_of_polynomial_orbitCover u representative hcover
  rw [← (F.normalKernelOriginalCharactersEquiv hact L hL).finrank_eq]
  obtain ⟨v,hv⟩ := hu (F.normalKernelOriginalSubrepresentation hact L hL)
  exact representationCharacterHead_le_generators _ v hv

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
