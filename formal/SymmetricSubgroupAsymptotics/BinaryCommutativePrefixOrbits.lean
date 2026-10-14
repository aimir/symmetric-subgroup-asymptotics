import SymmetricSubgroupAsymptotics.BinaryPrimaryPrefixFixedRank

/-!
# A binary-primary prefix for a commutative binary quotient

This small consumer checks the designated-prefix mechanism when every
ambient conjugation type is fixed. It is useful for an actual elementary
abelian quotient of a literal exceptional top; it does not replace the
nontrivial-type estimates for arbitrary pair-lift quotients.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {Q B : Type} [Group Q] [Finite Q] [Group B]

omit [Finite Q] in
theorem binaryCentralOmegaSubmodule_bot :
    binaryCentralOmegaSubmodule (⊥ : Subgroup Q) = ⊥ := by
  ext z
  change binaryCentralOmegaEmbedding z.toMul = 1 ↔ z = 0
  constructor
  · intro h
    apply Additive.toMul.injective
    apply binaryCentralOmegaEmbedding_injective
    simpa only [toMul_zero, map_one] using h
  · rintro rfl
    exact map_one _

omit [Finite Q] in
theorem binaryKernelOmegaConjugation_eq_one_of_commutative
    [IsMulCommutative Q] (pi : Q →* B) (q : Q) :
    binaryKernelOmegaConjugationRepresentation pi q = 1 := by
  apply LinearMap.ext
  intro z
  apply Additive.toMul.injective
  apply binaryCentralOmegaEmbedding_injective
  apply Subtype.ext
  change (binaryKernelOmegaConjugate pi q z.toMul : Q) =
    ((binaryCentralOmegaEmbedding z.toMul : pi.ker) : Q)
  rw [binaryKernelOmegaConjugate_val, mul_comm q]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Every simple submodule of the actual kernel omega socle is fixed for
a commutative ambient quotient. This discharges nonfixed multiplicities
by excluding such types, rather than replacing their Schur dimensions. -/
theorem binaryKernelOmega_socle_submodule_fixed_of_commutative
    [IsMulCommutative Q] (pi : Q →* B)
    (S : Submodule (ZMod 2)[Q]
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.asModule) :
    representationSubmoduleFixed
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation S := by
  intro g x
  apply Subtype.ext
  rw [Submodule.coe_smul, Representation.single_smul, one_smul]
  apply Subtype.ext
  change binaryKernelOmegaConjugationRepresentation pi g _ = _
  rw [binaryKernelOmegaConjugation_eq_one_of_commutative]
  rfl

/-- One binary-primary linear prefix leaves at most `r` separating orbit
slots in an actual commutative binary quotient of central rank at most
`r+1`. The resulting kernel, its fixed-rank reduction and its socle
capacity are all attached to the constructed character itself. -/
theorem exists_binaryPrimaryPrefix_orbits_of_commutative
    [IsMulCommutative Q] (hQ : IsPGroup 2 Q) (r : ℕ)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ r + 1) :
    ∃ χ : Q →* ℂˣ, IsPGroup 2 χ.range ∧ IsPGroup 2 χ.ker ∧
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule χ.ker) ≤ r ∧
      representationSchurCapacity
        (finiteRepresentationSocle
          (binaryKernelOmegaConjugationRepresentation χ)).toRepresentation ≤ r ∧
      Nonempty (BinaryKernelOmegaLinearOrbits χ r) := by
  have hderived : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator Q)) ≤ r := by
    rw [commutator_eq_bot, binaryCentralOmegaSubmodule_bot,
      finrank_bot]
    exact Nat.zero_le r
  obtain ⟨χ, hχ, hresidual⟩ :=
    exists_binaryPrimaryLinearCharacter_residual_rank_le (k := ℂ)
      r hcentral hderived
  have hcap : representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation χ)).toRepresentation ≤ r := by
    apply binaryKernelOmega_socleSchurCapacity_le_of_centralResidual χ r hresidual
    intro S _hS hnonfixed
    exact (hnonfixed
      (binaryKernelOmega_socle_submodule_fixed_of_commutative χ S)).elim
  exact ⟨χ, hχ, hQ.to_subgroup χ.ker, hresidual, hcap,
    ⟨BinaryKernelOmegaLinearOrbits.ofSocleSchurCapacity hcap⟩⟩

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
