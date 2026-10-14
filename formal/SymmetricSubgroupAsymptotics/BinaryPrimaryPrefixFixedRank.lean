import SymmetricSubgroupAsymptotics.BinaryPrimaryOddTwist
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelOrbitAnchor

/-!
# Fixed-space reduction after a binary-primary linear prefix

Ambient-fixed central involutions of a normal kernel are central
involutions of the whole group lying in that kernel. The literal inclusion
below makes the rank reduction from `BinaryPrimaryLinearCharacter`
available to the existing Schur-capacity and relative orbit generators.
The remaining nontrivial simple-type inequalities stay explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {Q B : Type} [Group Q] [Finite Q] [Group B]

/-- An ambient-fixed kernel involution is central in the whole group. -/
def binaryKernelOmegaFixedCentral (pi : Q →* B)
    (z : (binaryKernelOmegaConjugationRepresentation pi).invariants) :
    binaryCentralOmega Q := by
  let x : Q := ((binaryCentralOmegaEmbedding z.val.toMul : pi.ker) : Q)
  have hcentral : x ∈ Subgroup.center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    have hfixed : binaryKernelOmegaConjugateOmega pi q z.val.toMul = z.val.toMul :=
      congrArg Additive.toMul (z.property q)
    have hconjugate : q * x * q⁻¹ = x := by
      calc
        q * x * q⁻¹ = (binaryKernelOmegaConjugate pi q z.val.toMul : Q) :=
          (binaryKernelOmegaConjugate_val pi q z.val.toMul).symm
        _ = x := congrArg
          (fun w : binaryCentralOmega pi.ker ↦
            ((binaryCentralOmegaEmbedding w : pi.ker) : Q)) hfixed
    have h := congrArg (fun y : Q ↦ y * q) hconjugate
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  have hsquare : x ^ 2 = 1 :=
    congrArg (fun y : pi.ker ↦ (y : Q))
      (binaryCentralOmegaEquiv pi.ker z.val.toMul).property.2
  exact ⟨⟨x, hcentral⟩, Subtype.ext hsquare⟩

omit [Finite Q] in
@[simp] theorem binaryKernelOmegaFixedCentral_val (pi : Q →* B)
    (z : (binaryKernelOmegaConjugationRepresentation pi).invariants) :
    binaryCentralOmegaEmbedding (binaryKernelOmegaFixedCentral pi z) =
      ((binaryCentralOmegaEmbedding z.val.toMul : pi.ker) : Q) := rfl

/-- Keep the kernel condition while placing the fixed vectors inside the
whole group's central omega module. -/
def binaryKernelOmegaFixedToResidual (pi : Q →* B) :
    (binaryKernelOmegaConjugationRepresentation pi).invariants →+
      binaryCentralOmegaSubmodule pi.ker where
  toFun z := ⟨Additive.ofMul (binaryKernelOmegaFixedCentral pi z),
    (binaryCentralOmegaEmbedding z.val.toMul).property⟩
  map_zero' := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply binaryCentralOmegaEmbedding_injective
    rfl
  map_add' z w := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply binaryCentralOmegaEmbedding_injective
    rfl

omit [Finite Q] in
theorem binaryKernelOmegaFixedToResidual_injective (pi : Q →* B) :
    Function.Injective (binaryKernelOmegaFixedToResidual pi) := by
  intro z w h
  apply Subtype.ext
  apply Additive.toMul.injective
  apply binaryCentralOmegaEmbedding_injective
  apply Subtype.ext
  exact congrArg
    (fun y : binaryCentralOmegaSubmodule pi.ker ↦
      binaryCentralOmegaEmbedding y.val.toMul) h

/-- The ambient fixed-space rank is bounded by the literal central rank
remaining after the prefix. Intrinsic kernel centrality alone is not used
as a substitute for ambient fixedness. -/
theorem binaryKernelOmega_invariants_finrank_le_centralResidual (pi : Q →* B) :
    Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation pi).invariants ≤
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule pi.ker) :=
  LinearMap.finrank_le_finrank_of_injective
    (f := (binaryKernelOmegaFixedToResidual pi).toZModLinearMap 2)
    (binaryKernelOmegaFixedToResidual_injective pi)

/-- Construct the binary-primary prefix and prove the actual fixed-rank
bound on its kernel, including the optional trivial-prefix case. -/
theorem exists_binaryPrimaryPrefix_fixedRank_le
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] (r : ℕ)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ r + 1)
    (hderived : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator Q)) ≤ r) :
    ∃ χ : Q →* kˣ, IsPGroup 2 χ.range ∧
      Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation χ).invariants ≤ r := by
  obtain ⟨χ, hχ, hresidual⟩ :=
    exists_binaryPrimaryLinearCharacter_residual_rank_le (k := k)
      r hcentral hderived
  exact ⟨χ, hχ,
    (binaryKernelOmega_invariants_finrank_le_centralResidual χ).trans hresidual⟩

/-- A cubic (or other odd-order) anchor with binary kernel yields one
ordinary linear prefix and the same residual fixed-rank bound. -/
theorem exists_oddTwistedLinearPrefix_fixedRank_le
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    (ψ : Q →* kˣ) (n : ℕ) (hn : Nat.Coprime 2 n)
    (hψ : ∀ g : Q, (ψ g) ^ n = 1) (hker : IsPGroup 2 ψ.ker)
    (r : ℕ)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ r + 1)
    (hderived : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator Q)) ≤ r) :
    ∃ ξ : Q →* kˣ, IsPGroup 2 ξ.ker ∧
      Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation ξ).invariants ≤ r := by
  obtain ⟨ξ, hξ, hresidual⟩ :=
    exists_oddTwistedLinearCharacter_residual_rank_le
      ψ n hn hψ hker r hcentral hderived
  exact ⟨ξ, hξ,
    (binaryKernelOmega_invariants_finrank_le_centralResidual ξ).trans hresidual⟩

/-- The fixed-type cost is supplied by the designated prefix. The
nontrivial simple-type costs are still the actual multiplicity estimates
for this prefix kernel's socle. -/
theorem binaryKernelOmega_socleSchurCapacity_le_of_centralResidual
    (pi : Q →* B) (r : ℕ)
    (hresidual : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule pi.ker) ≤ r)
    (hnonfixed : ∀ S : Submodule (ZMod 2)[Q]
        (finiteRepresentationSocle
          (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.asModule,
      [IsSimpleModule (ZMod 2)[Q] S] →
      ¬ representationSubmoduleFixed
        (finiteRepresentationSocle
          (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation S →
      schurSocleMultiplicity
          (k := ZMod 2) (R := (ZMod 2)[Q])
          (A := (finiteRepresentationSocle
            (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.asModule)
          (X := S) ≤
        r * Module.finrank (Module.End (ZMod 2)[Q] S) S) :
    representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation ≤ r := by
  apply representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    _ r ?_ hnonfixed
  rw [finiteRepresentationSocle_invariants_finrank_eq]
  exact (binaryKernelOmega_invariants_finrank_le_centralResidual pi).trans hresidual

/-- The residual fixed-rank reduction and the displayed nontrivial
simple-type bounds produce the actual `r` separating normal-orbit slots.
This is an existing semisimple generator theorem, not a feasibility axiom. -/
noncomputable def BinaryKernelOmegaLinearOrbits.ofCentralResidual
    (pi : Q →* B) (r : ℕ)
    (hresidual : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule pi.ker) ≤ r)
    (hnonfixed : ∀ S : Submodule (ZMod 2)[Q]
        (finiteRepresentationSocle
          (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.asModule,
      [IsSimpleModule (ZMod 2)[Q] S] →
      ¬ representationSubmoduleFixed
        (finiteRepresentationSocle
          (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation S →
      schurSocleMultiplicity
          (k := ZMod 2) (R := (ZMod 2)[Q])
          (A := (finiteRepresentationSocle
            (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.asModule)
          (X := S) ≤
        r * Module.finrank (Module.End (ZMod 2)[Q] S) S) :
    BinaryKernelOmegaLinearOrbits pi r :=
  BinaryKernelOmegaLinearOrbits.ofSocleSchurCapacity
    (binaryKernelOmega_socleSchurCapacity_le_of_centralResidual
      pi r hresidual hnonfixed)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
