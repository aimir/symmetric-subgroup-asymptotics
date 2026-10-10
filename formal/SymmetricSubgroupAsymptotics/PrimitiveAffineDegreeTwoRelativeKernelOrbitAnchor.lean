import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelAnchor

/-!
# Relative characters from normal orbits in a binary kernel

The paired-eight argument does not need a basis-sized tuple of characters
of its binary direct kernel.  It needs one irreducible character for each
normal-generator slot of the kernel's central involution module.  This file
isolates that reduction.

For each slot, an irreducible representation of the binary kernel is lifted
to an irreducible representation of the whole quotient by Frobenius
reciprocity and Maschke.  Normality of the overgroup kernel then makes the
whole conjugacy orbit of the chosen kernel representation visible.  If the
displayed kernel irreducibles separate central involutions after all ambient
conjugates, the lifted whole-group irreducibles are jointly faithful on the
kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {Q B : Type*} [Group Q] [Finite Q] [Group B]

/-- Ambient conjugation preserves the intrinsic central involutions of a
normal kernel.  We construct the result through the literal ambient omega
subgroup, whose normality has already been proved. -/
noncomputable def binaryKernelOmegaConjugateOmega
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) :
    binaryCentralOmega pi.ker := by
  let e := binaryCentralOmegaEquivNormalKernel pi
  let z' : normalKernelCentralOmega pi := e z
  exact e.symm
    ⟨q * (z' : Q) * q⁻¹,
      Subgroup.Normal.conj_mem inferInstance (z' : Q) z'.2 q⟩

/-- The same conjugate, regarded as an element of the normal kernel. -/
noncomputable def binaryKernelOmegaConjugate
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) : pi.ker :=
  binaryCentralOmegaEmbedding (binaryKernelOmegaConjugateOmega pi q z)

@[simp] theorem binaryKernelOmegaConjugate_val
    (pi : Q →* B) (q : Q) (z : binaryCentralOmega pi.ker) :
    (binaryKernelOmegaConjugate pi q z : Q) =
      q * (binaryCentralOmegaEmbedding z : Q) * q⁻¹ :=
  by
    let e := binaryCentralOmegaEquivNormalKernel pi
    let z' : normalKernelCentralOmega pi := e z
    let y : normalKernelCentralOmega pi :=
      ⟨q * (z' : Q) * q⁻¹,
        Subgroup.Normal.conj_mem inferInstance (z' : Q) z'.2 q⟩
    have h := congrArg (fun x : normalKernelCentralOmega pi ↦ (x : Q))
      (e.apply_symm_apply y)
    simpa only [binaryKernelOmegaConjugate,
      binaryKernelOmegaConjugateOmega, e, z', y] using h

/-- A tuple of irreducible kernel representations whose ambient conjugacy
orbits separate the intrinsic central involutions.  This is the exact
semantic output required from a finite dual-orbit certificate. -/
structure BinaryKernelOmegaOrbitIrreducibles
    (pi : Q →* B) (r : ℕ) : Type 1 where
  fibre : Fin r → FiniteIrreducibleRepresentation ℂ pi.ker
  separates : ∀ z : binaryCentralOmega pi.ker,
    (∀ i q, (fibre i).action (binaryKernelOmegaConjugate pi q z) = 1) →
      z = 1

/-- A character form of the same finite certificate.  Characters are kept
on the literal central-omega subgroup of the binary kernel, so existing
central-character machinery constructs the kernel irreducibles without a
new representation model. -/
structure BinaryKernelOmegaOrbitCharacters
    (pi : Q →* B) (r : ℕ) : Type where
  character : Fin r → binaryOmegaSubgroup pi.ker →* ℂ
  separates : ∀ z : binaryCentralOmega pi.ker,
    (∀ i q, character i
      (binaryOmegaSubgroupEquiv
        (binaryKernelOmegaConjugateOmega pi q z)) = 1) → z = 1

namespace BinaryKernelOmegaOrbitCharacters

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaOrbitCharacters pi r)

/-- Central characters give the kernel irreducibles consumed by the
overgroup lifting theorem. -/
noncomputable def toOrbitIrreducibles :
    BinaryKernelOmegaOrbitIrreducibles pi r := by
  have hexists (i : Fin r) :=
    exists_bundled_central_character
      (binaryOmegaSubgroup pi.ker) binaryOmegaSubgroup_central
      (C.character i)
  choose fibre scalar using hexists
  exact
    { fibre := fibre
      separates := by
        intro z hz
        apply C.separates z
        intro i q
        let omega := binaryKernelOmegaConjugateOmega pi q z
        let h : binaryOmegaSubgroup pi.ker := binaryOmegaSubgroupEquiv omega
        have hs (v : (fibre i).Space) := scalar i h v
        have ha : (fibre i).action (h : pi.ker) = 1 := by
          change (fibre i).action
            (binaryCentralOmegaEmbedding omega) = 1
          exact hz i q
        letI : Nontrivial (fibre i).action.asModule :=
          IsSimpleModule.nontrivial ℂ[pi.ker] (fibre i).action.asModule
        letI : Nontrivial (fibre i).Space :=
          (fibre i).action.asModuleEquiv.toEquiv.symm.nontrivial
        obtain ⟨v, hv⟩ := exists_ne (0 : (fibre i).Space)
        have hscalar : C.character i h = 1 :=
          (smul_left_injective ℂ hv) (by
            simpa only [ha, Module.End.one_apply, one_smul] using (hs v).symm)
        exact hscalar }

end BinaryKernelOmegaOrbitCharacters

namespace BinaryKernelOmegaOrbitIrreducibles

variable {pi : Q →* B} {r : ℕ}
  (C : BinaryKernelOmegaOrbitIrreducibles pi r)

/-- The irreducible whole-group representation lying over one displayed
kernel irreducible. -/
noncomputable def overgroup (i : Fin r) :
    OvergroupRestrictionConstituent (C.fibre i).action pi.ker.subtype :=
  OvergroupRestrictionConstituent.choose pi.ker (C.fibre i).action

/-- Bundle the lifted overgroup constituent in the character-count type. -/
noncomputable def relative (i : Fin r) :
    FiniteIrreducibleRepresentation ℂ Q where
  Space := (C.overgroup i).Space
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  action := (C.overgroup i).action
  irreducible := inferInstance

/-- The lifted whole-group irreducibles are jointly faithful when restricted
to the binary kernel. -/
theorem relative_faithful_on_kernel
    (hpi : IsPGroup 2 pi.ker) (x : pi.ker)
    (hx : ∀ i, (C.relative i).action (x : Q) = 1) :
    x = 1 := by
  apply binaryCentralOmega_joint_kernel_detection hpi
    (fun i ↦ (C.relative i).action.comp pi.ker.subtype)
  · intro z hz
    apply C.separates z
    intro i q
    let y := binaryKernelOmegaConjugate pi q z
    have hzq : (C.relative i).action (y : Q) = 1 := by
      change (C.relative i).action
        (q * (binaryCentralOmegaEmbedding z : Q) * q⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hz i]
      simp
    ext v
    apply (C.overgroup i).inclusion_injective
    have hintertwine :=
      Representation.IntertwiningMap.isIntertwining
        (C.fibre i).action
        ((C.relative i).action.comp pi.ker.subtype)
        (C.overgroup i).inclusion y v
    change (C.overgroup i).inclusion ((C.fibre i).action y v) =
      (C.overgroup i).inclusion v
    rw [hintertwine]
    change (C.relative i).action (y : Q) ((C.overgroup i).inclusion v) = _
    rw [hzq]
    rfl
  · exact hx

end BinaryKernelOmegaOrbitIrreducibles

namespace DegreeTwoPairRelativeKernelAnchor

/-- Build the complete relative-kernel anchor from a fixed prefix and a
normal-orbit tuple on the binary prefix kernel.  The relative representations
and their restriction constituents are constructed here; downstream finite
rows only have to supply the orbit-separation certificate. -/
noncomputable def ofBinaryKernelOmegaOrbitIrreducibles
    {profile : DegreeTwoPairRelativeProfile}
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (orbit : BinaryKernelOmegaOrbitIrreducibles pi profile.relative) :
    DegreeTwoPairRelativeKernelAnchor Q profile where
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  relative := orbit.relative
  kernel := pi.ker
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  constituent := fun i ↦
    NormalRestrictionConstituent.choose (orbit.relative i).action pi.ker
  faithful := by
    intro q hbinary hlinear hord hrelative
    have hq : q ∈ pi.ker := by
      rw [kernel_eq]
      exact ⟨⟨fun i ↦ MonoidHom.mem_ker.mpr (hbinary i),
        fun i ↦ MonoidHom.mem_ker.mpr (hlinear i)⟩,
        fun i ↦ MonoidHom.mem_ker.mpr (hord i)⟩
    let x : pi.ker := ⟨q, hq⟩
    have hx : x = 1 := orbit.relative_faithful_on_kernel
      kernel_twoGroup x (fun i ↦ hrelative i)
    simpa using congrArg Subtype.val hx

/-- Character-facing form of
`ofBinaryKernelOmegaOrbitIrreducibles`.  A finite certificate may stay on
the intrinsic central omega subgroup; the required kernel irreducibles and
their ambient lifts are chosen uniformly. -/
noncomputable def ofBinaryKernelOmegaOrbitCharacters
    {profile : DegreeTwoPairRelativeProfile}
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (orbit : BinaryKernelOmegaOrbitCharacters pi profile.relative) :
    DegreeTwoPairRelativeKernelAnchor Q profile :=
  ofBinaryKernelOmegaOrbitIrreducibles pi binary binary_twoGroup linear
    ordinary kernel_eq kernel_twoGroup orbit.toOrbitIrreducibles

end DegreeTwoPairRelativeKernelAnchor

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
