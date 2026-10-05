import SymmetricSubgroupAsymptotics.ActualWreathAffineSixCapacity

/-!
# Canonical ternary width for every actual affine section

The six-block capacity-two theorem is one value of a general statement.
After restricting a literal affine section to an actual Sylow-three
subgroup, the Mackey width of the original block index bounds the invariant
quotient.  Evaluation on a fixed vector of each original simple source then
bounds the original Schur capacity.  This file keeps the canonical integer
width before any degree-specific numerical specialization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace ActualWreathAffineCapacity

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

variable (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

section NormalSection

variable (N : Subgroup S.A) [N.Normal]

set_option maxHeartbeats 800000 in
/-- The Sylow restriction of the inflated literal section has invariant
dimension at most the canonical Mackey width.  Keeping this calculation
separate prevents the induced-representation and Schur-capacity towers from
being elaborated in one theorem. -/
theorem inflatedSectionInvariants_le_ternaryWidthCore
    (P : Sylow 3 S.A)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    Module.finrank (ZMod C.p) (Representation.invariants
      (show Representation (ZMod C.p) P
          ((PermutationalWreathProduct.Compression.ElementarySubmodule
              (p := C.p) S.rho phi C.equiv.symm) ⧸
            normalSpace S phi C N) from
        (inflatedSectionRepresentation S phi C N).comp
          (P : Subgroup S.A).subtype)) ≤
      ternaryWidthCore (Fintype.card I) ((Fintype.card I).factorization 3) := by
  let f := representationRestrictionHom
    (ambientRepresentation S phi C)
    (inducedRepresentation S phi C i₀) (P : Subgroup S.A).subtype
    (inducedIntertwiner S phi C i₀)
  let W :=
    (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) ⧸ normalSpace S phi C N
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  letI : Finite (E S phi C).quotientRepresentation :=
    inferInstanceAs (Finite (E S phi C).V)
  letI : Finite W := Finite.of_surjective
    (normalSpace S phi C N).mkQ (normalSpace S phi C N).mkQ_surjective
  letI : FiniteDimensional (ZMod C.p) W :=
    FiniteDimensional.of_surjective
      (normalSpace S phi C N).mkQ (normalSpace S phi C N).mkQ_surjective
  let tau : Representation (ZMod C.p) S.A W :=
    inflatedSectionRepresentation S phi C N
  have hindex : (S.topPointStabilizer i₀).index = Fintype.card I := by
    rw [S.topPointStabilizer_index i₀]
  have hinv : Module.finrank (ZMod C.p)
      (Representation.invariants
        (show Representation (ZMod C.p) P W from
          tau.comp (P : Subgroup S.A).subtype)) ≤
      ternaryWidthCore (Fintype.card I)
        ((Fintype.card I).factorization 3) := by
    have h := inducedRestrictionTernary_section_invariants_le_widthCore
      (S.topPointStabilizer i₀) (localRepresentation S phi C i₀) P
      f.range (show Representation (ZMod C.p) P W from
        tau.comp (P : Subgroup S.A).subtype)
      (sylowSectionQuotient S phi C N P i₀)
      (sylowSectionQuotient_surjective S phi C N P i₀)
    rw [hindex, hdim, one_mul] at h
    exact h
  exact hinv

/-- The inflated literal section has capacity at most the canonical
Sylow/Mackey width.  This theorem combines the isolated invariant estimate
with the general p-subgroup Schur-capacity comparison. -/
theorem inflatedSectionCapacity_le_ternaryWidthCore
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    representationSchurCapacity
      (inflatedSectionRepresentation S phi C N) ≤
      ternaryWidthCore (Fintype.card I) ((Fintype.card I).factorization 3) := by
  let P : Sylow 3 S.A := Classical.choice inferInstance
  let W :=
    (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) ⧸ normalSpace S phi C N
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  letI : Finite (E S phi C).quotientRepresentation :=
    inferInstanceAs (Finite (E S phi C).V)
  letI : Finite W := Finite.of_surjective
    (normalSpace S phi C N).mkQ (normalSpace S phi C N).mkQ_surjective
  letI : FiniteDimensional (ZMod C.p) W :=
    FiniteDimensional.of_surjective
      (normalSpace S phi C N).mkQ (normalSpace S phi C N).mkQ_surjective
  have hPC : IsPGroup C.p P := by
    simpa only [hp] using P.isPGroup'
  have hinv := inflatedSectionInvariants_le_ternaryWidthCore
    S phi C N P hdim i₀
  have hcap : representationSchurCapacity
        (inflatedSectionRepresentation S phi C N) ≤
      Module.finrank (ZMod C.p) (Representation.invariants
        (show Representation (ZMod C.p) P W from
          (inflatedSectionRepresentation S phi C N).comp
            (P : Subgroup S.A).subtype)) :=
    representationSchurCapacity_le_pSubgroup_invariants
      (P : Subgroup S.A) hPC (inflatedSectionRepresentation S phi C N)
  have hinvR : (Module.finrank (ZMod C.p) (Representation.invariants
      (show Representation (ZMod C.p) P W from
        (inflatedSectionRepresentation S phi C N).comp
          (P : Subgroup S.A).subtype)) : ℝ) ≤
      ternaryWidthCore (Fintype.card I)
        ((Fintype.card I).factorization 3) := by
    exact_mod_cast hinv
  exact hcap.trans hinvR

/-- Every literal one-dimensional ternary section has Schur capacity at most
the canonical Sylow/Mackey width of the actual block index. -/
theorem sharpSectionCapacity_le_ternaryWidthCore
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    representationSchurCapacity
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N).ρ ≤
      ternaryWidthCore (Fintype.card I) ((Fintype.card I).factorization 3) := by
  letI : FiniteDimensional (ZMod C.p)
      (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm) := inferInstance
  letI : FiniteDimensional (ZMod (E S phi C).p) (E S phi C).V :=
    (E S phi C).finiteDimensional
  letI : FiniteDimensional (ZMod (E S phi C).p)
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N) := by
    change FiniteDimensional (ZMod (E S phi C).p)
      ((E S phi C).V ⧸
        (originalChart S phi C).normalSpace
          (pi S phi) (E S phi C).quotientRepresentation N)
    infer_instance
  have hinflated := inflatedSectionCapacity_le_ternaryWidthCore
    S phi C N hp hdim i₀
  have heq := representationSchurCapacity_comp
    (QuotientGroup.mk' ((pi S phi).ker ⊔ N))
    (QuotientGroup.mk'_surjective ((pi S phi).ker ⊔ N))
    ((originalChart S phi C).sectionRepresentation
      (pi S phi) (E S phi C).quotientRepresentation N).ρ
  rw [← heq]
  exact hinflated

end NormalSection

/-- Retain the proved joint fixed-top coefficient while replacing the
generic half-dimension exponent by the canonical ternary width. -/
noncomputable def sharpenJointCapacityToTernaryWidthCore
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart where
  capacity := ternaryWidthCore (Fintype.card I)
    ((Fintype.card I).factorization 3)
  capacity_nonneg := by positivity
  section_capacity := by
    intro N
    exact sharpSectionCapacity_le_ternaryWidthCore
      S phi C N hp hdim i₀
  coefficient := H.coefficient
  coefficient_nonneg := H.coefficient_nonneg
  fixed_top_fibre := H.fixed_top_fibre

@[simp] theorem sharpenJointCapacityToTernaryWidthCore_capacity
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    (sharpenJointCapacityToTernaryWidthCore
      S phi C H hp hdim i₀).capacity =
        ternaryWidthCore (Fintype.card I)
          ((Fintype.card I).factorization 3) := rfl

@[simp] theorem sharpenJointCapacityToTernaryWidthCore_coefficient
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    (sharpenJointCapacityToTernaryWidthCore
      S phi C H hp hdim i₀).coefficient = H.coefficient := rfl

end ActualWreathAffineCapacity
end SymmetricSubgroupAsymptotics

end
