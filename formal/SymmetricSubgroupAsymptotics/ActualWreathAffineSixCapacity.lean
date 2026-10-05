import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.InducedTernaryRestrictionSection
import SymmetricSubgroupAsymptotics.PermutationSemiregularSchurCapacity

/-!
# Sharp ternary section capacity over six actual blocks

For a one-dimensional ternary local chief factor over six blocks, every
literal normal section has Schur capacity at most two.  The proof restricts
the original section to an actual Sylow-three subgroup of the original
ambient group.  Its invariant space is a quotient of a subrepresentation of
the Sylow-restricted induced module, so the checked Mackey width `B(6)=2`
applies.  Evaluation on a nonzero Sylow-fixed vector in every original
simple source transfers that invariant bound back to the original Schur
capacity.

The resulting constructor keeps the old joint incidence coefficient and
only sharpens its source-dependent section exponent.  Thus no finite axis,
normal graph, transgression or cohomology datum is discarded.
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

/-- The section quotient after restricting the actual ambient injection to
a Sylow subgroup, with the image kept as a literal subrepresentation of the
restricted induced module. -/
noncomputable def sylowSectionQuotient
    (P : Sylow 3 S.A) (i₀ : I) :
    let f := representationRestrictionHom
      (ambientRepresentation S phi C)
      (inducedRepresentation S phi C i₀) (P : Subgroup S.A).subtype
      (inducedIntertwiner S phi C i₀)
    f.range.toRepresentation.IntertwiningMap
      ((inflatedSectionRepresentation S phi C N).comp (P : Subgroup S.A).subtype) := by
  let f := representationRestrictionHom
    (ambientRepresentation S phi C)
    (inducedRepresentation S phi C i₀) (P : Subgroup S.A).subtype
    (inducedIntertwiner S phi C i₀)
  have hf : Function.Injective f :=
    inducedIntertwiner_injective S phi C i₀
  have hf' : Function.Injective (RepresentationHeadExact.rangeProjection f) := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  let e := (RepresentationHeadExact.rangeProjection f).ofBijective
    ⟨hf', RepresentationHeadExact.rangeProjection_surjective f⟩
  let q := representationRestrictionHom
    (ambientRepresentation S phi C)
    (inflatedSectionRepresentation S phi C N) (P : Subgroup S.A).subtype
    (sectionQuotientIntertwiner S phi C N)
  exact q.comp e.symm.toIntertwiningMap

theorem sylowSectionQuotient_surjective
    (P : Sylow 3 S.A) (i₀ : I) :
    Function.Surjective (sylowSectionQuotient S phi C N P i₀) := by
  let f := representationRestrictionHom
    (ambientRepresentation S phi C)
    (inducedRepresentation S phi C i₀) (P : Subgroup S.A).subtype
    (inducedIntertwiner S phi C i₀)
  have hf : Function.Injective f :=
    inducedIntertwiner_injective S phi C i₀
  have hf' : Function.Injective (RepresentationHeadExact.rangeProjection f) := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  let e := (RepresentationHeadExact.rangeProjection f).ofBijective
    ⟨hf', RepresentationHeadExact.rangeProjection_surjective f⟩
  have he : Function.Surjective e.symm := e.symm.surjective
  have hq : Function.Surjective (representationRestrictionHom
      (ambientRepresentation S phi C)
      (inflatedSectionRepresentation S phi C N) (P : Subgroup S.A).subtype
      (sectionQuotientIntertwiner S phi C N)) :=
    sectionQuotientIntertwiner_surjective S phi C N
  exact hq.comp he

set_option maxHeartbeats 800000 in
/-- The Sylow restriction of the inflated literal section has at most two
invariants.  This isolates the induced-representation tower from the later
Schur-capacity comparison. -/
theorem inflatedSectionInvariants_le_two_of_ternary_six
    (P : Sylow 3 S.A)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (hsix : Fintype.card I = 6) (i₀ : I) :
    Module.finrank (ZMod C.p) (Representation.invariants
      (show Representation (ZMod C.p) P
          ((PermutationalWreathProduct.Compression.ElementarySubmodule
              (p := C.p) S.rho phi C.equiv.symm) ⧸
            normalSpace S phi C N) from
        (inflatedSectionRepresentation S phi C N).comp
          (P : Subgroup S.A).subtype)) ≤ 2 := by
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
  have hindex : (S.topPointStabilizer i₀).index = 6 := by
    rw [S.topPointStabilizer_index i₀, hsix]
  have hinv : Module.finrank (ZMod C.p)
      (Representation.invariants
        (show Representation (ZMod C.p) P W from
          tau.comp (P : Subgroup S.A).subtype)) ≤ 2 := by
    exact inducedRestrictionTernary_section_invariants_le_two_of_index_six
      (S.topPointStabilizer i₀) (localRepresentation S phi C i₀) P
      f.range (show Representation (ZMod C.p) P W from
        tau.comp (P : Subgroup S.A).subtype)
      (sylowSectionQuotient S phi C N P i₀)
      (sylowSectionQuotient_surjective S phi C N P i₀)
      hindex hdim
  exact hinv

/-- The inflated literal section has capacity two, obtained by comparing
Schur multiplicity with the isolated Sylow-invariant estimate. -/
theorem inflatedSectionCapacity_le_two_of_ternary_six
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (hsix : Fintype.card I = 6) (i₀ : I) :
    representationSchurCapacity
      (inflatedSectionRepresentation S phi C N) ≤ 2 := by
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
  have hinv := inflatedSectionInvariants_le_two_of_ternary_six
    S phi C N P hdim hsix i₀
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
          (P : Subgroup S.A).subtype)) : ℝ) ≤ 2 := by
    exact_mod_cast hinv
  exact hcap.trans hinvR

/-- Exact capacity two for every literal section of a one-dimensional
ternary affine kernel over six actual blocks. -/
theorem sharpSectionCapacity_le_two_of_ternary_six
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (hsix : Fintype.card I = 6) (i₀ : I) :
    representationSchurCapacity
      ((originalChart S phi C).sectionRepresentation
      (pi S phi) (E S phi C).quotientRepresentation N).ρ ≤ 2 := by
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
  have hinflated := inflatedSectionCapacity_le_two_of_ternary_six
    S phi C N hp hdim hsix i₀
  have heq := representationSchurCapacity_comp
    (QuotientGroup.mk' ((pi S phi).ker ⊔ N))
    (QuotientGroup.mk'_surjective ((pi S phi).ker ⊔ N))
    ((originalChart S phi C).sectionRepresentation
      (pi S phi) (E S phi C).quotientRepresentation N).ρ
  rw [← heq]
  exact hinflated

end NormalSection

/-- Retain a previously proved joint fixed-top coefficient while replacing
the generic half-dimension section exponent by the sharp six-block value
two. -/
noncomputable def sharpenJointCapacityToTwo_of_ternary_six
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (hsix : Fintype.card I = 6) (i₀ : I) :
    ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart where
  capacity := 2
  capacity_nonneg := by norm_num
  section_capacity := by
    intro N
    exact sharpSectionCapacity_le_two_of_ternary_six
      S phi C N hp hdim hsix i₀
  coefficient := H.coefficient
  coefficient_nonneg := H.coefficient_nonneg
  fixed_top_fibre := H.fixed_top_fibre

@[simp] theorem sharpenJointCapacityToTwo_of_ternary_six_capacity
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (hsix : Fintype.card I = 6) (i₀ : I) :
    (sharpenJointCapacityToTwo_of_ternary_six
      S phi C H hp hdim hsix i₀).capacity = 2 := rfl

@[simp] theorem sharpenJointCapacityToTwo_of_ternary_six_coefficient
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' (K S phi))
      (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (hsix : Fintype.card I = 6) (i₀ : I) :
    (sharpenJointCapacityToTwo_of_ternary_six
      S phi C H hp hdim hsix i₀).coefficient = H.coefficient := rfl

end ActualWreathAffineCapacity
end SymmetricSubgroupAsymptotics

end
