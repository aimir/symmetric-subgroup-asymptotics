import Mathlib.GroupTheory.Index

/-!
# Transport between finite surjective quotients with the same kernel

The finite catalogues store one literal quotient map, while the structural
argument produces another quotient map on the same source.  Equality of
their kernels gives the exact target equivalence and commuting square.
This file keeps that elementary first-isomorphism transport independent of
any affine catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The target equivalence induced by two surjective homomorphisms with the
same literal kernel. -/
noncomputable def surjectiveTargetEquivOfKernelEq
    {H L R : Type*} [Group H] [Group L] [Group R]
    (f : H →* L) (g : H →* R)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) : L ≃* R :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

/-- The induced target equivalence carries the first quotient map to the
second one pointwise. -/
theorem surjectiveTargetEquivOfKernelEq_comp
    {H L R : Type*} [Group H] [Group L] [Group R]
    (f : H →* L) (g : H →* R)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) :
    (surjectiveTargetEquivOfKernelEq f g hf hg hker).toMonoidHom.comp f = g := by
  ext x
  let ef := QuotientGroup.quotientKerEquivOfSurjective f hf
  let eg := QuotientGroup.quotientKerEquivOfSurjective g hg
  have hmk : ef.symm (f x) = QuotientGroup.mk x := by
    apply ef.injective
    rw [ef.apply_symm_apply]
    rfl
  change eg (QuotientGroup.quotientMulEquivOfEq hker (ef.symm (f x))) = g x
  rw [hmk, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end SymmetricSubgroupAsymptotics

end
