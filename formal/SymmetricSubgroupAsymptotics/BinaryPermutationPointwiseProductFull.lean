import SymmetricSubgroupAsymptotics.PGroupPermutationAugmentationInterval
import SymmetricSubgroupAsymptotics.BinaryCoupledHeadCertificate
import SymmetricSubgroupAsymptotics.PermutationCoordinateSumApply

/-! Two invariant subspaces whose dimensions sum to more than the
original degree generate the full module by POINTWISE products. The
proof uses the literal coordinate pairing, not group-algebra convolution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
local instance pointwiseProductFullPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G : Type} [Group G] {w : ℕ} [MulAction G (Fin w)]
    [MulAction.IsPretransitive G (Fin w)]

def binaryPointwiseProductSubrepresentation
    (J S : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin w))) :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin w)) where
  toSubmodule := binaryCoordinateProductSpan J.toSubmodule S.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have hstable : binaryCoordinateProductSpan J.toSubmodule S.toSubmodule ≤
        (binaryCoordinateProductSpan J.toSubmodule S.toSubmodule).comap
          (permutationFunctionRepresentation (ZMod 2) G (Fin w) g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,b,hb,rfl⟩
      change permutationFunctionRepresentation (ZMod 2) G (Fin w) g (a*b) ∈
        binaryCoordinateProductSpan J.toSubmodule S.toSubmodule
      exact Submodule.subset_span ⟨_,J.apply_mem_toSubmodule g ha,
        _,S.apply_mem_toSubmodule g hb,rfl⟩
    exact hstable hv

theorem binary_pointwise_productSpan_eq_top_of_dimension_sum
    (hG : IsPGroup 2 G) (i : Fin w)
    (J S : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hlarge : w < Module.finrank (ZMod 2) J.toSubmodule+
      Module.finrank (ZMod 2) S.toSubmodule) :
    binaryCoordinateProductSpan J.toSubmodule S.toSubmodule=⊤ := by
  let P := binaryPointwiseProductSubrepresentation J S
  by_contra hproper
  have haug := pGroup_permutation_proper_subrepresentation_le_augmentation hG i P hproper
  let e := permutationFunctionRepresentationSelfDual (k := ZMod 2) (G := G) (X := Fin w)
  let f : J.toSubmodule →ₗ[ZMod 2] S.toSubmodule.dualAnnihilator :=
    (e.toLinearMap.comp J.toSubmodule.subtype).codRestrict S.toSubmodule.dualAnnihilator (by
      intro a
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro b hb
      have hm := haug (Submodule.subset_span ⟨a.val,a.property,b,hb,rfl⟩)
      change PermutationAugmentation.coordinateSum (ZMod 2) (Fin w) (a.val*b)=0 at hm
      change permutationFunctionRepresentationSelfDual (k := ZMod 2) (G := G) a.val b=0
      rw [permutationFunctionRepresentationSelfDual_apply]
      rw [permutation_coordinateSum_apply] at hm
      simpa only [Pi.mul_apply] using hm)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : S.toSubmodule.dualAnnihilator => z.val) he
  have hb := f.finrank_le_finrank_of_injective hf
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq S.toSubmodule
  have hw : Module.finrank (ZMod 2) (Fin w → ZMod 2)=w := by simp
  rw [hw] at hd
  omega

end SymmetricSubgroupAsymptotics
