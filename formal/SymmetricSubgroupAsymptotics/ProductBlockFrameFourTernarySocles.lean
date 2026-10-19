import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding
import SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualSubgroupNormalGenerators

/-! An actual four-triple frame with block image containing A4 has three
normal generators on every original normal subgroup. The exact image in
the signed affine model retains every sign/translation correlation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U (Fin 4) (Fin 3))

private def ternaryAffineEmbedding : U →*
    AlternatingFourTernaryActualSubgroupNormalGenerators.Model :=
  TernaryPermutationWreathEmbedding.affine.comp C.wreathEmbedding

private theorem ternaryAffineEmbedding_injective :
    Function.Injective C.ternaryAffineEmbedding :=
  TernaryPermutationWreathEmbedding.affine_injective.comp C.wreathEmbedding_injective

theorem normal_triples_of_four_ternary_blocks
    (heven : alternatingGroup (Fin 4) ≤ C.top.range) :
    ∀ N : Subgroup U, N.Normal →
      ∃ x : Fin 3 → U, Subgroup.normalClosure (Set.range x) = N := by
  let f := C.ternaryAffineEmbedding
  let K := f.range
  let e : U ≃* K := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => C.ternaryAffineEmbedding_injective (congrArg Subtype.val h),
      f.rangeRestrict_surjective⟩
  have hA : alternatingGroup (Fin 4) ≤
      AlternatingSignedImageNormalGenerators.blockImage
        (AlternatingFourTernaryActualSubgroupNormalGenerators.SignedImage K) := by
    intro g hg
    obtain ⟨u,hu⟩ := heven hg
    refine ⟨(LinearSemidirectSubgroupKernelChart.projection
      AlternatingFourTernaryActualSubgroupNormalGenerators.action K).rangeRestrict
        (f.rangeRestrict u),?_⟩
    change (f u).right.right = g
    exact hu
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (AlternatingFourTernaryActualSubgroupNormalGenerators.normal_generating_triples K hA)

theorem quotientSocle_three_of_four_ternary_blocks
    (heven : alternatingGroup (Fin 4) ≤ C.top.range)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (C.normal_triples_of_four_ternary_blocks heven) N

end SymmetricSubgroupAsymptotics.ProductBlockFrame
