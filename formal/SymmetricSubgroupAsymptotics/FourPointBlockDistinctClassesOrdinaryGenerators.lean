import SymmetricSubgroupAsymptotics.FourPointBlockMultipleKernelOrdinaryInduction

/-! Distinct actual cubic-kernel classes give multiplicity one on the
SAME correlated translation representation, hence one ambient translation
seed in the original source. No full product or independent fibres occur. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockDistinctClassesOrdinaryGenerators
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

theorem normalGen_kernel_le_one
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (hinj : Function.Injective (localKernel (linearImage b hb x₀ hfour))) :
    MarkedC4.normalGen (kernel b hb x₀ hfour) ≤ 1 := by
  let C := linearImage b hb x₀ hfour
  have hbound (K : Subgroup (oddKernel C)) : Nat.card {i : X // localKernel C i = K} ≤ 1 := by
    letI : Subsingleton {i : X // localKernel C i = K} := ⟨fun x y =>
      Subtype.ext (hinj (x.property.trans y.property.symm))⟩
    exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have hu := BinaryPlaneOddKernelMultiplicityUniform.uniform_of_bound
    C (image_transitive b hb x₀ hfour) hO 1 hbound
  have hA := hu.of_injective (kernelInclusion b hb x₀ hfour)
    (kernelInclusion_injective b hb x₀ hfour)
  letI : Finite (kernelModule b hb x₀ hfour) := Finite.of_injective
    (fun a : kernelModule b hb x₀ hfour =>
      (kernelModuleChart b hb x₀ hfour).equiv (Multiplicative.ofAdd a))
    ((kernelModuleChart b hb x₀ hfour).equiv.injective.comp Multiplicative.ofAdd.injective)
  letI : FiniteDimensional (ZMod 2) (kernelModule b hb x₀ hfour) := Module.Finite.of_finite
  exact (kernelModuleChart b hb x₀ hfour).kernel_normalGen_le
    (projection b hb x₀ hfour) (kernelModule b hb x₀ hfour)
    (projection_surjective b hb x₀ hfour) 1 hA (kernel b hb x₀ hfour) le_rfl

theorem genRank_le_image_add_one
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (hinj : Function.Injective (localKernel (linearImage b hb x₀ hfour))) :
    MarkedC4.genRank G ≤ MarkedC4.genRank (linearImage b hb x₀ hfour) + 1 := by
  letI : IsMulCommutative (projection b hb x₀ hfour).ker :=
    FourPointBlockMultipleKernelOrdinaryInduction.kernel_isMulCommutative b hb x₀ hfour
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (projection b hb x₀ hfour) (projection_surjective b hb x₀ hfour)
  have hK := normalGen_kernel_le_one b hb x₀ hfour hO hinj
  change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ 1 at hK
  omega

end SymmetricSubgroupAsymptotics.FourPointBlockDistinctClassesOrdinaryGenerators
