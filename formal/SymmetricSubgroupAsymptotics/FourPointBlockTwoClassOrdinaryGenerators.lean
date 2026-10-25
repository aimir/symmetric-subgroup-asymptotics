import SymmetricSubgroupAsymptotics.BinaryPlaneTwoClassOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FourPointBlockMultipleKernelOrdinaryInduction
import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators

/-! The actual four-point affine block source with two literal odd-kernel
classes has at most top-rank plus two linear generators and floor(t/2)
translation generators. In particular four blocks cost at most six. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockTwoClassOrdinaryGenerators
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

theorem genRank_le_top_add_two_add_half
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥) (i j : X)
    (hne : localKernel (linearImage b hb x₀ hfour) i ≠ localKernel (linearImage b hb x₀ hfour) j)
    (hcover : ∀ k : X, localKernel (linearImage b hb x₀ hfour) k =
      localKernel (linearImage b hb x₀ hfour) i ∨ localKernel (linearImage b hb x₀ hfour) k =
      localKernel (linearImage b hb x₀ hfour) j) :
    MarkedC4.genRank G ≤ MarkedC4.genRank (Top (G := G) (X := X)) + 2 + Nat.card X / 2 := by
  have htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp
      (linearImage b hb x₀ hfour).subtype) := by
    intro q
    obtain ⟨g,hg⟩ := (ActualBlockWreathEmbedding.topMap (A := G) (X := X)).rangeRestrict_surjective q
    refine ⟨projection b hb x₀ hfour g,?_⟩
    change (linearMap b hb x₀ hfour g).right = q
    rw [linearMap_right]
    exact hg
  have hQ : MarkedC4.genRank (linearImage b hb x₀ hfour) ≤
      MarkedC4.genRank (Top (G := G) (X := X)) + 2 :=
    BinaryPlaneTwoClassOrdinaryGenerators.genRank_le_top_add_two
      (linearImage b hb x₀ hfour) htop (image_transitive b hb x₀ hfour) hO i j hne hcover
  letI : IsMulCommutative (projection b hb x₀ hfour).ker :=
    FourPointBlockMultipleKernelOrdinaryInduction.kernel_isMulCommutative b hb x₀ hfour
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (projection b hb x₀ hfour) (projection_surjective b hb x₀ hfour)
  have hK := FourPointBlockMultipleKernelOrdinaryInduction.normalGen_kernel_le_half
    b hb x₀ hfour hO ⟨i,j,hne⟩
  change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ Nat.card X / 2 at hK
  omega

theorem genRank_le_six_of_four_blocks (ht : Nat.card X = 4)
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥) (i j : X)
    (hne : localKernel (linearImage b hb x₀ hfour) i ≠ localKernel (linearImage b hb x₀ hfour) j)
    (hcover : ∀ k : X, localKernel (linearImage b hb x₀ hfour) k =
      localKernel (linearImage b hb x₀ hfour) i ∨ localKernel (linearImage b hb x₀ hfour) k =
      localKernel (linearImage b hb x₀ hfour) j) :
    MarkedC4.genRank G ≤ 6 := by
  have htop : MarkedC4.genRank (Top (G := G) (X := X)) ≤ 2 :=
    SmallFourPointOrdinaryGenerators.genRank_le_two ht
  have hh := genRank_le_top_add_two_add_half b hb x₀ hfour hO i j hne hcover
  omega

end SymmetricSubgroupAsymptotics.FourPointBlockTwoClassOrdinaryGenerators
