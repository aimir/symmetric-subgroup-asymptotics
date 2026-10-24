import SymmetricSubgroupAsymptotics.FourPointBlockMultipleKernelOrdinaryInduction
import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelTwoBlockUniform
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! Sharp ordinary generation for an actual four-point block action
whose nonzero odd layer has one literal local-kernel class. The actual
translation kernel is correlated and no affine splitting is assumed.
Only strictly smaller permutation degrees are used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockSingleKernelOrdinaryInduction
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlaneWreathNormalGenerators BinaryPlaneWreathActualOddKernel
open PermutationOrdinarySmallerActions
open FourPointBlockMultipleKernelOrdinaryInduction
  (puncturedHom puncturedHom_injective kernel_isMulCommutative)

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

/-- Actual single-class uniform generation bounds the correlated
original translation kernel. No splitting is used. -/
theorem normalGen_kernel_le_half [Nontrivial X]
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (hsingle : ∀ i : X,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i =
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) x₀) :
    MarkedC4.normalGen (kernel b hb x₀ hfour) ≤ Nat.card X / 2 := by
  have hu := BinaryPlaneSingleKernelTwoBlockUniform.uniform
    (linearImage b hb x₀ hfour) x₀ hsingle hO (image_transitive b hb x₀ hfour)
  have hA := hu.of_injective (kernelInclusion b hb x₀ hfour)
    (kernelInclusion_injective b hb x₀ hfour)
  letI : Finite (kernelModule b hb x₀ hfour) := Finite.of_injective
    (fun a : kernelModule b hb x₀ hfour =>
      (kernelModuleChart b hb x₀ hfour).equiv (Multiplicative.ofAdd a))
    ((kernelModuleChart b hb x₀ hfour).equiv.injective.comp Multiplicative.ofAdd.injective)
  letI : FiniteDimensional (ZMod 2) (kernelModule b hb x₀ hfour) := Module.Finite.of_finite
  exact (kernelModuleChart b hb x₀ hfour).kernel_normalGen_le
    (projection b hb x₀ hfour) (kernelModule b hb x₀ hfour)
    (projection_surjective b hb x₀ hfour) (Nat.card X / 2) hA
    (kernel b hb x₀ hfour) le_rfl

/-- The smaller faithful 3t-point quotient and at most floor(t/2)
translation positions together give the sharp 4t-point bound. -/
theorem half_degree [Nontrivial X]
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (hsingle : ∀ i : X,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i =
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) x₀)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  have hdegree : Nat.card Ω = 4 * Nat.card X := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,hfour] at hh
    exact hh.symm
  have ht : 2 ≤ Nat.card X := by
    have hh := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial X)
    omega
  let Y := Fin 3 × X
  have hpoints : Nat.card Y = 3 * Nat.card X := by
    change Nat.card (Fin 3 × X) = _
    rw [Nat.card_prod,Nat.card_fin]
  letI : MulAction (linearImage b hb x₀ hfour) Y :=
    MulAction.compHom Y (puncturedHom b hb x₀ hfour)
  letI : FaithfulSMul (linearImage b hb x₀ hfour) Y := {
    eq_of_smul_eq_smul := fun {u v} he =>
      puncturedHom_injective b hb x₀ hfour (Equiv.ext he) }
  have hQ := hbelow (linearImage b hb x₀ hfour) Y (by omega) (by omega)
  letI : IsMulCommutative (projection b hb x₀ hfour).ker :=
    kernel_isMulCommutative b hb x₀ hfour
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (projection b hb x₀ hfour) (projection_surjective b hb x₀ hfour)
  have hK := normalGen_kernel_le_half b hb x₀ hfour hO hsingle
  change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ Nat.card X / 2 at hK
  omega

/-- Literal finite generators, rather than only a rank inequality. -/
theorem exists_half_degree_generators [Nontrivial X]
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (hsingle : ∀ i : X,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i =
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) x₀)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ hfour hO hsingle hbelow⟩

/-- Original minimal-block installer. Its predicates refer to the actual
linear image constructed from this original subgroup, not supplied charts. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀) (hfour : Nat.card D.Fibre = 4)
    (hO : oddKernel (linearImage D.map D.map_equivariant D.base hfour) ≠ ⊥)
    (hsingle : ∀ i : D.Points,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel
        (linearImage D.map D.map_equivariant D.base hfour) i =
      BinaryPlaneOddKernelMultiplicityUniform.localKernel
        (linearImage D.map D.map_equivariant D.base hfour) D.base)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : Nontrivial D.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by have h := D.degrees_ge_two; omega)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators D.map D.map_equivariant D.base hfour hO hsingle hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.FourPointBlockSingleKernelOrdinaryInduction
