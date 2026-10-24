import SymmetricSubgroupAsymptotics.FourPointBlockTranslationKernel
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! Sharp ordinary generation for actual four-point block actions whose
actual linear image has nonzero odd layer and at least two local kernel
classes. The other two branches remain explicit; only strictly smaller
permutation degrees are used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockMultipleKernelOrdinaryInduction
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlaneWreathNormalGenerators BinaryPlaneWreathActualOddKernel
open PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

/-- The exact original linear image acts faithfully on three nonzero
plane vectors over every original block. -/
def puncturedHom : linearImage b hb x₀ hfour →* Equiv.Perm (Fin 3 × X) :=
  (PermutationalWreathProduct.toPerm (D := Equiv.Perm (Fin 3))
    (Q := Top (G := G) (X := X)) (I := X) (Lambda := Fin 3)).comp
      ((wreathMap (R := Top (G := G) (X := X)) (I := X)).comp
        (linearImage b hb x₀ hfour).subtype)

omit [Finite G] in
theorem puncturedHom_injective : Function.Injective (puncturedHom b hb x₀ hfour) := by
  letI : Nonempty X := ⟨x₀⟩
  exact PermutationalWreathProduct.toPerm_injective.comp
    (wreathMap_injective.comp Subtype.val_injective)

/-- The actual translation kernel is abelian, as its faithful coordinates are. -/
theorem kernel_isMulCommutative : IsMulCommutative (kernel b hb x₀ hfour) :=
  IsMulCommutative.of_comm fun u v => by
    apply coordinate_injective b hb x₀ hfour
    simp only [map_mul]
    exact mul_comm _ _

/-- The checked actual class projectors bound this correlated original
kernel's normal generators. No splitting is used. -/
theorem normalGen_kernel_le_half
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (htwo : ∃ i j : X,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i ≠
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) j) :
    MarkedC4.normalGen (kernel b hb x₀ hfour) ≤ Nat.card X / 2 := by
  have hu := BinaryPlaneOddKernelMultiplicityUniform.uniform_of_two_classes
    (linearImage b hb x₀ hfour) (image_transitive b hb x₀ hfour) hO htwo
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
    (htwo : ∃ i j : X,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i ≠
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) j)
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
  have hK := normalGen_kernel_le_half b hb x₀ hfour hO htwo
  change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ Nat.card X / 2 at hK
  omega

/-- Literal finite generators, rather than only a rank inequality. -/
theorem exists_half_degree_generators [Nontrivial X]
    (hO : oddKernel (linearImage b hb x₀ hfour) ≠ ⊥)
    (htwo : ∃ i j : X,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i ≠
        BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) j)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ hfour hO htwo hbelow⟩

/-- Original minimal-block installer. Its predicates refer to the actual
linear image constructed from this original subgroup, not supplied charts. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀) (hfour : Nat.card D.Fibre = 4)
    (hO : oddKernel (linearImage D.map D.map_equivariant D.base hfour) ≠ ⊥)
    (htwo : ∃ i j : D.Points,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel
        (linearImage D.map D.map_equivariant D.base hfour) i ≠
      BinaryPlaneOddKernelMultiplicityUniform.localKernel
        (linearImage D.map D.map_equivariant D.base hfour) j)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : Nontrivial D.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by have h := D.degrees_ge_two; omega)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators D.map D.map_equivariant D.base hfour hO htwo hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.FourPointBlockMultipleKernelOrdinaryInduction
