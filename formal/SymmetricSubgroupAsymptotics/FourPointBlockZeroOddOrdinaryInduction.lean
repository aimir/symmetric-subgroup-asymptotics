import SymmetricSubgroupAsymptotics.FourPointBlockMultipleKernelOrdinaryInduction
import SymmetricSubgroupAsymptotics.BinarySignWreathPointAction
import SymmetricSubgroupAsymptotics.BlockMonomialPolynomialOrbitGenerators

/-! The zero actual odd-layer branch of four-point block induction. Its
linear image embeds in the actual binary sign wreath, with a faithful
strictly smaller 2t-point action. The correlated translation kernel uses
the unrestricted two-dimensional vector-holonomy bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockZeroOddOrdinaryInduction
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel PermutationOrdinarySmallerActions

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

/-- The exact linear image's sign action has two points per original block. -/
def signHom : linearImage b hb x₀ hfour →* Equiv.Perm (ZMod 2 × X) :=
  (BinarySignWreathPointAction.pointHom
    (TernaryPermutationWreathEmbedding.signs
      (R := Top (G := G) (X := X)) (I := X))).comp
        (signProjection (linearImage b hb x₀ hfour))

omit [Finite G] in
theorem signHom_injective (hzero : oddKernel (linearImage b hb x₀ hfour) = ⊥) :
    Function.Injective (signHom b hb x₀ hfour) := by
  letI : Nonempty X := ⟨x₀⟩
  exact (BinarySignWreathPointAction.pointHom_injective _).comp
    ((signProjection (linearImage b hb x₀ hfour)).ker_eq_bot_iff.mp hzero)

/-- Arbitrary actual local holonomy costs at most two positions per
half block-orbit; this statement does not assume zero odd image. -/
theorem normalGen_kernel_le_dimension_half [Nontrivial X] :
    MarkedC4.normalGen (kernel b hb x₀ hfour) ≤ 2 * (Nat.card X / 2) := by
  let C := linearImage b hb x₀ hfour
  let rho := BinaryPlaneCyclicWreathUniform.representation C
  letI : MulAction C X := MulAction.compHom X
    ((PermutationalWreathProduct.rightHom : LinearFrame (G := G) (X := X) →*
      Top (G := G) (X := X)).comp C.subtype)
  letI : MulAction.IsPretransitive C X := ⟨image_transitive b hb x₀ hfour⟩
  have hdelta : ∀ g : C, ∀ i : X, ∃ L : Plane ≃ₗ[ZMod 2] Plane,
      ∀ v, rho g (Pi.single i v) = Pi.single (g • i) (L v) := by
    intro g i
    let w : LinearFrame (G := G) (X := X) := g.val
    refine ⟨w.left (w.right • i),?_⟩
    intro v
    funext j
    change w.left j ((Pi.single i v : X → Plane) (w.right⁻¹ • j)) =
      (Pi.single (w.right • i) (w.left (w.right • i) v) : X → Plane) j
    by_cases hj : j = w.right • i
    · subst j
      rw [inv_smul_smul,Pi.single_eq_same,Pi.single_eq_same]
    · have hn : w.right⁻¹ • j ≠ i := by
        intro h
        apply hj
        calc
          j = w.right • (w.right⁻¹ • j) := (smul_inv_smul _ _).symm
          _ = w.right • i := congrArg (fun z => w.right • z) h
      rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hj,map_zero]
  have hu : UniformSubrepresentationGeneratorBound rho (2 * (Nat.card X / 2)) := by
    simpa [Plane] using BlockMonomialPolynomialOrbitGenerators.uniform_of_transitive rho hdelta
  have hA := hu.of_injective (kernelInclusion b hb x₀ hfour)
    (kernelInclusion_injective b hb x₀ hfour)
  letI : Finite (kernelModule b hb x₀ hfour) := Finite.of_injective
    (fun a : kernelModule b hb x₀ hfour =>
      (kernelModuleChart b hb x₀ hfour).equiv (Multiplicative.ofAdd a))
    ((kernelModuleChart b hb x₀ hfour).equiv.injective.comp Multiplicative.ofAdd.injective)
  letI : FiniteDimensional (ZMod 2) (kernelModule b hb x₀ hfour) := Module.Finite.of_finite
  exact (kernelModuleChart b hb x₀ hfour).kernel_normalGen_le
    (projection b hb x₀ hfour) (kernelModule b hb x₀ hfour)
    (projection_surjective b hb x₀ hfour) (2 * (Nat.card X / 2)) hA
    (kernel b hb x₀ hfour) le_rfl

/-- Zero odd image lowers the faithful linear quotient to 2t points. -/
theorem half_degree [Nontrivial X]
    (hzero : oddKernel (linearImage b hb x₀ hfour) = ⊥)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    2 * MarkedC4.genRank G ≤ Nat.card Ω := by
  have hdegree : Nat.card Ω = 4 * Nat.card X := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,hfour] at hh
    exact hh.symm
  have ht : 2 ≤ Nat.card X := by
    have hh := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial X)
    omega
  let Y := ZMod 2 × X
  have hpoints : Nat.card Y = 2 * Nat.card X := by
    change Nat.card (ZMod 2 × X) = _
    rw [Nat.card_prod,Nat.card_zmod]
  letI : MulAction (linearImage b hb x₀ hfour) Y :=
    MulAction.compHom Y (signHom b hb x₀ hfour)
  letI : FaithfulSMul (linearImage b hb x₀ hfour) Y := {
    eq_of_smul_eq_smul := fun {u v} he =>
      signHom_injective b hb x₀ hfour hzero (Equiv.ext he) }
  have hQ := hbelow (linearImage b hb x₀ hfour) Y (by omega) (by omega)
  letI : IsMulCommutative (projection b hb x₀ hfour).ker :=
    FourPointBlockMultipleKernelOrdinaryInduction.kernel_isMulCommutative b hb x₀ hfour
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (projection b hb x₀ hfour) (projection_surjective b hb x₀ hfour)
  have hK := normalGen_kernel_le_dimension_half b hb x₀ hfour
  change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ 2 * (Nat.card X / 2) at hK
  omega

theorem exists_half_degree_generators [Nontrivial X]
    (hzero : oddKernel (linearImage b hb x₀ hfour) = ⊥)
    (hbelow : SmallerActionBound (Nat.card Ω)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 * S.card ≤ Nat.card Ω := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree b hb x₀ hfour hzero hbelow⟩

/-- Literal original subgroup installer, with its zero actual odd layer. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀) (hfour : Nat.card D.Fibre = 4)
    (hzero : oddKernel (linearImage D.map D.map_equivariant D.base hfour) = ⊥)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : Nontrivial D.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by have h := D.degrees_ge_two; omega)
  have hbase : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  have hh := exists_half_degree_generators D.map D.map_equivariant D.base hfour hzero hbase
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.FourPointBlockZeroOddOrdinaryInduction
