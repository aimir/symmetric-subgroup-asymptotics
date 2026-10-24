import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators
import SymmetricSubgroupAsymptotics.TernaryBlockTopOrdinaryGeneratorStep
import SymmetricSubgroupAsymptotics.FourPointBlockOrdinaryGeneratorInduction

/-! Four actual points per block and four actual block labels cost eight
ordinary generators without a smaller-degree generator hypothesis. The
linear quotient's sign action is allowed to be intransitive. All three
actual odd-kernel states are retained, with their proved correlated
translation-kernel bounds. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockFourLabelsOrdinaryGenerators
open FourPointBlockAffineCoordinates FourPointBlockTranslationKernel
open BinaryPlaneWreathActualOddKernel PermutationalWreathProduct

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

theorem linear_genRank_le_six (hlabels : Nat.card X = 4) :
    MarkedC4.genRank (linearImage b hb x₀ hfour) ≤ 6 := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let C := linearImage b hb x₀ hfour
  change MarkedC4.genRank C ≤ 6
  letI : MulAction C X := MulAction.compHom X
    ((rightHom : LinearFrame (G := G) (X := X) →* Top (G := G) (X := X)).comp C.subtype)
  letI : MulAction.IsPretransitive C X := ⟨image_transitive b hb x₀ hfour⟩
  let Y := Fin 3 × X
  letI : MulAction C Y := MulAction.compHom Y
    (FourPointBlockMultipleKernelOrdinaryInduction.puncturedHom b hb x₀ hfour)
  letI : FaithfulSMul C Y := {
    eq_of_smul_eq_smul := fun {u v} he =>
      FourPointBlockMultipleKernelOrdinaryInduction.puncturedHom_injective
        b hb x₀ hfour (Equiv.ext he) }
  let f : Y → X := Prod.snd
  have hf : ∀ (c : C) (y : Y),
      f (FourPointBlockMultipleKernelOrdinaryInduction.puncturedHom
        b hb x₀ hfour c y) = (c • f y : X) := fun _ _ => rfl
  let e : Fin 3 ≃ originalBlockFibre f x₀ := {
    toFun := fun i => ⟨(i,x₀),rfl⟩
    invFun := fun y => y.val.1
    left_inv := fun _ => rfl
    right_inv := fun y => Subtype.ext (Prod.ext rfl y.property.symm) }
  have h := TernaryBlockTopOrdinaryGeneratorStep.genRank_le_top_add_twice_half f hf x₀ e
  have ht := SmallFourPointOrdinaryGenerators.genRank_le_two
    (G := ActualBlockWreathEmbedding.Top (A := C) (X := X)) (X := X) hlabels
  calc
    MarkedC4.genRank C ≤
        MarkedC4.genRank (ActualBlockWreathEmbedding.Top (A := C) (X := X)) +
          2 * (Nat.card X / 2) := h
    _ ≤ 2 + 2 * (4 / 2) := Nat.add_le_add ht (by rw [hlabels])
    _ = 6 := rfl

theorem linear_genRank_le_four_of_zero
    (hzero : oddKernel (linearImage b hb x₀ hfour) = ⊥)
    (hlabels : Nat.card X = 4) :
    MarkedC4.genRank (linearImage b hb x₀ hfour) ≤ 4 := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let C := linearImage b hb x₀ hfour
  change MarkedC4.genRank C ≤ 4
  letI : MulAction C X := MulAction.compHom X
    ((rightHom : LinearFrame (G := G) (X := X) →* Top (G := G) (X := X)).comp C.subtype)
  letI : MulAction.IsPretransitive C X := ⟨image_transitive b hb x₀ hfour⟩
  let rho := (BinarySignWreathPointAction.signWreath
    (TernaryPermutationWreathEmbedding.signs (R := Top (G := G) (X := X)) (I := X))).comp
      (signProjection C)
  have hrho : Function.Injective rho :=
    (BinarySignWreathPointAction.signWreath_injective _).comp
      ((signProjection C).ker_eq_bot_iff.mp hzero)
  have hact : ∀ (c : C) (i : X), (rho c).right • i = c • i := fun _ _ => rfl
  have h := BinaryWreathOrdinaryGeneratorStep.genRank_le_top_add_half rho hrho hact
  have ht := SmallFourPointOrdinaryGenerators.genRank_le_two
    (G := (rightHom.comp rho).range) (X := X) hlabels
  calc
    MarkedC4.genRank C ≤ MarkedC4.genRank (rightHom.comp rho).range + Nat.card X / 2 := h
    _ ≤ 2 + 4 / 2 := Nat.add_le_add ht (by rw [hlabels])
    _ = 4 := rfl

include b hb x₀ hfour in
theorem genRank_le_eight (hlabels : Nat.card X = 4) : MarkedC4.genRank G ≤ 8 := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : IsMulCommutative (projection b hb x₀ hfour).ker :=
    FourPointBlockMultipleKernelOrdinaryInduction.kernel_isMulCommutative b hb x₀ hfour
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (projection b hb x₀ hfour) (projection_surjective b hb x₀ hfour)
  by_cases hzero : oddKernel (linearImage b hb x₀ hfour) = ⊥
  · have hQ := linear_genRank_le_four_of_zero b hb x₀ hfour hzero hlabels
    have hK := FourPointBlockZeroOddOrdinaryInduction.normalGen_kernel_le_dimension_half
      b hb x₀ hfour
    change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ 2 * (Nat.card X / 2) at hK
    rw [hlabels] at hK
    omega
  · have hQ := linear_genRank_le_six b hb x₀ hfour hlabels
    have hK : MarkedC4.normalGen (kernel b hb x₀ hfour) ≤ Nat.card X / 2 := by
      by_cases hsingle : ∀ i : X,
          BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) i =
            BinaryPlaneOddKernelMultiplicityUniform.localKernel (linearImage b hb x₀ hfour) x₀
      · exact FourPointBlockSingleKernelOrdinaryInduction.normalGen_kernel_le_half
          b hb x₀ hfour hzero hsingle
      · obtain ⟨i,hi⟩ := not_forall.mp hsingle
        exact FourPointBlockMultipleKernelOrdinaryInduction.normalGen_kernel_le_half
          b hb x₀ hfour hzero ⟨i,x₀,hi⟩
    change MarkedC4.normalGen (projection b hb x₀ hfour).ker ≤ Nat.card X / 2 at hK
    rw [hlabels] at hK
    omega

include b hb x₀ hfour in
theorem exists_generating_finset (hlabels : Nat.card X = 4) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ 8 := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,hS.le.trans (genRank_le_eight b hb x₀ hfour hlabels)⟩

end SymmetricSubgroupAsymptotics.FourPointBlockFourLabelsOrdinaryGenerators
