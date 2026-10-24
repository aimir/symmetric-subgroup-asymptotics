import SymmetricSubgroupAsymptotics.BinaryWreathOrdinaryGeneratorStep
import SymmetricSubgroupAsymptotics.TernaryBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! The actual top image, rather than a smaller-degree generator
hypothesis, controls a correlated three-point block action. The sign
quotient need not act transitively on its doubled point set. Only its
literal action on the original block labels is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryBlockTopOrdinaryGeneratorStep
open TernaryBlockKernelCoordinates PermutationalWreathProduct

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (e : Fin 3 ≃ originalBlockFibre b x₀)

def compressedTop : G ⧸ evenKernel b hb x₀ e →* Top (G := G) (X := X) :=
  rightHom.comp (Compression.quotientEmbedding (wreath b hb x₀ e) oddMarkerSign)

omit [Finite G] [Finite Ω] [Finite X] in
theorem compressedTop_mk (g : G) :
    compressedTop b hb x₀ e ((QuotientGroup.mk' (evenKernel b hb x₀ e)) g) =
      (ActualBlockWreathEmbedding.topMap (A := G) (X := X)).rangeRestrict g := rfl

omit [Finite G] [Finite Ω] [Finite X] in
theorem compressedTop_surjective : Function.Surjective (compressedTop b hb x₀ e) := by
  intro q
  obtain ⟨g,hg⟩ :=
    (ActualBlockWreathEmbedding.topMap (A := G) (X := X)).rangeRestrict_surjective q
  exact ⟨(QuotientGroup.mk' (evenKernel b hb x₀ e)) g,hg⟩

omit [Finite Ω] in
theorem sign_quotient_genRank_le [Nontrivial X] :
    MarkedC4.genRank (G ⧸ evenKernel b hb x₀ e) ≤
      MarkedC4.genRank (Top (G := G) (X := X)) + Nat.card X / 2 := by
  letI : Fintype X := Fintype.ofFinite X
  let K := evenKernel b hb x₀ e
  let rho := Compression.quotientEmbedding (wreath b hb x₀ e) oddMarkerSign
  let pi := compressedTop b hb x₀ e
  letI : MulAction (G ⧸ K) X := MulAction.compHom X pi
  letI : MulAction.IsPretransitive (G ⧸ K) X := ⟨by
    intro i j
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G i j
    refine ⟨(QuotientGroup.mk' K) g,?_⟩
    exact hg⟩
  have hact : ∀ (a : G ⧸ K) (i : X), (rho a).right • i = a • i :=
    fun _ _ => rfl
  have h := BinaryWreathOrdinaryGeneratorStep.genRank_le_top_add_half rho
    (Compression.quotientEmbedding_injective (wreath b hb x₀ e) oddMarkerSign) hact
  have hfull : (rightHom.comp rho).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (compressedTop_surjective b hb x₀ e)
  let E : (rightHom.comp rho).range ≃* Top (G := G) (X := X) :=
    (MulEquiv.subgroupCongr hfull).trans Subgroup.topEquiv
  simpa only [CoprimeNilpotentProductGenerators.genRank_mulEquiv E] using h

include b hb x₀ e in
theorem genRank_le_top_add_twice_half [Nontrivial X] :
    MarkedC4.genRank G ≤ MarkedC4.genRank (Top (G := G) (X := X)) +
      2 * (Nat.card X / 2) := by
  let K := evenKernel b hb x₀ e
  letI : IsMulCommutative K := evenKernel_isMulCommutative b hb x₀ e
  letI : IsMulCommutative (QuotientGroup.mk' K).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have h := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  rw [QuotientGroup.ker_mk'] at h
  have hK := TernaryBlockOrdinaryGeneratorInduction.normalGen_evenKernel_le_half b hb x₀ e
  have hQ := sign_quotient_genRank_le b hb x₀ e
  change MarkedC4.normalGen K ≤ Nat.card X / 2 at hK
  change MarkedC4.genRank (G ⧸ K) ≤
    MarkedC4.genRank (Top (G := G) (X := X)) + Nat.card X / 2 at hQ
  omega

end SymmetricSubgroupAsymptotics.TernaryBlockTopOrdinaryGeneratorStep
