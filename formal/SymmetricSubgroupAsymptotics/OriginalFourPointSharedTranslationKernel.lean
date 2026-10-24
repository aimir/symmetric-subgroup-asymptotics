import SymmetricSubgroupAsymptotics.FourPointBlockPrimitiveZeroOddImage
import SymmetricSubgroupAsymptotics.WreathCompressionKernelCongruence
import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.FourPointBlockSingleKernelOrdinaryInduction

/-! The structural and native translation kernels are equal as subgroups
of the SAME original source. Thus the checked actual cubic-kernel sharing
bound, including correlated and single-isotypic odd images, applies to the
original head without a smaller-action or published Tracey hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalFourPointSharedTranslationKernel
open OriginalAffineBlockCharacteristicHead PermutationalWreathProduct

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)
local instance pointsNontrivial : Nontrivial block.Points :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.2
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem compression_kernel_eq_native (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2) :
    Compression.kernel (OriginalBlockOrdinaryCompressionState.initialState J block).rho
      (QuotientGroup.mk' P.V) =
        FourPointBlockTranslationKernel.kernel block.map block.map_equivariant block.base hfour := by
  let rho := ActualBlockWreathEmbedding.embedding block.map block.map_equivariant block.base
  let psi := FourPointBlockPrimitiveZeroOddImage.localLinear block.map block.map_equivariant block.base hfour
  have hker : (QuotientGroup.mk' P.V).ker = psi.ker := by
    have hh := PrimitiveAffineFourNativeLinearKernel.linearHom_kernel P
      (FourPointBlockAffineCoordinates.fibreChart block.map block.base hfour) block.component_preprimitive
      (P.elementaryChart block.component_preprimitive) hp
    exact (QuotientGroup.ker_mk' P.V).trans hh.symm
  calc
    Compression.kernel (OriginalBlockOrdinaryCompressionState.initialState J block).rho
        (QuotientGroup.mk' P.V) = Compression.kernel rho psi :=
      WreathCompressionKernelCongruence.kernel_eq_of_ker_eq rho (QuotientGroup.mk' P.V) psi hker
    _ = (FourPointBlockAffineCoordinates.linearMap block.map block.map_equivariant block.base hfour).ker := by
      rw [FourPointBlockPrimitiveZeroOddImage.linearMap_eq_compression block.map block.map_equivariant block.base hfour]
      rfl
    _ = FourPointBlockTranslationKernel.kernel
        block.map block.map_equivariant block.base hfour :=
      (MonoidHom.ker_rangeRestrict (FourPointBlockAffineCoordinates.linearMap block.map block.map_equivariant block.base hfour)).symm

theorem normalGen_translation_le_half (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2)
    (hO : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) ≠ ⊥) :
    MarkedC4.normalGen (Compression.kernel
      (OriginalBlockOrdinaryCompressionState.initialState J block).rho (QuotientGroup.mk' P.V)) ≤
        Nat.card block.Points / 2 := by
  rw [compression_kernel_eq_native J block P hfour hp]
  let C := FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour
  by_cases hsingle : ∀ i : block.Points,
      BinaryPlaneOddKernelMultiplicityUniform.localKernel C i =
        BinaryPlaneOddKernelMultiplicityUniform.localKernel C block.base
  · exact FourPointBlockSingleKernelOrdinaryInduction.normalGen_kernel_le_half
      block.map block.map_equivariant block.base hfour hO hsingle
  · obtain ⟨i,hi⟩ := not_forall.mp hsingle
    exact FourPointBlockMultipleKernelOrdinaryInduction.normalGen_kernel_le_half
      block.map block.map_equivariant block.base hfour hO ⟨i,block.base,hi⟩

theorem genRank_le_half_add_quotient (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2)
    (hO : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) ≠ ⊥) :
    MarkedC4.genRank J ≤ MarkedC4.genRank (quotientState J block P).A +
      Nat.card block.Points / 2 := by
  let E := Compression.kernel (OriginalBlockOrdinaryCompressionState.initialState J block).rho
    (QuotientGroup.mk' P.V)
  let q : J →* J ⧸ E := QuotientGroup.mk' E
  letI : IsMulCommutative E := by
    let e : E ≃* FourPointBlockTranslationKernel.kernel
        block.map block.map_equivariant block.base hfour :=
      MulEquiv.subgroupCongr (compression_kernel_eq_native J block P hfour hp)
    have hcomm := FourPointBlockMultipleKernelOrdinaryInduction.kernel_isMulCommutative
      block.map block.map_equivariant block.base hfour
    refine { is_comm := ⟨?_⟩ }
    intro x y
    apply e.injective
    simpa only [map_mul] using hcomm.is_comm.comm (e x) (e y)
  letI : IsMulCommutative q.ker := by
    change IsMulCommutative (QuotientGroup.mk' E).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hh := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen q
    (QuotientGroup.mk'_surjective E)
  change MarkedC4.genRank J ≤ MarkedC4.genRank (quotientState J block P).A +
    MarkedC4.normalGen (QuotientGroup.mk' E).ker at hh
  rw [QuotientGroup.ker_mk'] at hh
  exact hh.trans (Nat.add_le_add_left
    (normalGen_translation_le_half J block P hfour hp hO) _)

end SymmetricSubgroupAsymptotics.OriginalFourPointSharedTranslationKernel
