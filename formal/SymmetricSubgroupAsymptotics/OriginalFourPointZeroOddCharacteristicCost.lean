import SymmetricSubgroupAsymptotics.FourPointBlockPrimitiveZeroOddImage
import SymmetricSubgroupAsymptotics.WreathCompressionKernelCongruence
import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.ActualWreathChooseDivisorCapacity

/-! Zero odd image leaves only the literal translation-head capacity and
the actual top rank. The original compression quotient is identified with
the native linear image by equality of the SAME local kernels. No coarse
Tracey, smaller-action generator input, or independent GL2 factor charge
is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalFourPointZeroOddCharacteristicCost
open OriginalAffineBlockCharacteristicHead PermutationalWreathProduct

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

def quotientStateEquivLinearImage (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2) :
    (quotientState J block P).A ≃*
      FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour := by
  let rho := ActualBlockWreathEmbedding.embedding block.map block.map_equivariant block.base
  let psi := FourPointBlockPrimitiveZeroOddImage.localLinear block.map block.map_equivariant block.base hfour
  have hker : (QuotientGroup.mk' P.V).ker = psi.ker := by
    have hh := PrimitiveAffineFourNativeLinearKernel.linearHom_kernel P
      (FourPointBlockAffineCoordinates.fibreChart block.map block.base hfour) block.component_preprimitive
      (P.elementaryChart block.component_preprimitive) hp
    exact (QuotientGroup.ker_mk' P.V).trans hh.symm
  let e := WreathCompressionKernelCongruence.quotientEquivImage rho
    (QuotientGroup.mk' P.V) psi hker
  exact e.trans (MulEquiv.subgroupCongr
    (congrArg (fun f : J →* FourPointBlockAffineCoordinates.LinearFrame (G := J) (X := block.Points) => f.range)
      (FourPointBlockPrimitiveZeroOddImage.linearMap_eq_compression
        block.map block.map_equivariant block.base hfour).symm))

theorem quotientState_genRank_eq_top (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2)
    (hzero : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥) :
    MarkedC4.genRank (quotientState J block P).A = MarkedC4.genRank block.Top := by
  let C := FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour
  let f : C →* block.Top := rightHom.comp C.subtype
  have hf : Function.Injective f :=
    FourPointBlockPrimitiveZeroOddImage.top_injective_of_oddKernel_eq_bot block.map block.map_equivariant block.base hfour
      P block.component_preprimitive (P.elementaryChart block.component_preprimitive) hp hzero
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g,hg⟩ := q.property
    refine ⟨FourPointBlockAffineCoordinates.projection block.map block.map_equivariant block.base hfour g,?_⟩
    change (FourPointBlockAffineCoordinates.linearMap block.map block.map_equivariant block.base hfour g).right = q
    rw [FourPointBlockAffineCoordinates.linearMap_right]
    exact Subtype.ext hg
  let e := (quotientStateEquivLinearImage J block P hfour hp).trans
    (MulEquiv.ofBijective f ⟨hf,hsurj⟩)
  exact CoprimeNilpotentProductGenerators.genRank_mulEquiv e

theorem genRank_le_head_add_top (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2)
    (hzero : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥)
    (i : block.Points) :
    MarkedC4.genRank J ≤ (headCharge J block P i).capacity + MarkedC4.genRank block.Top := by
  have hh := ActualWreathElementaryOrdinaryStep.genRank_le_capacity_add_next
    (OriginalBlockOrdinaryCompressionState.initialState J block)
    (QuotientGroup.mk' P.V) (translationChart J block P) (QuotientGroup.mk'_surjective P.V) i
  change MarkedC4.genRank J ≤ (headCharge J block P i).capacity +
    MarkedC4.genRank (quotientState J block P).A at hh
  rwa [quotientState_genRank_eq_top J block P hfour hp hzero] at hh

theorem genRank_le_primary_choose (hfour : Nat.card block.Fibre = 4) (hp : P.p = 2)
    (hzero : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥)
    (i : block.Points) (a : ℕ) (hd : 2 ^ a ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ) *
      Fintype.card block.Points * ActualWreathChooseDivisorCapacity.primaryRate 2 a +
        MarkedC4.genRank block.Top := by
  have hdiv : (translationChart J block P).p ^ a ∣ Fintype.card block.Points := by
    change P.p ^ a ∣ Fintype.card block.Points
    simpa only [hp] using hd
  have hc := ActualWreathChooseDivisorCapacity.layerCapacity_primary_choose
    (OriginalBlockOrdinaryCompressionState.initialState J block)
    (QuotientGroup.mk' P.V) (translationChart J block P) i a hdiv
  change ((headCharge J block P i).capacity : ℝ) ≤
    (translationDimension J block P : ℝ) * Fintype.card block.Points *
      ActualWreathChooseDivisorCapacity.primaryRate P.p a at hc
  rw [hp] at hc
  have hr : (MarkedC4.genRank J : ℝ) ≤ ((headCharge J block P i).capacity : ℝ) +
      MarkedC4.genRank block.Top := by
    exact_mod_cast genRank_le_head_add_top J block P hfour hp hzero i
  linarith

end SymmetricSubgroupAsymptotics.OriginalFourPointZeroOddCharacteristicCost
