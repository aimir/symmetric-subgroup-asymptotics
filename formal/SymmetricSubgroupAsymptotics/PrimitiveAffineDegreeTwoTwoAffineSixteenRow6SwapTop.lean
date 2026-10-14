import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffineGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19AffineTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop

/-! Exact shared diagonal/swap model for the retained two-affine row6. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup
abbrev V := Multiplicative Vector
abbrev φ := AffineModel.linAut R
abbrev Model := BinaryDiagonalSwap.Model φ
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row6.top

def singerElement : R := ⟨singer, PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem⟩
def frobeniusElement : R :=
  ⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius,
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius_mem⟩

def pointChart : Fin 16 ≃ Vector ⊕ Vector :=
  PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.pointChart

def literalAction : Model →* Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp
    (BinaryDiagonalSwap.permutationAction φ (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (BinaryDiagonalSwap.permutationAction_injective φ _ (AffineModel.action_injective R))

def vector (n : ℕ) : V := Multiplicative.ofAdd (binaryVectorOfMask 3 n)

def modelGenerators : Fin 12 → Model :=
  ![inl (vector 3, 1), inl (vector 6, 1), inl (vector 1, 1),
    inl (1, vector 3), inl (1, vector 6), inl (1, vector 1),
    inl (vector 1, 1), inl (vector 4, 1), inl (vector 7, 1),
    BinaryDiagonalSwap.affineDiagonal R singerElement,
    BinaryDiagonalSwap.affineDiagonal R (singerElement ^ 5 * frobeniusElement),
    ⟨(vector 2, 1), (singerElement * frobeniusElement, C2Wreath.gen)⟩]

theorem generators_binding (i : Fin 12) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row6Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalFrobenius : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row6Generators 9 ^ 2 *
    DegreeTwoTwoAffineSixteenInterfaces.row6Generators 10

theorem linear_generator_words (i : Fin 2) :
    literalAction (BinaryDiagonalSwap.affineDiagonal R
      ⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators i,
        Subgroup.subset_closure (Set.mem_range_self i)⟩) =
      ![DegreeTwoTwoAffineSixteenInterfaces.row6Generators 9, literalFrobenius] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def swapWord : Equiv.Perm (Fin 16) :=
  (DegreeTwoTwoAffineSixteenInterfaces.row6Generators 9 ^ 3 *
      DegreeTwoTwoAffineSixteenInterfaces.row6Generators 10)⁻¹ *
    (DegreeTwoTwoAffineSixteenInterfaces.row6Generators 6 *
      DegreeTwoTwoAffineSixteenInterfaces.row6Generators 7 *
      DegreeTwoTwoAffineSixteenInterfaces.row6Generators 8) *
    DegreeTwoTwoAffineSixteenInterfaces.row6Generators 11

theorem swap_binding : literalAction (inr (1, C2Wreath.gen)) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : literalAction.range = Top := by
  let K : Subgroup Model := Top.comap literalAction
  have hg (i : Fin 12) : DegreeTwoTwoAffineSixteenInterfaces.row6Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hf : literalFrobenius ∈ Top := Top.mul_mem (Top.pow_mem (hg 9) 2) (hg 10)
  have hlinear (r : R) : BinaryDiagonalSwap.affineDiagonal R r ∈ K := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators
      PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators
      (literalAction.comp (BinaryDiagonalSwap.affineDiagonal R)) Top _ r
    intro i
    change literalAction (BinaryDiagonalSwap.affineDiagonal R _) ∈ Top
    rw [linear_generator_words]
    fin_cases i
    · exact hg 9
    · exact hf
  have ht : BinaryDiagonalSwap.affineFirstTranslation R
      (Multiplicative.ofAdd firstVector) ∈ K := by
    change literalAction (modelGenerators 2) ∈ Top
    rw [generators_binding]
    exact hg 2
  have hswap : (inr (1, C2Wreath.gen) : Model) ∈ K := by
    change literalAction (inr (1, C2Wreath.gen)) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem
      (Top.mul_mem (Top.inv_mem (Top.mul_mem (Top.pow_mem (hg 9) 3) (hg 10)))
        (Top.mul_mem (Top.mul_mem (hg 6) (hg 7)) (hg 8))) (hg 11)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact BinaryDiagonalSwap.affine_model_mem_of_generators R
      PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem K hlinear ht hswap g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop
end SymmetricSubgroupAsymptotics

end
