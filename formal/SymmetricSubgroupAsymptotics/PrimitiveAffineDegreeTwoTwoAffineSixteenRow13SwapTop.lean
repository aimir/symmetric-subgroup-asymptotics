import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffineGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces

/-! Exact shared diagonal/swap model for the retained two-affine row13. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := Row20.linearGroup
abbrev V := Multiplicative Vector
abbrev φ := AffineModel.linAut R
abbrev Model := BinaryDiagonalSwap.Model φ
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row13.top

def singerElement : R := ⟨singer, Row20.singer_mem⟩
def swapElement : R := ⟨swap, Row20.swap_mem⟩
def transvection : R := singerElement ^ 4 * swapElement * (singerElement ^ 4)⁻¹
def coordinateRotation : R := (transvection * singerElement) ^ 2
def upperSwap : R := coordinateRotation * swapElement * coordinateRotation⁻¹

def pointChart : Fin 16 ≃ Vector ⊕ Vector :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr pointEquiv.symm pointEquiv.symm)

def literalAction : Model →* Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp
    (BinaryDiagonalSwap.permutationAction φ (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (BinaryDiagonalSwap.permutationAction_injective φ _ (AffineModel.action_injective R))

def vector (n : ℕ) : V := Multiplicative.ofAdd (binaryVectorOfMask 3 n)

def modelGenerators : Fin 12 → Model :=
  ![inl (vector 1, 1), inl (vector 4, 1), inl (vector 2, 1),
    inl (1, vector 1), inl (1, vector 4), inl (1, vector 2),
    inl (vector 1, 1), inl (vector 2, 1), inl (vector 4, 1),
    BinaryDiagonalSwap.affineDiagonal R transvection,
    BinaryDiagonalSwap.affineDiagonal R coordinateRotation,
    ⟨(vector 7, 1), (upperSwap, C2Wreath.gen)⟩]

theorem generators_binding (i : Fin 12) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row13Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalSinger : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row13Generators 9 *
    DegreeTwoTwoAffineSixteenInterfaces.row13Generators 10 ^ 2

def literalSwap : Equiv.Perm (Fin 16) :=
  (literalSinger ^ 4)⁻¹ * DegreeTwoTwoAffineSixteenInterfaces.row13Generators 9 *
    literalSinger ^ 4

theorem linear_generator_words (i : Fin 2) :
    literalAction (BinaryDiagonalSwap.affineDiagonal R
      ⟨Row20.linearGenerators i, Subgroup.subset_closure (Set.mem_range_self i)⟩) =
        ![literalSinger, literalSwap] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def swapWord : Equiv.Perm (Fin 16) :=
  (DegreeTwoTwoAffineSixteenInterfaces.row13Generators 10 * literalSwap *
      (DegreeTwoTwoAffineSixteenInterfaces.row13Generators 10)⁻¹)⁻¹ *
    (DegreeTwoTwoAffineSixteenInterfaces.row13Generators 6 *
      DegreeTwoTwoAffineSixteenInterfaces.row13Generators 7 *
      DegreeTwoTwoAffineSixteenInterfaces.row13Generators 8) *
    DegreeTwoTwoAffineSixteenInterfaces.row13Generators 11

theorem swap_binding : literalAction (inr (1, C2Wreath.gen)) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : literalAction.range = Top := by
  let K : Subgroup Model := Top.comap literalAction
  have hg (i : Fin 12) : DegreeTwoTwoAffineSixteenInterfaces.row13Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hs : literalSinger ∈ Top := Top.mul_mem (hg 9) (Top.pow_mem (hg 10) 2)
  have hb : literalSwap ∈ Top :=
    Top.mul_mem (Top.mul_mem (Top.inv_mem (Top.pow_mem hs 4)) (hg 9)) (Top.pow_mem hs 4)
  have hlinear (r : R) : BinaryDiagonalSwap.affineDiagonal R r ∈ K := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators Row20.linearGenerators
      (literalAction.comp (BinaryDiagonalSwap.affineDiagonal R)) Top _ r
    intro i
    change literalAction (BinaryDiagonalSwap.affineDiagonal R _) ∈ Top
    rw [linear_generator_words]
    fin_cases i
    · exact hs
    · exact hb
  have ht : BinaryDiagonalSwap.affineFirstTranslation R
      (Multiplicative.ofAdd firstVector) ∈ K := by
    change literalAction (modelGenerators 0) ∈ Top
    rw [generators_binding]
    exact hg 0
  have hswap : (inr (1, C2Wreath.gen) : Model) ∈ K := by
    change literalAction (inr (1, C2Wreath.gen)) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem
      (Top.mul_mem (Top.inv_mem (Top.mul_mem (Top.mul_mem (hg 10) hb) (Top.inv_mem (hg 10))))
        (Top.mul_mem (Top.mul_mem (hg 6) (hg 7)) (hg 8))) (hg 11)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact BinaryDiagonalSwap.affine_model_mem_of_generators R Row20.singer_mem
      K hlinear ht hswap g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop
end SymmetricSubgroupAsymptotics

end
