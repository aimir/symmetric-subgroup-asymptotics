import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwistedSingerModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop

/-! Exact pairing-graph affine model for the retained two-affine row14. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow14TwistedTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PrimitiveAffineDegreeTwoTwistedSingerModels
open PrimitiveAffineDegreeTwoTwistedSingerModels.Row14
open PairedFormSwapAffine

abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row14.top
def pointChart : Fin 16 ≃ Vector ⊕ Vector := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.pointChart

def literalAction : PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.Model →*
    Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp
    (permutationAction φ form168 form168_symmetric (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (permutationAction_injective φ form168 form168_symmetric _ (AffineModel.action_injective R))

def vector (n : ℕ) : V := Multiplicative.ofAdd (binaryVectorOfMask 3 n)

def modelGenerators : Fin 12 → PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.Model :=
  ![inl (vector 1, 1), inl (vector 4, 1), inl (vector 2, 1),
    inl (1, vector 1), inl (1, vector 4), inl (1, vector 2),
    inl (vector 1, 1), inl (vector 2, 1), inl (vector 4, 1),
    pairInr φ form168 form168_symmetric transvectionPair,
    pairInr φ form168 form168_symmetric rotationPair,
    ⟨(vector 7, 1), ⟨swapPair, C2Wreath.gen⟩⟩]

theorem generators_binding (i : Fin 12) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row14Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalSinger : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row14Generators 9 *
    DegreeTwoTwoAffineSixteenInterfaces.row14Generators 10 ^ 2

def literalSwap : Equiv.Perm (Fin 16) :=
  (literalSinger ^ 4)⁻¹ * DegreeTwoTwoAffineSixteenInterfaces.row14Generators 9 *
    literalSinger ^ 4

def linearWords : Fin 2 → Equiv.Perm (Fin 16) := ![literalSinger, literalSwap]

theorem linear_generator_words (i : Fin 2) :
    literalAction (pairInr φ form168 form168_symmetric (pairs i)) = linearWords i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def swapWord : Equiv.Perm (Fin 16) :=
  literalSwap⁻¹ *
    (DegreeTwoTwoAffineSixteenInterfaces.row14Generators 6 *
      DegreeTwoTwoAffineSixteenInterfaces.row14Generators 7 *
      DegreeTwoTwoAffineSixteenInterfaces.row14Generators 8) *
    DegreeTwoTwoAffineSixteenInterfaces.row14Generators 11

theorem swap_binding : literalAction (inr (inr C2Wreath.gen)) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : literalAction.range = Top := by
  let K : Subgroup PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.Model :=
    Top.comap literalAction
  have hg (i : Fin 12) : DegreeTwoTwoAffineSixteenInterfaces.row14Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hw : ∀ i, linearWords i ∈ Top := by
    have hs : literalSinger ∈ Top := Top.mul_mem (hg 9) (Top.pow_mem (hg 10) 2)
    intro i
    fin_cases i
    · exact hs
    · exact Top.mul_mem (Top.mul_mem (Top.inv_mem (Top.pow_mem hs 4)) (hg 9))
        (Top.pow_mem hs 4)
  have hpair (p : PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.Pair) :
      pairInr φ form168 form168_symmetric p ∈ K := by
    apply graph_hom_mem_of_generators Row20.linearGenerators form168 form168_separates
      pairs pairs_first (literalAction.comp (pairInr φ form168 form168_symmetric)) Top _ p
    intro i
    change literalAction (pairInr φ form168 form168_symmetric (pairs i)) ∈ Top
    rw [linear_generator_words]
    exact hw i
  have ht : firstTranslation φ form168 form168_symmetric
      (Multiplicative.ofAdd firstVector) ∈ K := by
    change literalAction (modelGenerators 0) ∈ Top
    rw [generators_binding]
    exact hg 0
  have hswap : (inr (inr C2Wreath.gen) :
      PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.Model) ∈ K := by
    change literalAction (inr (inr C2Wreath.gen)) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem
      (Top.mul_mem (Top.inv_mem (hw 1))
        (Top.mul_mem (Top.mul_mem (hg 6) (hg 7)) (hg 8))) (hg 11)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact affine_model_mem_of_generators R form168 form168_symmetric
      singerPair singerPair_first K hpair ht hswap g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow14TwistedTop
end SymmetricSubgroupAsymptotics

end

