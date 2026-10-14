import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwistedSingerModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop

/-! Exact pairing-graph affine model for the retained two-affine row7. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow7TwistedTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PrimitiveAffineDegreeTwoTwistedSingerModels
open PrimitiveAffineDegreeTwoTwistedSingerModels.Row7
open PairedFormSwapAffine

abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row7.top
def pointChart : Fin 16 ≃ Vector ⊕ Vector := PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.pointChart

def literalAction : PrimitiveAffineDegreeTwoTwistedSingerModels.Row7.Model →*
    Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp
    (permutationAction φ form7 form7_symmetric (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (permutationAction_injective φ form7 form7_symmetric _ (AffineModel.action_injective R))

def vector (n : ℕ) : V := Multiplicative.ofAdd (binaryVectorOfMask 3 n)

def modelGenerators : Fin 12 → PrimitiveAffineDegreeTwoTwistedSingerModels.Row7.Model :=
  ![inl (vector 3, 1), inl (vector 6, 1), inl (vector 1, 1),
    inl (1, vector 3), inl (1, vector 6), inl (1, vector 1),
    inl (vector 1, 1), inl (vector 4, 1), inl (vector 7, 1),
    pairInr φ form7 form7_symmetric singerPair,
    pairInr φ form7 form7_symmetric (singerPair ^ 5 * frobeniusPair),
    ⟨(vector 5, 1), ⟨singerPair ^ 3 * frobeniusPair, C2Wreath.gen⟩⟩]

theorem generators_binding (i : Fin 12) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row7Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def linearWords : Fin 2 → Equiv.Perm (Fin 16) :=
  ![DegreeTwoTwoAffineSixteenInterfaces.row7Generators 9,
    DegreeTwoTwoAffineSixteenInterfaces.row7Generators 9 ^ 2 *
      DegreeTwoTwoAffineSixteenInterfaces.row7Generators 10]

theorem linear_generator_words (i : Fin 2) :
    literalAction (pairInr φ form7 form7_symmetric (pairs i)) = linearWords i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def swapWord : Equiv.Perm (Fin 16) :=
  (DegreeTwoTwoAffineSixteenInterfaces.row7Generators 9 ^ 5 *
      DegreeTwoTwoAffineSixteenInterfaces.row7Generators 10)⁻¹ *
    (DegreeTwoTwoAffineSixteenInterfaces.row7Generators 6 *
      DegreeTwoTwoAffineSixteenInterfaces.row7Generators 7) *
    DegreeTwoTwoAffineSixteenInterfaces.row7Generators 11

theorem swap_binding : literalAction (inr (inr C2Wreath.gen)) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : literalAction.range = Top := by
  let K : Subgroup PrimitiveAffineDegreeTwoTwistedSingerModels.Row7.Model :=
    Top.comap literalAction
  have hg (i : Fin 12) : DegreeTwoTwoAffineSixteenInterfaces.row7Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hw : ∀ i, linearWords i ∈ Top := by
    intro i
    fin_cases i
    · exact hg 9
    · exact Top.mul_mem (Top.pow_mem (hg 9) 2) (hg 10)
  have hpair (p : PrimitiveAffineDegreeTwoTwistedSingerModels.Row7.Pair) :
      pairInr φ form7 form7_symmetric p ∈ K := by
    apply graph_hom_mem_of_generators PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators form7 form7_separates
      pairs pairs_first (literalAction.comp (pairInr φ form7 form7_symmetric)) Top _ p
    intro i
    change literalAction (pairInr φ form7 form7_symmetric (pairs i)) ∈ Top
    rw [linear_generator_words]
    exact hw i
  have ht : firstTranslation φ form7 form7_symmetric
      (Multiplicative.ofAdd firstVector) ∈ K := by
    change literalAction (modelGenerators 2) ∈ Top
    rw [generators_binding]
    exact hg 2
  have hswap : (inr (inr C2Wreath.gen) :
      PrimitiveAffineDegreeTwoTwistedSingerModels.Row7.Model) ∈ K := by
    change literalAction (inr (inr C2Wreath.gen)) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem
      (Top.mul_mem (Top.inv_mem (Top.mul_mem (Top.pow_mem (hg 9) 5) (hg 10)))
        (Top.mul_mem (hg 6) (hg 7))) (hg 11)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact affine_model_mem_of_generators R form7 form7_symmetric
      singerPair singerPair_first K hpair ht hswap g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : PrimitiveAffineDegreeTwoTwistedSingerModels.Row7.Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow7TwistedTop
end SymmetricSubgroupAsymptotics

end

