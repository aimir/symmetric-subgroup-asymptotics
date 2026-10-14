import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSingerPairComplementGeneration
import SymmetricSubgroupAsymptotics.BinarySingerWreathAffineNormalGenerators
import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop

/-! The exact two original paired-Singer tops share one affine image
construction. False selects row8, true selects row9. Every literal
coordinate, complement word, and swap word is retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRows8And9SingerTops

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev R := PrimitiveAffineDegreeTwoSingerPairComplements.R
abbrev V := Multiplicative Vector
abbrev C (twisted : Bool) := PrimitiveAffineDegreeTwoSingerPairComplements.Complement twisted
abbrev phi (twisted : Bool) := WreathAffineCoordinates.restrictedAction (AffineModel.linAut R) (C twisted)
abbrev Model (twisted : Bool) := WreathAffineCoordinates.Model (AffineModel.linAut R) (C twisted)

def row (twisted : Bool) : DegreeTwoPairTopFiniteInterface 16 :=
  if twisted then DegreeTwoTwoAffineSixteenInterfaces.row9 else DegreeTwoTwoAffineSixteenInterfaces.row8

abbrev Top (twisted : Bool) := (row twisted).top

def literalGenerators (twisted : Bool) : Fin 14 → Equiv.Perm (Fin 16) :=
  if twisted then DegreeTwoTwoAffineSixteenInterfaces.row9Generators
  else DegreeTwoTwoAffineSixteenInterfaces.row8Generators

theorem top_eq_closure (twisted : Bool) : Top twisted = Subgroup.closure (Set.range (literalGenerators twisted)) := by
  cases twisted <;> rfl

abbrev pointChart := PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.pointChart

def literalAction (twisted : Bool) : Model twisted →* Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp
    (WreathAffineCoordinates.permutationAction (AffineModel.linAut R) (C twisted)
      (AffineModel.action R))

theorem literalAction_injective (twisted : Bool) : Function.Injective (literalAction twisted) :=
  pointChart.symm.permCongrHom.injective.comp
    (WreathAffineCoordinates.permutationAction_injective (AffineModel.linAut R) (C twisted)
      (AffineModel.action R) (AffineModel.action_injective R))

def complementGenerator (twisted : Bool) (i : Fin 4) : C twisted :=
  ⟨PrimitiveAffineDegreeTwoSingerPairComplements.generators twisted i,
    PrimitiveAffineDegreeTwoSingerPairComplements.generators_mem twisted i⟩

def vector (n : ℕ) : V := Multiplicative.ofAdd (binaryVectorOfMask 3 n)

def modelGenerators (twisted : Bool) : Fin 14 → Model twisted :=
  ![inr (complementGenerator twisted 0),
    inl (vector 3, 1), inl (vector 6, 1), inl (vector 1, 1),
    inr (complementGenerator twisted 1),
    inl (1, vector 3), inl (1, vector 6), inl (1, vector 1),
    inl (vector 1, 1), inl (vector 4, 1), inl (vector 7, 1),
    inr (complementGenerator twisted 0),
    inr (complementGenerator twisted 0 ^ 5 *
      complementGenerator twisted 1 ^ (if twisted then 1 else 5) * complementGenerator twisted 2),
    inl (vector 6, 1) * inr (complementGenerator twisted 0 ^ 3 *
      complementGenerator twisted 1 ^ (if twisted then 0 else 1) *
      complementGenerator twisted 2 * complementGenerator twisted 3)]

theorem generators_binding (twisted : Bool) (i : Fin 14) :
    literalAction twisted (modelGenerators twisted i) = literalGenerators twisted i := by
  cases twisted <;> apply Equiv.ext <;> intro x <;> revert i x <;> decide +kernel

def swapWord (twisted : Bool) : Equiv.Perm (Fin 16) :=
  (literalGenerators twisted 0 ^ 5 * literalGenerators twisted 4 ^ (if twisted then 6 else 3) *
      literalGenerators twisted 12)⁻¹ *
    (literalGenerators twisted 8 * literalGenerators twisted 10) * literalGenerators twisted 13

def complementWords (twisted : Bool) : Fin 4 → Equiv.Perm (Fin 16) :=
  ![literalGenerators twisted 0, literalGenerators twisted 4,
    literalGenerators twisted 0 ^ 2 * literalGenerators twisted 4 ^ (if twisted then 6 else 2) *
      literalGenerators twisted 12, swapWord twisted]

theorem complement_words_binding (twisted : Bool) (i : Fin 4) :
    literalAction twisted (inr (complementGenerator twisted i)) = complementWords twisted i := by
  cases twisted <;> apply Equiv.ext <;> intro x <;> revert i x <;> decide +kernel

theorem irreducible (twisted : Bool) : IrreducibleAbelianSemidirect.Irreducible (phi twisted) :=
  BinarySingerWreathAffineNormalGenerators.irreducible R
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem (C twisted)
    (PrimitiveAffineDegreeTwoSingerPairComplements.firstSinger_mem twisted)
    (PrimitiveAffineDegreeTwoSingerPairComplements.pure_swap_mem twisted)

theorem model_normal_generators (twisted : Bool) :
    ∀ N : Subgroup (Model twisted), N.Normal →
      ∃ x : Fin 2 → Model twisted, Subgroup.normalClosure (Set.range x) = N :=
  BinarySingerWreathAffineNormalGenerators.normal_generating_tuples R
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem (C twisted)
    (PrimitiveAffineDegreeTwoSingerPairComplements.firstSinger_mem twisted)
    (PrimitiveAffineDegreeTwoSingerPairComplements.pure_swap_mem twisted) (by decide)
    (PrimitiveAffineDegreeTwoSingerPairComplements.normal_generating_pairs twisted)

theorem action_range (twisted : Bool) : (literalAction twisted).range = Top twisted := by
  let K : Subgroup (Model twisted) := (Top twisted).comap (literalAction twisted)
  have hg (i : Fin 14) : literalGenerators twisted i ∈ Top twisted := by
    rw [top_eq_closure]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hwords (i : Fin 4) : complementWords twisted i ∈ Top twisted := by
    fin_cases i
    · exact hg 0
    · exact hg 4
    · exact (Top twisted).mul_mem
        ((Top twisted).mul_mem ((Top twisted).pow_mem (hg 0) 2)
          ((Top twisted).pow_mem (hg 4) _)) (hg 12)
    · exact (Top twisted).mul_mem
        ((Top twisted).mul_mem
          ((Top twisted).inv_mem ((Top twisted).mul_mem
            ((Top twisted).mul_mem ((Top twisted).pow_mem (hg 0) 5)
              ((Top twisted).pow_mem (hg 4) _)) (hg 12)))
          ((Top twisted).mul_mem (hg 8) (hg 10))) (hg 13)
  have hcomplement (c : C twisted) : (inr c : Model twisted) ∈ K := by
    apply PrimitiveAffineDegreeTwoSingerPairComplements.hom_mem_of_generators twisted
      ((literalAction twisted).comp (inr : C twisted →* Model twisted)) (Top twisted) _ c
    intro i
    change literalAction twisted (inr (complementGenerator twisted i)) ∈ Top twisted
    rw [complement_words_binding]
    exact hwords i
  have ht : (inl (Multiplicative.ofAdd firstVector, 1) : Model twisted) ∈ K := by
    change literalAction twisted (modelGenerators twisted 3) ∈ Top twisted
    rw [generators_binding]
    exact hg 3
  have hne : (Multiplicative.ofAdd firstVector, (1 : V)) ≠ 1 := by
    intro h
    exact firstVector_ne_zero (congrArg (fun v : V × V ↦ v.1.toAdd) h)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact IrreducibleAbelianSemidirect.mem_of_complement_and_translation (phi twisted)
      (irreducible twisted) K hcomplement _ hne ht g
  · rw [top_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators twisted i, generators_binding twisted i⟩

def modelEquiv (twisted : Bool) : Model twisted ≃* Top twisted :=
  (MonoidHom.ofInjective (f := literalAction twisted) (literalAction_injective twisted)).trans
    (MulEquiv.subgroupCongr (action_range twisted))

end PrimitiveAffineDegreeTwoTwoAffineSixteenRows8And9SingerTops
end SymmetricSubgroupAsymptotics

end
