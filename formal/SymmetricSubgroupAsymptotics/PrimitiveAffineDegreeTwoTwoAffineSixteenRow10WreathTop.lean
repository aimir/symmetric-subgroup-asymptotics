import SymmetricSubgroupAsymptotics.BinarySingerAffineWreathGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19AffineTop

/-! The original row10 is the wreath of its checked local affine group.
All bindings retain the original sixteen point labels and generator order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow10WreathTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup
abbrev Local := AffineModel.Aff R
abbrev Model := C2Wreath.W Local
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row10.top

def first : Local →* Model := C2Wreath.firstFactor
def second : Local →* Model := (inl : Local × Local →* Model).comp (MonoidHom.inr _ _)

def pointChart : Fin 16 ≃ Vector ⊕ Vector :=
  PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.pointChart

def literalAction : Model →* Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp (C2Wreath.action (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (C2Wreath.action_injective _ (AffineModel.action_injective R))

def translation (n : ℕ) : Local := inl (Multiplicative.ofAdd (binaryVectorOfMask 3 n))
def singerElement : R := ⟨singer, PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem⟩
def singerLocal : Local := inr singerElement
def frobeniusElement : R :=
  ⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius,
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius_mem⟩
def adjustedFrobenius : Local := inr (singerElement ^ 5 * frobeniusElement)

def modelGenerators : Fin 16 → Model :=
  ![first (translation 1), first (translation 4), first (translation 7),
    first singerLocal, first adjustedFrobenius,
    second (translation 1), second (translation 4), second (translation 7),
    second singerLocal, second adjustedFrobenius,
    first (translation 1), first (translation 4), first (translation 7),
    first singerLocal, first adjustedFrobenius,
    first (translation 2) * inr C2Wreath.gen]

theorem generators_binding (i : Fin 16) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row10Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalFrobenius : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row10Generators 3 ^ 2 *
    DegreeTwoTwoAffineSixteenInterfaces.row10Generators 4

theorem linear_generator_words (i : Fin 2) :
    literalAction (first (inr
      (⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators i, Subgroup.subset_closure (Set.mem_range_self i)⟩ : R))) =
        ![DegreeTwoTwoAffineSixteenInterfaces.row10Generators 3, literalFrobenius] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def swapWord : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row10Generators 0 *
    DegreeTwoTwoAffineSixteenInterfaces.row10Generators 1 *
    DegreeTwoTwoAffineSixteenInterfaces.row10Generators 2 *
    DegreeTwoTwoAffineSixteenInterfaces.row10Generators 15

theorem swap_binding : literalAction (inr C2Wreath.gen) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : literalAction.range = Top := by
  let K : Subgroup Model := Top.comap literalAction
  have hg (i : Fin 16) : DegreeTwoTwoAffineSixteenInterfaces.row10Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hf : literalFrobenius ∈ Top := Top.mul_mem (Top.pow_mem (hg 3) 2) (hg 4)
  have hlinear (r : R) : first (inr r) ∈ K := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators
      (literalAction.comp (first.comp (inr : R →* Local))) Top _ r
    intro i
    change literalAction (first (inr _)) ∈ Top
    rw [linear_generator_words]
    fin_cases i
    · exact hg 3
    · exact hf
  have ht : first (inl (Multiplicative.ofAdd firstVector)) ∈ K := by
    change literalAction (modelGenerators 0) ∈ Top
    rw [generators_binding]
    exact hg 0
  have hswap : (inr C2Wreath.gen : Model) ∈ K := by
    change literalAction (inr C2Wreath.gen) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem (Top.mul_mem (Top.mul_mem (hg 0) (hg 1)) (hg 2)) (hg 15)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact BinarySingerAffineWreathGeneration.mem_of_generators R PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem
      K hlinear ht hswap g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow10WreathTop
end SymmetricSubgroupAsymptotics

end
