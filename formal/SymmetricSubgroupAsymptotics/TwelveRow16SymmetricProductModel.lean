import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveKleinSplitSocles
import SymmetricSubgroupAsymptotics.TernaryFourDiagonalActions

/-! Selected local model pilot for the original row16. Two explicit
ternary eigenvectors carry independent Klein sign characters. All finite
checks below concern the displayed36-element source and12 original points;
no subgroup or normal-subgroup census is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelveRow16SymmetricProductModel
open SemidirectProduct
open TernaryFourBlockKleinSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

abbrev D := DihedralGroup 3
abbrev Source := D × D

def eigenA : Vector := fun i => ![1,1,2,2] i.toAdd
def eigenB : Vector := fun i => ![1,2,2,1] i.toAdd

private abbrev chart (g : D) := TernaryFourDiagonalActions.dihedralToModel g

def modelMap : Source →* Model false where
  toFun g :=
    ⟨Multiplicative.ofAdd (fun i =>
      eigenA i*(chart g.1).left.toAdd+eigenB i*(chart g.2).left.toAdd),
      ((chart g.1).right*(chart g.2).right,(chart g.1).right)⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      revert i
      decide +kernel
    · decide +kernel
  map_mul' := by
    intro g h
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      revert g h i
      decide +kernel
    · revert g h
      decide +kernel

def action : Source →* Equiv.Perm (Fin 12) := (literalAction false).comp modelMap

def lifts : Fin 3 → Source :=
  ![(DihedralGroup.r 2,DihedralGroup.r 2),
    (1,DihedralGroup.sr 0),(DihedralGroup.sr 0,DihedralGroup.sr 0)]

theorem bindings (i : Fin 3) : action (lifts i)=row16Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem action_injective : Function.Injective action := by
  have key : ∀ g h : Source,(∀ i : Fin 12,action g i=action h i) → g=h := by
    decide +kernel
  intro g h he
  exact key g h (fun i => congrArg (fun a : Equiv.Perm (Fin 12) => a i) he)

end SymmetricSubgroupAsymptotics.TwelveRow16SymmetricProductModel
