import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveKleinSplitSocles
import SymmetricSubgroupAsymptotics.TernaryFourDiagonalActions

/-! Selected local model pilot for the original row18. A constant ternary vector and a sign vector separate the
central cubic factor from the dihedral factor. All finite
checks below concern the displayed36-element source and12 original points;
no subgroup or normal-subgroup census is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelveRow18DihedralCentralModel
open SemidirectProduct
open TernaryFourBlockKleinSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

abbrev D := DihedralGroup 3
abbrev C3 := Multiplicative (ZMod 3)
abbrev Source := (D × C3) × Bit

def eigenA : Vector := fun i => ![1,1,1,1] i.toAdd
def eigenB : Vector := fun i => ![1,2,1,2] i.toAdd

private abbrev chart (g : D) := TernaryFourDiagonalActions.dihedralToModel g

def modelMap : Source →* Model false where
  toFun g :=
    ⟨Multiplicative.ofAdd (fun i =>
      eigenA i*g.1.2.toAdd+eigenB i*(chart g.1.1).left.toAdd),
      ((chart g.1.1).right,g.2)⟩
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
  ![((DihedralGroup.r 2,Multiplicative.ofAdd 2),1),
    ((DihedralGroup.sr 0,1),1),((1,1),Multiplicative.ofAdd 1)]

theorem bindings (i : Fin 3) : action (lifts i)=row18Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem action_injective : Function.Injective action := by
  have key : ∀ g h : Source,(∀ i : Fin 12,action g i=action h i) → g=h := by
    decide +kernel
  intro g h he
  exact key g h (fun i => congrArg (fun a : Equiv.Perm (Fin 12) => a i) he)

end SymmetricSubgroupAsymptotics.TwelveRow18DihedralCentralModel
