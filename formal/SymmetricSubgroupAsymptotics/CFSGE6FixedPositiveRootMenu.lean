import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The literal E6 diagram involution fixes at most twelve positive
integral roots. The finite menu is already complete by reflection
closure; this additional filter is checked by the kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGE6FixedPositiveRootMenu
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateFiniteRootMenu

def fixedMenu : Finset (Fin 6→ℤ) := CFSGE6FiniteRootMenu.menu.filter
  (fun x=>(∀i,0≤x i) ∧ ∀i,x (CFSG.Models.e6Twist i)=x i)

theorem fixed_menu_card : fixedMenu.card=12 := by decide +kernel

noncomputable section
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem fixed_positive_root_card_le :
    Nat.card {k:PositiveRoot CartanMatrix.E₆ //
      ∀i,k.val.val (CFSG.Models.e6Twist i)=k.val.val i}≤12 := by
  let f : {k:PositiveRoot CartanMatrix.E₆ //
      ∀i,k.val.val (CFSG.Models.e6Twist i)=k.val.val i}→fixedMenu := fun k=>
    ⟨k.val.val.val,Finset.mem_filter.mpr ⟨root_mem_menu CartanMatrix.E₆
      CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos CFSGE6FiniteRootMenu.menu
      CFSGE6FiniteRootMenu.negative_simple_mem CFSGE6FiniteRootMenu.reflection_closed k.val.val,
        k.val.property,k.property⟩⟩
  have hi:Function.Injective f:=by
    intro k l he
    apply Subtype.ext
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun z:fixedMenu=>z.val) he)
  have hc:Nat.card {k:PositiveRoot CartanMatrix.E₆ //
      ∀i,k.val.val (CFSG.Models.e6Twist i)=k.val.val i}≤fixedMenu.card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hi
  exact hc.trans_eq fixed_menu_card

end
end SymmetricSubgroupAsymptotics.CFSGE6FixedPositiveRootMenu
