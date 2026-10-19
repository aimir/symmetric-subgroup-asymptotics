import SymmetricSubgroupAsymptotics.TwoTripleSignedAffineCoordinates

/-! The signed two-coordinate action is faithful. This is a receipt on
the fixed eight-element upper, not on any subgroup or normal catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleSignedUpperFaithful
open TwoTripleSignedUpperLinearAction

private def coordinates : Upper ≃ (Binary × Binary) × Binary where
  toFun g := (g.left,g.right)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance faithfulUpperFintype : Fintype Upper :=
  Fintype.ofEquiv ((Binary × Binary) × Binary) coordinates.symm

private theorem receipt : ∀ g h : Upper,
    (∀ v : Vector, representation g v=representation h v) → g=h := by
  decide +kernel

theorem faithful : Function.Injective representation := by
  intro g h he
  apply receipt g h
  intro v
  exact LinearMap.congr_fun he v

private theorem power_four : ∀ g : Upper, g^4=1 := by decide +kernel

theorem binary (U : Subgroup Upper) : IsPGroup 2 U := by
  intro u
  refine ⟨2,?_⟩
  apply Subtype.ext
  exact power_four u.val

end SymmetricSubgroupAsymptotics.TwoTripleSignedUpperFaithful
