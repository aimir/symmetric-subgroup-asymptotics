import SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Data.Finite.Card

/-! A subgroup-preserving automorphism fixes the centre pointwise when
that literal subgroup centre has order two. No ambient innerness or
extension of an automorphism is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AutomorphismFixedOrderTwoCentre
open CFSGInvariantSubgroupCoordinateImage
variable {G A : Type*} [Group G] [Group A]

theorem apply_eq_self_of_card_two (hA : Nat.card A=2) (f : MulAut A) (x : A) :
    f x=x := by
  by_cases hx : x=1
  · simpa only [hx,map_one]
  · have hfx : f x≠1 := by
      intro he
      exact hx (f.injective (he.trans (map_one f).symm))
    obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
    exact (ha (f x) hfx).trans (ha x hx).symm

theorem fixes_subgroup_center (H : Subgroup G) (f : MulAut G)
    (hH : H.map f.toMonoidHom=H) (hZ : Nat.card (Subgroup.center H)=2)
    (z : Subgroup.center H) : f (z.val : G)=(z.val : G) := by
  have he := apply_eq_self_of_card_two hZ
    (Subgroup.centerCongr (restrictAut H f hH)) z
  exact congrArg (fun c : Subgroup.center H => (c.val : G)) he

end SymmetricSubgroupAsymptotics.AutomorphismFixedOrderTwoCentre
