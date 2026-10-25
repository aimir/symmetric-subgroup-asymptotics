import SymmetricSubgroupAsymptotics.CentralModuloNormalInvolutionJoin
import Mathlib.Algebra.Group.Action.End

/-! An automorphism acting by inversion preserves every subgroup of the
layer. Its adjunction to an actual preserving subgroup therefore retains
the same invariant layer, without linearity over a larger field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.AutomorphismSubgroupInversionJoin
variable {P X : Type*} [Group P] [Group X]

theorem invariant_join (ψ : P →* MulAut X) (L : Subgroup P) (W : Subgroup X)
    (hL : ∀ g ∈ L, ∀ x ∈ W, ψ g x ∈ W) (t : P)
    (ht : ∀ x, ψ t x = x⁻¹) :
    ∀ g ∈ L ⊔ Subgroup.zpowers t, ∀ x ∈ W, ψ g x ∈ W := by
  letI : MulAction P X := MulAction.compHom X ψ
  have hLS : ∀ g ∈ L, g • (W : Set X) = (W : Set X) := by
    intro g hg
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hL g hg y hy
    · intro hx
      refine ⟨g⁻¹ • x,hL g⁻¹ (L.inv_mem hg) x hx,?_⟩
      exact smul_inv_smul g x
  have htS : t • (W : Set X) = (W : Set X) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change ψ t y ∈ W
      rw [ht]
      exact W.inv_mem hy
    · intro hx
      refine ⟨x⁻¹,W.inv_mem hx,?_⟩
      change ψ t x⁻¹ = x
      rw [ht,inv_inv]
  intro g hg x hx
  have hs := CentralModuloNormalInvolutionJoin.invariant_join L t (W : Set X) hLS htS g hg
  have he : ψ g x ∈ g • (W : Set X) := ⟨x,hx,rfl⟩
  rw [hs] at he
  exact he

end SymmetricSubgroupAsymptotics.AutomorphismSubgroupInversionJoin
