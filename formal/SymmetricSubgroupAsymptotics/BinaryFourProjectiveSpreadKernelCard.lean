import SymmetricSubgroupAsymptotics.BinaryFourProjectiveSpread

/-! A faithful action on the actual five-plane spread has at most three
kernel elements. This strengthens cyclicity using the checked three
literal scalar alternatives; it is not an order/census input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourProjectiveSpread

theorem action_kernel_card_le_three
    {G : Type} [Group G] (rho : G →* LinearGroup) (hrho : Function.Injective rho)
    (f : G →* Equiv.Perm (Fin 5)) (e : LinearGroup)
    (hact : ∀ g : G, ∀ i : Fin 5,
      planeAction (rho g) (spread e i)=spread e (f g i)) : Nat.card f.ker ≤ 3 := by
  let kappa : f.ker →* LinearGroup :=
    (MulAut.conj e⁻¹).toMonoidHom.comp (rho.comp f.ker.subtype)
  have hc (g : f.ker) : ∃ j : Fin 3,kappa g=![1,scalar,scalar^2] j := by
    have hfixed : ∀ i : Fin 5,planeAction (kappa g) (plane i)=plane i := by
      intro i
      have hg : f g.val=1 := g.property
      have hi : planeAction (rho g.val) (spread e i)=spread e i := by
        rw [hact,hg]
        rfl
      change planeAction (e⁻¹*rho g.val*e) (plane i)=plane i
      calc
        planeAction (e⁻¹*rho g.val*e) (plane i)=
            planeAction e⁻¹ (planeAction (rho g.val) (planeAction e (plane i))) := by
          simp only [map_mul,Equiv.Perm.mul_apply]
        _=planeAction e⁻¹ (planeAction e (plane i)) := congrArg (planeAction e⁻¹) hi
        _=plane i := by rw [map_inv]; exact (planeAction e).symm_apply_apply _
    rcases fixed_classification (kappa g) hfixed with h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  choose code hcode using hc
  have hinj : Function.Injective code := by
    intro x y h
    apply Subtype.ext
    apply hrho
    apply (MulAut.conj e⁻¹).injective
    change kappa x=kappa y
    exact (hcode x).trans ((congrArg (fun j : Fin 3 => ![1,scalar,scalar^2] j) h).trans
      (hcode y).symm)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective code hinj

end SymmetricSubgroupAsymptotics.BinaryFourProjectiveSpread
