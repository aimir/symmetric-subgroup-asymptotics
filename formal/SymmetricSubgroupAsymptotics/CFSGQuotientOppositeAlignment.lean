import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Transitivity on actual opposite subgroup conjugates descends through
a surjection injective on the positive subgroup. No automorphism of the
quotient is lifted through the surjection. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment
open CFSGSubgroupConjugateRestriction
variable {G H : Type*} [Group G] [Group H]

theorem opposite_alignment_map (f : G→*H) (hf : Function.Surjective f)
    (U V B : Subgroup G) (hU : Function.Injective (f.comp U.subtype))
    (halign : ∀g : G,U⊓U.map (MulAut.conj g).toMonoidHom=⊥→
      ∃b∈B,U.map (MulAut.conj g).toMonoidHom=V.map (MulAut.conj b).toMonoidHom)
    (q : H)
    (hdisj : U.map f⊓(U.map f).map (MulAut.conj q).toMonoidHom=⊥) :
    ∃b∈B.map f,(U.map f).map (MulAut.conj q).toMonoidHom=
      (V.map f).map (MulAut.conj b).toMonoidHom := by
  obtain ⟨g,rfl⟩ := hf q
  have hpre : U⊓U.map (MulAut.conj g).toMonoidHom=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hfx : f x∈U.map f⊓(U.map f).map (MulAut.conj (f g)).toMonoidHom := by
      refine ⟨⟨x,hx.1,rfl⟩,?_⟩
      rw [←map_conjugate]
      exact ⟨x,hx.2,rfl⟩
    rw [hdisj,Subgroup.mem_bot] at hfx
    have hUeq : f.comp U.subtype ⟨x,hx.1⟩=f.comp U.subtype 1 := by
      change f x=f 1
      simpa only [map_one] using hfx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hU hUeq))
  obtain ⟨b,hb,he⟩ := halign g hpre
  refine ⟨f b,⟨b,hb,rfl⟩,?_⟩
  have hh := congrArg (fun S : Subgroup G=>S.map f) he
  dsimp only at hh
  rwa [map_conjugate,map_conjugate] at hh

end SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment
