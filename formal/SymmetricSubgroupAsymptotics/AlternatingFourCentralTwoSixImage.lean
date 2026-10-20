import SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImage
import SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSocles
import SymmetricSubgroupAsymptotics.FourPointAlternatingGeneratorCover
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSixImage
abbrev Model := AlternatingFourCentralTwoSocles.Model
abbrev Bit := AlternatingFourCentralTwoSocles.C2
private def bitPerm : Bit →* Equiv.Perm (Fin 2) where
  toFun z := if z=1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' := by
    have h : ∀ z w : Bit,
      (if z*w=1 then (1 : Equiv.Perm (Fin 2)) else Equiv.swap 0 1)=
        (if z=1 then 1 else Equiv.swap 0 1)*(if w=1 then 1 else Equiv.swap 0 1) := by
      decide +kernel
    exact h
private def inclusion : Model →* DoubleSymmetricFourSixImage.Group where
  toFun m := (m.1.val,bitPerm m.2)
  map_one' := Prod.ext rfl bitPerm.map_one
  map_mul' m n := Prod.ext rfl (bitPerm.map_mul m.2 n.2)

def action : Model →* Equiv.Perm (Fin 6) := DoubleSymmetricFourSixImage.action.comp inclusion

theorem action_injective : Function.Injective action := by
  have hb : Function.Injective bitPerm := by
    have h : ∀ z w : Bit,bitPerm z=bitPerm w → z=w := by decide +kernel
    exact h
  intro m n h
  have he := DoubleSymmetricFourSixImage.action_injective h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact hb (congrArg Prod.snd he)

theorem pure_apply (p : alternatingGroup (Fin 4)) :
    action (p,1)=SymmetricFourTwelvePointSocles.edge p.val := by
  change SymmetricFourTwelvePointSocles.edge p.val *
    DoubleSymmetricFourSixImage.complement (bitPerm 1)=_
  rw [map_one,map_one,mul_one]

theorem central_apply : action (1,Multiplicative.ofAdd 1)=
    TwelvePointRemainingStructuralSymmetricSixActions.opposite := by
  apply Equiv.ext
  decide +kernel

variable {U : Type} [Group U] (top : U →* Equiv.Perm (Fin 6))
    (inside : ∀ u,∃ m : Model,action m=top u) (wa wb wz : U)
    (ha : top wa=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.a)
    (hb : top wb=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b)
    (hz : top wz=action (1,Multiplicative.ofAdd 1))

include ha hb hz in
private theorem action_mem (m : Model) : action m∈top.range := by
  have hp : SymmetricFourTwelvePointSocles.edge m.1.val∈top.range :=
    FourPointAlternatingGeneratorCover.alternating_le
      (top.range.comap SymmetricFourTwelvePointSocles.edge) ⟨wa,ha⟩ ⟨wb,hb⟩ m.1.property
  have hcases : ∀ z : Bit,z=1 ∨ z=Multiplicative.ofAdd 1 := by decide +kernel
  rcases m with ⟨p,z⟩
  rcases hcases z with rfl | rfl
  · rw [pure_apply]
    exact hp
  · have he : (p,Multiplicative.ofAdd (1 : ZMod 2))=
        (p,1)*(1,Multiplicative.ofAdd (1 : ZMod 2)) := by ext <;> simp
    rw [he,map_mul,pure_apply]
    exact top.range.mul_mem hp ⟨wz,hz⟩

def hom : Model →* top.range := action.codRestrict top.range (action_mem top wa wb wz ha hb hz)

def equiv : Model ≃* top.range := MulEquiv.ofBijective (hom top wa wb wz ha hb hz)
  ⟨fun _ _ h => action_injective (congrArg Subtype.val h),by
    intro u
    obtain ⟨v,hv⟩ := u.property
    obtain ⟨m,hm⟩ := inside v
    exact ⟨m,Subtype.ext (hm.trans hv)⟩⟩
end SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSixImage
