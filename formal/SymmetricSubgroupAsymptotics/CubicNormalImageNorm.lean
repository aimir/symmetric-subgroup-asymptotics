import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! A genuine three-conjugate norm identity descends to the SAME normal
image. Fixed-point-freeness needs no splitting or denominator choice. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicNormalImageNorm

theorem fixed_eq_one {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (V : Subgroup G)
    (L : Subgroup Q) (hpre : L.comap f≤V) (a : G)
    (hsq : ∀ v∈V, v^2=1)
    (hnorm : ∀ v∈V, v*(a*v*a⁻¹)*(a^2*v*(a^2)⁻¹)=1)
    (x : Q) (hx : x∈L) (hfix : f a*x*(f a)⁻¹=x) : x=1 := by
  obtain ⟨v,hv⟩ := hf x
  have hV : v∈V := hpre (by change f v∈L; rw [hv]; exact hx)
  have hx2 : x^2=1 := by
    have hh := congrArg f (hsq v hV)
    simpa only [map_pow,map_one,hv] using hh
  have hfix2 : (f a)^2*x*((f a)^2)⁻¹=x := by
    calc
      (f a)^2*x*((f a)^2)⁻¹=f a*(f a*x*(f a)⁻¹)*(f a)⁻¹ := by rw [pow_two]; group
      _=x := by rw [hfix,hfix]
  have hn := congrArg f (hnorm v hV)
  simp only [map_mul,map_inv,map_pow,map_one,hv] at hn
  rw [hfix,hfix2,← pow_two,hx2,one_mul] at hn
  exact hn

theorem card_le {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) (V : Subgroup G)
    (L : Subgroup Q) (hpre : L.comap f≤V) : Nat.card L≤Nat.card V := by
  have hL : L≤V.map f := by
    intro x hx
    obtain ⟨v,hv⟩ := hf x
    exact ⟨v,hpre (by change f v∈L; rw [hv]; exact hx),hv⟩
  have hli : Nat.card L≤Nat.card (V.map f) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hL) (Subgroup.inclusion_injective hL)
  let q : V →* V.map f := {
    toFun v := ⟨f v,⟨v,v.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' v w := Subtype.ext (map_mul f v.val w.val) }
  have hq : Function.Surjective q := by
    rintro ⟨x,v,hv,rfl⟩
    exact ⟨⟨v,hv⟩,rfl⟩
  exact hli.trans (Nat.card_le_card_of_surjective q hq)

end SymmetricSubgroupAsymptotics.CubicNormalImageNorm
