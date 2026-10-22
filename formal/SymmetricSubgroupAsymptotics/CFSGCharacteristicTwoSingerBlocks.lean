import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.Abel

/-! The two actual three-dimensional A2 Singer block shapes in
characteristic two. This is only a coordinate-word lemma; no named
subgroup recognition or whole-root-space decomposition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoSingerBlocks
variable {K M : Type*} [CommRing K] [CharP K 2] [AddCommGroup M] [Module K M]

private theorem add_self_zero (R : Type*) [CommRing R] [CharP R 2]
    {V : Type*} [AddCommGroup V] [Module R V] (v : V) : v+v=0 := by
  calc
    v+v=(2:R) • v := (two_smul R v).symm
    _=0 := by rw [CharP.ofNat_eq_zero R 2,zero_smul]

omit [CharP K 2] in
private theorem fixes_successor (f : Module.End K M) (k : ℕ) (x : M)
    (hx : (f^k) x=x) : (f^k) (f x)=f x := by
  have hh := DFunLike.congr_fun ((Commute.refl f).pow_left k).eq x
  change (f^k) (f x)=f ((f^k) x) at hh
  simpa only [hx] using hh

theorem first_companion_seven (f : Module.End K M) (x y z : M)
    (hx : f x=y) (hy : f y=z) (hz : f z=x+y) :
    (f^7) x=x ∧ (f^7) y=y ∧ (f^7) z=z := by
  have hmain : (f^7) x=x+(y+y)+(z+z) := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hx,hy,hz,map_add]
    abel
  have h7x : (f^7) x=x := by
    simpa only [add_self_zero K,add_zero] using hmain
  have h7y : (f^7) y=y := by simpa only [hx] using fixes_successor f 7 x h7x
  have h7z : (f^7) z=z := by simpa only [hy] using fixes_successor f 7 y h7y
  exact ⟨h7x,h7y,h7z⟩

theorem second_companion_seven (f : Module.End K M) (x y z : M)
    (hx : f x=y) (hy : f y=z) (hz : f z=x+z) :
    (f^7) x=x ∧ (f^7) y=y ∧ (f^7) z=z := by
  have hmain : (f^7) x=x+(x+x)+(y+y)+((z+z)+(z+z)) := by
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hx,hy,hz,map_add]
    abel
  have h7x : (f^7) x=x := by
    simpa only [add_self_zero K,add_zero] using hmain
  have h7y : (f^7) y=y := by simpa only [hx] using fixes_successor f 7 x h7x
  have h7z : (f^7) z=z := by simpa only [hy] using fixes_successor f 7 y h7y
  exact ⟨h7x,h7y,h7z⟩

end SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoSingerBlocks
