import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A rotation and ONE unit shear in an actual action on F3^2 give
transitivity on the nonzero quotient vectors. The proof uses powers of
that same shear and field row reduction. No action table, group-order,
SL2 recognition, or splitting assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TernaryPlaneRotationShearTransitivity
abbrev V := ZMod 3 × ZMod 3
variable {G : Type*} [Group G] [MulAction G V]

private theorem nonzero_scalar (a : ZMod 3) (ha : a≠0) : a=1 ∨ a= -1 := by
  exact (by decide +kernel : ∀ a : ZMod 3, a≠0 → a=1 ∨ a= -1) a ha

theorem shear_pow (d : G) (hD : ∀ v : V, d • v=(v.1,v.2+v.1))
    (n : ℕ) (v : V) : d^n • v=(v.1,v.2+(n : ZMod 3)*v.1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_smul,ih,hD]
    apply Prod.ext
    · rfl
    · change (v.2+(n : ZMod 3)*v.1)+v.1=v.2+((n+1 : ℕ) : ZMod 3)*v.1
      rw [Nat.cast_add,Nat.cast_one]
      ring

theorem shear_parameter (d : G) (hD : ∀ v : V, d • v=(v.1,v.2+v.1))
    (t : ZMod 3) (v : V) : d^t.val • v=(v.1,v.2+t*v.1) := by
  simpa only [ZMod.natCast_zmod_val] using shear_pow d hD t.val v

private theorem first_nonzero_to_unit (f d : G)
    (hF : ∀ v : V, f • v=(-v.2,v.1))
    (hD : ∀ v : V, d • v=(v.1,v.2+v.1))
    (v : V) (ha : v.1≠0) : ∃ g : G, g • v=(1,0) := by
  let t : ZMod 3 := -v.2/v.1
  have hs : v.2+t*v.1=0 := by
    dsimp only [t]
    rw [div_mul_cancel₀ _ ha,add_neg_cancel]
  have he : d^t.val • v=(v.1,0) := by rw [shear_parameter d hD,hs]
  rcases nonzero_scalar v.1 ha with h1 | hm
  · exact ⟨d^t.val,by simpa only [h1] using he⟩
  · refine ⟨f^2*d^t.val,?_⟩
    rw [mul_smul,he,pow_two,mul_smul,hF,hF]
    simpa only [hm,neg_zero,neg_neg]

theorem exists_to_unit (f d : G)
    (hF : ∀ v : V, f • v=(-v.2,v.1))
    (hD : ∀ v : V, d • v=(v.1,v.2+v.1))
    (v : V) (hv : v≠0) : ∃ g : G, g • v=(1,0) := by
  by_cases ha : v.1≠0
  · exact first_nonzero_to_unit f d hF hD v ha
  · have ha0 : v.1=0 := not_ne_iff.mp ha
    have hb : v.2≠0 := by
      intro hb
      exact hv (Prod.ext ha0 hb)
    have hfirst : (f • v).1≠0 := by rw [hF]; exact neg_ne_zero.mpr hb
    obtain ⟨g,hg⟩ := first_nonzero_to_unit f d hF hD (f • v) hfirst
    exact ⟨g*f,by rw [mul_smul]; exact hg⟩

theorem transitive_nonzero (f d : G)
    (hF : ∀ v : V, f • v=(-v.2,v.1))
    (hD : ∀ v : V, d • v=(v.1,v.2+v.1))
    (v w : V) (hv : v≠0) (hw : w≠0) : ∃ g : G, g • v=w := by
  obtain ⟨g,hg⟩ := exists_to_unit f d hF hD v hv
  obtain ⟨h,hh⟩ := exists_to_unit f d hF hD w hw
  refine ⟨h⁻¹*g,?_⟩
  rw [mul_smul,hg,←hh,inv_smul_smul]

end SymmetricSubgroupAsymptotics.TernaryPlaneRotationShearTransitivity
