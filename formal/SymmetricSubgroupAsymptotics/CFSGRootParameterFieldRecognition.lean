import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Three additive parameter bijections preserving the coefficient-one
A2 product incidence determine a single field automorphism after their
nonzero scalar factors are removed. This is an algebraic recognition
lemma; extraction of the incidence from a group automorphism is separate. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGRootParameterFieldRecognition
variable {K : Type*} [Field K]

private theorem one_image_ne_zero (f : K ≃+ K) : f 1 ≠ 0 := by
  intro h
  exact one_ne_zero (f.injective (h.trans f.map_zero.symm))

theorem scaled_multiplicative (f g h : K ≃+ K)
    (hproduct : ∀ x y : K, h (x * y) = f x * g y) (x y : K) :
    f (x * y) * f 1 = f x * f y := by
  have hb : g 1 ≠ 0 := one_image_ne_zero g
  have hc (z : K) : h z = f z * g 1 := by simpa only [mul_one] using hproduct z 1
  have hd (z : K) : h z = f 1 * g z := by simpa only [one_mul] using hproduct 1 z
  apply mul_right_cancel₀ hb
  calc
    (f (x * y) * f 1) * g 1 = f 1 * (f (x * y) * g 1) := by ring
    _ = f 1 * (f x * g y) := by rw [← hc, hproduct]
    _ = f x * (f 1 * g y) := by ring
    _ = f x * (f y * g 1) := by rw [← hd, hc]
    _ = (f x * f y) * g 1 := by ring

def normalizedHom (f g h : K ≃+ K)
    (hproduct : ∀ x y : K, h (x * y) = f x * g y) : K →+* K where
  toFun x := f x / f 1
  map_zero' := by rw [map_zero, zero_div]
  map_one' := div_self (one_image_ne_zero f)
  map_add' x y := by rw [map_add, add_div]
  map_mul' x y := by
    have ha : f 1 ≠ 0 := one_image_ne_zero f
    have hm := scaled_multiplicative f g h hproduct x y
    field_simp
    exact hm

def normalizedEquiv (f g h : K ≃+ K)
    (hproduct : ∀ x y : K, h (x * y) = f x * g y) : K ≃+* K :=
  RingEquiv.ofBijective (normalizedHom f g h hproduct) (by
    have ha : f 1 ≠ 0 := one_image_ne_zero f
    constructor
    · intro x y hxy
      apply f.injective
      change f x / f 1 = f y / f 1 at hxy
      have he := congrArg (fun z : K => z * f 1) hxy
      simpa only [div_mul_cancel₀ _ ha] using he
    · intro y
      refine ⟨f.symm (y * f 1), ?_⟩
      change f (f.symm (y * f 1)) / f 1 = y
      rw [f.apply_symm_apply, mul_div_cancel_right₀ y ha])

theorem common_field_automorphism (f g h : K ≃+ K)
    (hproduct : ∀ x y : K, h (x * y) = f x * g y) :
    ∃ σ : K ≃+* K, (∀ x : K,
      f x = f 1 * σ x ∧ g x = g 1 * σ x ∧ h x = h 1 * σ x) ∧
      h 1 = f 1 * g 1 := by
  let σ := normalizedEquiv f g h hproduct
  have ha : f 1 ≠ 0 := one_image_ne_zero f
  have hs (x : K) : σ x = f x / f 1 := rfl
  have hc (x : K) : h x = f x * g 1 := by simpa only [mul_one] using hproduct x 1
  have hd (x : K) : h x = f 1 * g x := by simpa only [one_mul] using hproduct 1 x
  have h1 : h 1 = f 1 * g 1 := by simpa only [mul_one] using hproduct 1 1
  refine ⟨σ, ?_, h1⟩
  intro x
  rw [hs]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · apply mul_left_cancel₀ ha
    calc
      f 1 * g x = h x := (hd x).symm
      _ = f x * g 1 := hc x
      _ = f 1 * (g 1 * (f x / f 1)) := by field_simp
  · rw [hc, h1]
    field_simp

end SymmetricSubgroupAsymptotics.CFSGRootParameterFieldRecognition
