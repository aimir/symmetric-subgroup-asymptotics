import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Additive rigidity of a quadratic-extension norm plane. A norm
isometry fixing one is either identity or the coefficient involution.
There is no premise of linearity over the fixed field, no cardinality
enumeration, and no division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticNormAdditiveRigidity
variable {K : Type*} [Field K]

def norm (sigma : K ≃+* K) (x : K) : K := x * sigma x

theorem norm_mul (sigma : K ≃+* K) (x y : K) :
    norm sigma (x * y) = norm sigma x * norm sigma y := by
  simp only [norm, map_mul]
  ring

theorem trace_preserved (sigma : K ≃+* K) (h : K →+ K) (h1 : h 1 = 1)
    (hN : ∀ x, norm sigma (h x) = norm sigma x) (x : K) :
    h x + sigma (h x) = x + sigma x := by
  have hh := hN (x + 1)
  have hx := hN x
  simp only [norm, map_add, h1, map_one] at hh hx
  linear_combination hh - hx

theorem eq_self_or_sigma (sigma : K ≃+* K) (h : K →+ K) (h1 : h 1 = 1)
    (hN : ∀ x, norm sigma (h x) = norm sigma x) (x : K) : h x = x ∨ h x = sigma x := by
  have htr := trace_preserved sigma h h1 hN x
  have hn := hN x
  have hz : (h x - x) * (h x - sigma x) = 0 := by
    calc
      _ = h x * ((h x + sigma (h x)) - (x + sigma x)) -
          (norm sigma (h x) - norm sigma x) := by dsimp only [norm]; ring
      _ = 0 := by rw [htr, hn]; ring
  exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp

theorem eq_id_or_sigma (sigma : K ≃+* K) (h : K →+ K) (h1 : h 1 = 1)
    (hN : ∀ x, norm sigma (h x) = norm sigma x) :
    (∀ x, h x = x) ∨ (∀ x, h x = sigma x) := by
  by_cases hn : ∃ a, sigma a ≠ a
  · obtain ⟨a, ha⟩ := hn
    rcases eq_self_or_sigma sigma h h1 hN a with hea | hea
    · left
      intro x
      rcases eq_self_or_sigma sigma h h1 hN x with hex | hex
      · exact hex
      · rcases eq_self_or_sigma sigma h h1 hN (a + x) with hh | hh
        · rw [map_add, hea, hex] at hh
          exact hex.trans (add_left_cancel hh)
        · rw [map_add, hea, hex, map_add] at hh
          exact False.elim (ha (add_right_cancel hh).symm)
    · right
      intro x
      rcases eq_self_or_sigma sigma h h1 hN x with hex | hex
      · rcases eq_self_or_sigma sigma h h1 hN (a + x) with hh | hh
        · rw [map_add, hea, hex] at hh
          exact False.elim (ha (add_right_cancel hh))
        · rw [map_add, hea, hex, map_add] at hh
          exact hex.trans (add_left_cancel hh)
      · exact hex
  · left
    intro x
    rcases eq_self_or_sigma sigma h h1 hN x with hx | hx
    · exact hx
    · exact hx.trans (by by_contra hne; exact hn ⟨x, hne⟩)

theorem similitude_eq_mul_or_mul_sigma (sigma : K ≃+* K)
    (h : K →+ K) (c : K) (hc : c ≠ 0)
    (hN : ∀ x, norm sigma (h x) = c * norm sigma x) :
    (∀ x, h x = h 1 * x) ∨ (∀ x, h x = h 1 * sigma x) := by
  let u := h 1
  have huN : norm sigma u = c := by simpa only [norm, map_one, mul_one] using hN 1
  have hu : u ≠ 0 := by
    intro hz
    apply hc
    rw [← huN, hz]
    simp only [norm, zero_mul]
  let h' : K →+ K := {
    toFun := fun x => u⁻¹ * h x
    map_zero' := by rw [map_zero, mul_zero]
    map_add' := fun x y => by rw [map_add, mul_add] }
  have h'1 : h' 1 = 1 := inv_mul_cancel₀ hu
  have h'N (x : K) : norm sigma (h' x) = norm sigma x := by
    change norm sigma (u⁻¹ * h x) = _
    rw [norm_mul, hN, ← huN]
    have he : norm sigma u⁻¹ * norm sigma u = 1 := by
      rw [← norm_mul, inv_mul_cancel₀ hu]
      simp only [norm, map_one, mul_one]
    rw [← mul_assoc, he, one_mul]
  rcases eq_id_or_sigma sigma h' h'1 h'N with hh | hh
  · left
    intro x
    have he := congrArg (fun z : K => u * z) (hh x)
    change u * (u⁻¹ * h x) = u * x at he
    simpa only [← mul_assoc, mul_inv_cancel₀ hu, one_mul] using he
  · right
    intro x
    have he := congrArg (fun z : K => u * z) (hh x)
    change u * (u⁻¹ * h x) = u * sigma x at he
    simpa only [← mul_assoc, mul_inv_cancel₀ hu, one_mul] using he

theorem norm_map (sigma tau : K ≃+* K) (hcomm : Function.Commute sigma tau) (x : K) :
    norm sigma (tau x) = tau (norm sigma x) := by
  simp only [norm, hcomm x, map_mul]

theorem semilinearSimilitude_eq_mul_or_mul_sigma (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (h : K →+ K) (c : K) (hc : c ≠ 0)
    (hN : ∀ x, norm sigma (h x) = c * tau (norm sigma x)) :
    (∀ x, h x = h 1 * tau x) ∨ (∀ x, h x = h 1 * tau (sigma x)) := by
  have hcomm' : Function.Commute sigma tau.symm := by
    intro x
    apply tau.injective
    simpa only [tau.apply_symm_apply] using (hcomm (tau.symm x)).symm
  let h' : K →+ K := tau.symm.toAddMonoidHom.comp h
  have hc' : tau.symm c ≠ 0 := by
    intro he
    apply hc
    exact tau.symm.injective (he.trans (map_zero tau.symm).symm)
  have hn' (x : K) : norm sigma (h' x) = tau.symm c * norm sigma x := by
    change norm sigma (tau.symm (h x)) = _
    rw [norm_map sigma tau.symm hcomm', hN, map_mul, tau.symm_apply_apply]
  rcases similitude_eq_mul_or_mul_sigma sigma h' (tau.symm c) hc' hn' with hh | hh
  · left
    intro x
    have he := congrArg tau (hh x)
    change tau (tau.symm (h x)) = tau (tau.symm (h 1) * x) at he
    simpa only [map_mul, tau.apply_symm_apply] using he
  · right
    intro x
    have he := congrArg tau (hh x)
    change tau (tau.symm (h x)) = tau (tau.symm (h 1) * sigma x) at he
    simpa only [map_mul, tau.apply_symm_apply] using he

end SymmetricSubgroupAsymptotics.CFSGQuadraticNormAdditiveRigidity
