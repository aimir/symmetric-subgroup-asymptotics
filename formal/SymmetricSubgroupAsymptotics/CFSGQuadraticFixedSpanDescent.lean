import SymmetricSubgroupAsymptotics.CFSGQuadraticFixedCoefficients
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Tactic.Abel

/-! Literal scalar extension of subspaces of defining-fixed vectors
reflects membership and preserves intersections. The proof descends
actual vectors through the nonfixed quadratic coordinate; it does not
identify base- and extension-field spans by assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanDescent
open CFSGQuadraticFixedCoefficients
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (sigma : K ≃+* K) (theta : K) (htheta : sigma theta ≠ theta)

include htheta in
theorem fixed_pair_eq_zero (T : V →ₛₗ[sigma.toRingHom] V)
    (x y : V) (hx : T x = x) (hy : T y = y) (h : x + theta • y = 0) :
    x = 0 ∧ y = 0 := by
  have hh := congrArg T h
  simp only [map_add, map_smulₛₗ, hx, hy, map_zero] at hh
  have he : sigma theta • y = theta • y := add_left_cancel (hh.trans h.symm)
  have hz : (sigma theta - theta) • y = 0 := by rw [sub_smul, he, sub_self]
  have hy0 : y = 0 := (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr htheta)
  exact ⟨by simpa only [hy0, smul_zero, add_zero] using h, hy0⟩

variable (F : Subfield K)

theorem subfield_smul (c : F) (x : V) : (c.val : K) • x = c • x :=
  rfl

include htheta in
theorem exists_span_decomposition (hsigma : ∀ a, sigma (sigma a) = a)
    (hF : ∀ a, a ∈ F ↔ sigma a = a) (S : Submodule F V)
    (z : V) (hz : z ∈ Submodule.span K (S : Set V)) :
    ∃ x ∈ S, ∃ y ∈ S, z = x + theta • y := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact ⟨z, hz, 0, S.zero_mem, by simp only [smul_zero, add_zero]⟩
  | zero => exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp only [smul_zero, add_zero]⟩
  | add z w _ _ hz hw =>
    obtain ⟨x, hx, y, hy, he⟩ := hz
    obtain ⟨x', hx', y', hy', he'⟩ := hw
    refine ⟨x + x', S.add_mem hx hx', y + y', S.add_mem hy hy', ?_⟩
    rw [he, he', smul_add]
    abel
  | smul a z _ hz =>
    obtain ⟨x, hx, y, hy, he⟩ := hz
    obtain ⟨c, d, ha⟩ := exists_subfield_coefficients sigma hsigma theta htheta F hF a
    obtain ⟨e, f, hat⟩ := exists_subfield_coefficients sigma hsigma theta htheta F hF (a * theta)
    refine ⟨c • x + e • y, S.add_mem (S.smul_mem c hx) (S.smul_mem e hy),
      d • x + f • y, S.add_mem (S.smul_mem d hx) (S.smul_mem f hy), ?_⟩
    calc
      a • z = a • x + (a * theta) • y := by rw [he, smul_add, smul_smul]
      _ = (c.val + theta * d.val) • x + (e.val + theta * f.val) • y := by rw [hat, ha]
      _ = (c • x + e • y) + theta • (d • x + f • y) := by
        rw [add_smul, add_smul, mul_smul, mul_smul, smul_add]
        simp only [subfield_smul]
        abel

include theta htheta in
theorem fixed_mem_span_iff (hsigma : ∀ a, sigma (sigma a) = a)
    (hF : ∀ a, a ∈ F ↔ sigma a = a) (T : V →ₛₗ[sigma.toRingHom] V)
    (S : Submodule F V) (hS : ∀ x ∈ S, T x = x) (z : V) (hz : T z = z) :
    z ∈ Submodule.span K (S : Set V) ↔ z ∈ S := by
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, he⟩ := exists_span_decomposition sigma theta htheta F hsigma hF S z h
    have hh := congrArg T he
    simp only [hz, map_add, map_smulₛₗ, hS x hx, hS y hy] at hh
    have hs : sigma theta • y = theta • y := add_left_cancel (hh.symm.trans he)
    have hzero : (sigma theta - theta) • y = 0 := by rw [sub_smul, hs, sub_self]
    have hy0 : y = 0 := (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr htheta)
    simpa only [he, hy0, smul_zero, add_zero] using hx
  · intro h
    exact Submodule.subset_span h

include theta htheta in
theorem span_inf (hsigma : ∀ a, sigma (sigma a) = a)
    (hF : ∀ a, a ∈ F ↔ sigma a = a) (T : V →ₛₗ[sigma.toRingHom] V)
    (S P : Submodule F V) (hS : ∀ x ∈ S, T x = x) (hP : ∀ x ∈ P, T x = x) :
    Submodule.span K ((S ⊓ P : Submodule F V) : Set V) =
      Submodule.span K (S : Set V) ⊓ Submodule.span K (P : Set V) := by
  apply le_antisymm
  · apply le_inf
    · exact Submodule.span_mono (fun _ hx => hx.1)
    · exact Submodule.span_mono (fun _ hx => hx.2)
  · intro z hz
    obtain ⟨x, hx, y, hy, he⟩ := exists_span_decomposition sigma theta htheta F hsigma hF S z hz.1
    obtain ⟨u, hu, v, hv, he'⟩ := exists_span_decomposition sigma theta htheta F hsigma hF P z hz.2
    have hdiff : (x - u) + theta • (y - v) = 0 := by
      calc
        _ = (x + theta • y) - (u + theta • v) := by rw [smul_sub]; abel
        _ = 0 := sub_eq_zero.mpr (he.symm.trans he')
    have hdx : T (x - u) = x - u := by rw [map_sub, hS x hx, hP u hu]
    have hdy : T (y - v) = y - v := by rw [map_sub, hS y hy, hP v hv]
    obtain ⟨hxu, hyv⟩ := fixed_pair_eq_zero sigma theta htheta T (x - u) (y - v) hdx hdy hdiff
    have hxP : x ∈ P := (sub_eq_zero.mp hxu).symm ▸ hu
    have hyP : y ∈ P := (sub_eq_zero.mp hyv).symm ▸ hv
    rw [he]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨hx, hxP⟩)
      (Submodule.smul_mem _ theta (Submodule.subset_span ⟨hy, hyP⟩))

end SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanDescent
