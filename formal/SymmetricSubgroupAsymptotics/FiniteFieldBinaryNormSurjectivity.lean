import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The determinant norm a²+tab+b² is onto over a finite field when
t²≠4. Odd characteristic uses the existing two-quadratic-polynomial
intersection theorem; characteristic two uses surjectivity of squaring.
No quadratic-extension classification or norm-surjectivity premise is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteFieldBinaryNormSurjectivity
open Polynomial
variable {K : Type*} [Field K] [Finite K]

theorem exists_diagonal_norm (D δ : K) (hD : D≠0) (hchar : ringChar K≠2) :
    ∃ u v : K, u^2-D*v^2=4*δ := by
  letI : Fintype K := Fintype.ofFinite K
  let f : K[X] := X^2-C (4*δ)
  let g : K[X] := C (-D)*X^2
  have hf : f.degree=2 := degree_X_pow_sub_C (by decide : 0<(2:ℕ)) _
  have hg : g.degree=2 := by
    change (C (-D)*X^2 : K[X]).degree=2
    rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hD)), degree_X_pow]
    norm_num
  obtain ⟨u,v,h⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hchar)
  refine ⟨u,v,?_⟩
  have he : u^2-4*δ+(-D)*v^2=0 := by simpa only
    [f, g, eval_sub, eval_pow, eval_X, eval_C, eval_mul] using h
  linear_combination he

theorem exists_norm (t δ : K) (ht : t^2≠4) :
    ∃ a b : K, a^2+t*a*b+b^2=δ := by
  by_cases hchar : ringChar K=2
  · obtain ⟨a,ha⟩ := FiniteField.isSquare_of_char_two hchar δ
    refine ⟨a,0,?_⟩
    simpa only [mul_zero, add_zero, zero_pow (by decide : (2:ℕ)≠0), pow_two] using ha.symm
  · have hD : t^2-4≠0 := sub_ne_zero.mpr ht
    obtain ⟨u,v,he⟩ := exists_diagonal_norm (t^2-4) δ hD hchar
    have h2 : (2:K)≠0 := Ring.two_ne_zero hchar
    have h4 : (4:K)≠0 := by
      simpa only [show (4:K)=2*2 by ring] using mul_ne_zero h2 h2
    refine ⟨(u-t*v)/2,v,?_⟩
    apply mul_left_cancel₀ h4
    calc
      4*(((u-t*v)/2)^2+t*((u-t*v)/2)*v+v^2)=u^2-(t^2-4)*v^2 := by
        field_simp [h2]; ring
      _ =4*δ := he

end SymmetricSubgroupAsymptotics.FiniteFieldBinaryNormSurjectivity
