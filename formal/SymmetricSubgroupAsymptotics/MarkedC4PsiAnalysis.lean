import SymmetricSubgroupAsymptotics.MarkedC4HallCount

/-!
# The real analysis of the Hall splice

* `Ψ(v,x)` is attained at `y* = v` (if `v ≤ x`) or `(v+x)/2`;
* superadditivity: `Ψ(v,x) + Ψ(w,x') ≤ Ψ(v+w,x)` for `x' ≤ x`;
* column exchange: moving mass `δ` from a column `(u+δ, x')` to a column
  `(V, x)` with `u+δ ≤ V`, `x' ≤ x` does not decrease `∑ Ψ`;
* `g_B(x) = max_{0≤z≤B} (z(B-z)/4 + xz)` and the exact optimization
  `x(v-x) + g_B(x)/4 ≤ (v+B/4)²/4` for `0 ≤ x ≤ v`;
* the final quadratic `B²/32 + ((v₁+B/4)² + (v₂+B/4)²)/4 ≤ F(a+B, r)` for
  `v₁ ≤ a/2 + r`, `v₂ = r`, where `F(n,r) = n²/16 + nr/4 + r²/2`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-! ## The maximizer and superadditivity -/

/-- The maximizing rank of `Ψ`. -/
def ystar (v x : ℝ) : ℝ := if v ≤ x then v else (v + x) / 2

theorem ystar_nonneg {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) : 0 ≤ ystar v x := by
  unfold ystar
  split_ifs <;> linarith

theorem ystar_le {v x : ℝ} : ystar v x ≤ v := by
  unfold ystar
  split_ifs with h
  · exact le_rfl
  · linarith [not_le.mp h]

theorem psi_eq (v x : ℝ) : psi v x = ystar v x * (v - ystar v x + x) := by
  unfold psi ystar
  split_ifs with h
  · ring
  · ring

theorem psi_superadd {v w x x' : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) (hx' : 0 ≤ x')
    (hxx : x' ≤ x) : psi v x + psi w x' ≤ psi (v + w) x := by
  have hx : 0 ≤ x := le_trans hx' hxx
  set y₁ := ystar v x
  set y₂ := ystar w x'
  have h1 : 0 ≤ y₁ := ystar_nonneg hv hx
  have h2 : 0 ≤ y₂ := ystar_nonneg hw hx'
  have h1v : y₁ ≤ v := ystar_le
  have h2w : y₂ ≤ w := ystar_le
  have hmax := le_psi (v := v + w) (x := x) (y := y₁ + y₂) hx (by linarith) (by linarith)
  rw [psi_eq v x, psi_eq w x']
  nlinarith [mul_nonneg h1 (sub_nonneg.mpr h2w), mul_nonneg h2 (sub_nonneg.mpr h1v),
    mul_nonneg h2 (sub_nonneg.mpr hxx)]

/-! ## Column exchange -/

/-- The slope `max(x, (v+x)/2)`. -/
def psiSlope (v x : ℝ) : ℝ := max x ((v + x) / 2)

theorem psiSlope_mono {v v' x x' : ℝ} (hv : v ≤ v') (hx : x ≤ x') :
    psiSlope v x ≤ psiSlope v' x' := by
  unfold psiSlope
  exact max_le_max hx (by linarith)

theorem psi_add_ge {v δ x : ℝ} (hv : 0 ≤ v) (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    psi v x + δ * psiSlope v x ≤ psi (v + δ) x := by
  unfold psi psiSlope
  by_cases h1 : v + δ ≤ x
  · have h0 : v ≤ x := by linarith
    rw [if_pos h0, if_pos h1, max_eq_left (by linarith)]
    ring_nf
    exact le_rfl
  · by_cases h0 : v ≤ x
    · rw [if_pos h0, if_neg h1, max_eq_left (by linarith)]
      nlinarith [sq_nonneg (v + δ - x)]
    · rw [if_neg h0, if_neg h1, max_eq_right (by linarith)]
      nlinarith [sq_nonneg δ]

theorem psi_add_le {u δ x : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    psi (u + δ) x ≤ psi u x + δ * psiSlope (u + δ) x := by
  unfold psi psiSlope
  by_cases h1 : u + δ ≤ x
  · have h0 : u ≤ x := by linarith
    rw [if_pos h0, if_pos h1, max_eq_left (by linarith)]
    ring_nf
    exact le_rfl
  · by_cases h0 : u ≤ x
    · rw [if_pos h0, if_neg h1, max_eq_right (by linarith)]
      have hd : x - u ≤ δ := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (by linarith : (0 : ℝ) ≤ δ + (x - u))]
    · rw [if_neg h0, if_neg h1, max_eq_right (by linarith)]
      nlinarith [sq_nonneg δ]

/-- **Column exchange.** -/
theorem psi_exchange {V u δ x x' : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hx' : 0 ≤ x')
    (hxx : x' ≤ x) (huV : u + δ ≤ V) :
    psi V x + psi (u + δ) x' ≤ psi (V + δ) x + psi u x' := by
  have hV : 0 ≤ V := by linarith
  have hx : 0 ≤ x := le_trans hx' hxx
  have h1 := psi_add_ge hV hδ hx
  have h2 := psi_add_le hu hδ hx'
  have h3 : psiSlope (u + δ) x' ≤ psiSlope V x := psiSlope_mono huV hxx
  nlinarith [mul_le_mul_of_nonneg_left h3 hδ]

theorem psi_mono_left {v v' x : ℝ} (hv : 0 ≤ v) (hvv : v ≤ v') (hx : 0 ≤ x) :
    psi v x ≤ psi v' x := by
  have := psi_add_ge hv (sub_nonneg.mpr hvv) hx
  have hs : 0 ≤ (v' - v) * psiSlope v x := by
    apply mul_nonneg (sub_nonneg.mpr hvv)
    unfold psiSlope
    exact le_max_of_le_left hx
  rw [add_sub_cancel] at this
  linarith

/-! ## The function `g_B` and the one-variable optimization -/

/-- `g_B(x) = max_{0 ≤ z ≤ B} (z(B-z)/4 + xz)`. -/
def gB (B x : ℝ) : ℝ := if x ≤ B / 4 then B ^ 2 / 16 + B * x / 2 + x ^ 2 else B * x

theorem le_gB {B x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (hzB : z ≤ B) :
    z * (B - z) / 4 + x * z ≤ gB B x := by
  unfold gB
  split_ifs with h
  · nlinarith [sq_nonneg (z / 2 - (B / 4 + x))]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hzB) (by linarith : (0 : ℝ) ≤ x - z / 4)]

theorem gB_zero (B : ℝ) (hB : 0 ≤ B) : gB B 0 = B ^ 2 / 16 := by
  unfold gB
  rw [if_pos (by linarith)]
  ring

theorem gB_nonneg {B x : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) : 0 ≤ gB B x := by
  have := le_gB (B := B) (x := x) (z := 0) hx le_rfl hB
  simpa using this

/-- **The exact one-variable optimization.** -/
theorem rank_gB_le {B v x : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (hxv : x ≤ v) :
    x * (v - x) + gB B x / 4 ≤ (v + B / 4) ^ 2 / 4 := by
  unfold gB
  split_ifs with h
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxv) (by linarith : (0 : ℝ) ≤ v - 3 * x + B / 2)]
  · nlinarith [sq_nonneg ((v + B / 4) / 2 - x)]

/-! ## The final quadratic -/

/-- The marked moment exponent `F(n, r) = n²/16 + nr/4 + r²/2`. -/
def markedF (n r : ℝ) : ℝ := n ^ 2 / 16 + n * r / 4 + r ^ 2 / 2

theorem splice_quadratic_le {a B r v₁ : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hv₁ : 0 ≤ v₁) (hv₁le : v₁ ≤ a / 2 + r) :
    B ^ 2 / 32 + ((v₁ + B / 4) ^ 2 + (r + B / 4) ^ 2) / 4 ≤ markedF (a + B) r := by
  unfold markedF
  have h : (v₁ + B / 4) ^ 2 ≤ (a / 2 + r + B / 4) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith)
    linarith
  nlinarith [mul_nonneg ha hB]

theorem markedF_mono_left {n n' r : ℝ} (hn : 0 ≤ n) (hnn : n ≤ n') (hr : 0 ≤ r) :
    markedF n r ≤ markedF n' r := by
  unfold markedF
  nlinarith

/-- The peeling reserve: `F(b,r) - F(b-w,r) = w(b-w)/8 + wr/4 + w²/16`. -/
theorem markedF_reserve (b w r : ℝ) :
    markedF b r - markedF (b - w) r = w * (b - w) / 8 + w * r / 4 + w ^ 2 / 16 := by
  unfold markedF
  ring

/-- The nilpotent split: `F(m,r) + d²/16 ≤ F(b,r)` when `m + d ≤ b`. -/
theorem markedF_split {m d b r : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hmd : m + d ≤ b) : markedF m r + d ^ 2 / 16 ≤ markedF b r := by
  unfold markedF
  nlinarith [mul_nonneg hm hd, mul_nonneg hd hr]

end MarkedC4
end SymmetricSubgroupAsymptotics
