import SymmetricSubgroupAsymptotics.FusionHotBenchmark

/-!
# Quadratically small numerical hot kernels

The only asymptotic input is explicitly the coarse exponent `1/16 + o(1)`
for the supplied count sequence. For the actual subgroup sequence that input
is the published coarse theorem, not a proved result of this formal project.
This module proves the numerical kernel estimate; a physical orbit-pointing
encoding is still required before applying it to a subgroup family.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact independently published coarse counting input, exposed as a
proposition on the count sequence rather than an axiom. -/
def FusionCoarseEstimate (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, s n ≤ (2:ℝ)^((1/16+ε)*(n:ℝ)^2)

theorem eventually_linear_add_le_quadratic {a C K : ℝ}
    (ha : 0<a) (_hC : 0≤C) (hK : 0≤K) :
    ∀ᶠ b : ℕ in atTop, C*(b:ℝ)+K ≤ a*(b:ℝ)^2 := by
  filter_upwards [eventually_ge_atTop (max 1 ⌈(C+K)/a⌉₊)] with b hb
  have hb1 : 1≤(b:ℝ) := by exact_mod_cast (le_max_left 1 ⌈(C+K)/a⌉₊).trans hb
  have hbC : (C+K)/a ≤ (b:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈(C+K)/a⌉₊).trans hb)
  have hbC' : C+K ≤ (b:ℝ)*a := (div_le_iff₀ ha).mp hbC
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hb1),
    mul_nonneg (sub_nonneg.mpr hbC') (show 0≤(b:ℝ) by positivity)]

/-- Rounding makes the graph degree at most a fixed multiple of b. -/
theorem fusion_graph_degree_le (b v : ℕ) {e : ℝ} (he : 0≤e) (hb : 1≤b) :
    ((b+fusionMoment e v b*v:ℕ):ℝ) ≤
      (1+8*e/(v:ℝ)^2*(v:ℝ)+(v:ℝ))*(b:ℝ) := by
  have hdist := (fusionMoment_distance (v := v) he (show 0≤(b:ℝ) by positivity)).2
  have hbR : 1≤(b:ℝ) := by exact_mod_cast hb
  push_cast
  simp only [div_eq_mul_inv] at hdist ⊢
  nlinarith [mul_nonneg (show 0≤(v:ℝ) by positivity) (sub_nonneg.mpr hbR),
    mul_le_mul_of_nonneg_right hdist (show 0≤(v:ℝ) by positivity)]

/-- The original factorial pointing, original action divisor, and complete
coarse-count moment are kept as separate factors. -/
def fusionHotKernel (s : ℕ → ℝ) (b h v : ℕ) (D a e : ℝ) : ℝ :=
  ((((b+2*h).factorial:ℝ)/(b.factorial:ℝ))/exactBenchmark (b+2*h)) * (D/a) *
    (2:ℝ)^((((2*h:ℕ):ℝ)-(v:ℝ)-16*e)/8*(b:ℝ)-
      ((fusionMoment e v b:ℝ)-1)*((v:ℝ)/8+e)*(b:ℝ)) *
    s (b+fusionMoment e v b*v)

/-- A fixed positive-width entry has a quadratically decaying numerical hot
kernel. The coarse input is explicit; no bounded normalized count is assumed. -/
theorem fusionHotKernel_eventually (s : ℕ → ℝ) (hs : FusionCoarseEstimate s)
    (h v : ℕ) (hv : 0<v) {D a e : ℝ}
    (hD : 0≤D) (ha : 0<a) (he : 0<e) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ b : ℕ in atTop,
      fusionHotKernel s b h v D a e ≤ C*(2:ℝ)^(-κ*(b:ℝ)^2) := by
  let A : ℝ := 4*e^2/(v:ℝ)^2
  let L : ℝ := 1+8*e/(v:ℝ)^2*(v:ℝ)+(v:ℝ)
  let ε : ℝ := A/(4*L^2)
  let K : ℝ := (v:ℝ)^2/16+5*((2*h:ℕ):ℝ)/8+1/4
  have hvR : 0<(v:ℝ) := by exact_mod_cast hv
  have hA : 0<A := by dsimp [A]; positivity
  have hL : 0<L := by dsimp [L]; positivity
  have hε : 0<ε := by dsimp [ε]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  have hεL : ε*L^2=A/4 := by dsimp [ε]; field_simp
  have hφ := euler_positive
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs ε hε)
  refine ⟨eulerProduct⁻¹*(D/a)+1,A/2,by positivity,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max N (max 1 (2*h))),
    eventually_linear_add_le_quadratic (show 0<A/4 by positivity)
      (show (0:ℝ)≤5/8 by norm_num) hK] with b hb hsmall
  have hbN : N≤b := (le_max_left _ _).trans hb
  have hb1 : 1≤b := (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  have hbwidth : 2*h≤b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  have hbR : 0≤(b:ℝ) := by positivity
  have hxN : N≤b+fusionMoment e v b*v := hbN.trans (Nat.le_add_right _ _)
  have hx := hN _ hxN
  have hdegree := fusion_graph_degree_le b v he.le hb1
  have hdegree2 : (((b+fusionMoment e v b*v:ℕ):ℝ))^2 ≤ L^2*(b:ℝ)^2 := by
    dsimp [L] at *
    nlinarith [sq_nonneg ((1+8*e/(v:ℝ)^2*(v:ℝ)+(v:ℝ))*(b:ℝ)-
      ((b+fusionMoment e v b*v:ℕ):ℝ))]
  have herror : ε*(((b+fusionMoment e v b*v:ℕ):ℝ))^2 ≤ A/4*(b:ℝ)^2 := by
    calc
      _ ≤ ε*(L^2*(b:ℝ)^2) := mul_le_mul_of_nonneg_left hdegree2 hε.le
      _ = _ := by rw [←mul_assoc,hεL]
  have hsquare := fusion_hot_exponent_le (w := ((2*h:ℕ):ℝ)) he.le hbR hvR.ne'
  have hexp : (-((b+2*h:ℕ):ℝ)^2/16+5*((b+2*h:ℕ):ℝ)/8+1/4) +
      ((((2*h:ℕ):ℝ)-(v:ℝ)-16*e)/8*(b:ℝ)-
        ((fusionMoment e v b:ℝ)-1)*((v:ℝ)/8+e)*(b:ℝ)) +
      (1/16+ε)*(((b+fusionMoment e v b*v:ℕ):ℝ))^2 ≤ -(A/2)*(b:ℝ)^2 := by
    push_cast at hsquare herror ⊢
    dsimp [A,K] at hsmall ⊢
    dsimp [A] at herror
    push_cast at hsmall
    simp only [div_eq_mul_inv] at hsquare herror hsmall ⊢
    nlinarith [mul_nonneg he.le hbR,sq_nonneg ((2*h:ℕ):ℝ)]
  unfold fusionHotKernel
  calc
    _ ≤ (eulerProduct⁻¹ * (2:ℝ)^(-((b+2*h:ℕ):ℝ)^2/16+
        5*((b+2*h:ℕ):ℝ)/8+1/4)) * (D/a) *
        (2:ℝ)^((((2*h:ℕ):ℝ)-(v:ℝ)-16*e)/8*(b:ℝ)-
          ((fusionMoment e v b:ℝ)-1)*((v:ℝ)/8+e)*(b:ℝ)) *
        (2:ℝ)^((1/16+ε)*(((b+fusionMoment e v b*v:ℕ):ℝ))^2) := by
      apply le_trans (mul_le_mul_of_nonneg_left hx ?_) ?_
      · have hp := exactBenchmark_pos (b+2*h)
        positivity
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (fusionHot_pointing_denominator_le b h hbwidth)
          (div_nonneg hD ha.le)
    _ = (eulerProduct⁻¹*(D/a)) *
        (2:ℝ)^((-((b+2*h:ℕ):ℝ)^2/16+5*((b+2*h:ℕ):ℝ)/8+1/4) +
          ((((2*h:ℕ):ℝ)-(v:ℝ)-16*e)/8*(b:ℝ)-
            ((fusionMoment e v b:ℝ)-1)*((v:ℝ)/8+e)*(b:ℝ)) +
          (1/16+ε)*(((b+fusionMoment e v b*v:ℕ):ℝ))^2) := by
      have hm (x y z C E : ℝ) :
          (C*(2:ℝ)^x)*E*(2:ℝ)^y*(2:ℝ)^z = (C*E)*(2:ℝ)^(x+y+z) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ)<2),
          Real.rpow_add (by norm_num : (0:ℝ)<2)]
        ring
      exact hm _ _ _ _ _
    _ ≤ (eulerProduct⁻¹*(D/a))*(2:ℝ)^(-(A/2)*(b:ℝ)^2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end SymmetricSubgroupAsymptotics
