import SymmetricSubgroupAsymptotics.FusionDirectUniform

/-! Numerical aggregation of varying-width first-moment coefficients.
The menu hypothesis is an explicit bound on the sum of the original
weights `D/a`, rather than a bound on the number of labels. The theorem
does not supply that hypothesis or an actual subgroup-family cover. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private theorem fusionDirect_polynomial_base_eventually :
    ∀ᶠ n : ℕ in atTop,
      ((n+1 : ℕ) : ℝ)^3*(2 : ℝ)^(1/2 : ℝ) ≤ (2 : ℝ)^((n : ℝ)/256) := by
  filter_upwards [eventually_shifted_natpow_mul_exponential_le 1 3
    (show (0 : ℝ)<1/256 by norm_num), eventually_ge_atTop 2048] with n hn hlarge
  have hnr : (2048 : ℝ)≤n := by exact_mod_cast hlarge
  have hbound : (((n+1 : ℕ) : ℝ)^3*(2 : ℝ)^(1/2 : ℝ))*
      (2 : ℝ)^(-(n : ℝ)/256) ≤ (2 : ℝ)^(7/2-(n : ℝ)/512) := by
    calc
      _ = (2 : ℝ)^(1/2 : ℝ)*
          (((n+1 : ℕ) : ℝ)^3*(2 : ℝ)^(-(1/256 : ℝ)*(n : ℝ))) := by
        have he : -(n : ℝ)/256 = -(1/256 : ℝ)*(n : ℝ) := by ring
        rw [he]
        ring
      _ ≤ (2 : ℝ)^(1/2 : ℝ)*
          (((1+1 : ℕ) : ℝ)^3*(2 : ℝ)^(-((1/256 : ℝ)/2)*(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by
        norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
        have h8 : (8 : ℝ) = (2 : ℝ)^(3 : ℝ) := by norm_num
        rw [← mul_assoc, h8,
          ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
          ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
        congr 1
        ring
  have hone : (2 : ℝ)^(7/2-(n : ℝ)/512)≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ)≤2) (show 7/2-(n : ℝ)/512≤0 by linarith)
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos
    (by norm_num : (0 : ℝ)<2) (-(n : ℝ)/256))).mp
  calc
    (2 : ℝ)^(-(n : ℝ)/256)*
        (((n+1 : ℕ) : ℝ)^3*(2 : ℝ)^(1/2 : ℝ)) =
      (((n+1 : ℕ) : ℝ)^3*(2 : ℝ)^(1/2 : ℝ))*
        (2 : ℝ)^(-(n : ℝ)/256) := mul_comm _ _
    _ ≤ 1 := hbound.trans hone
    _ = (2 : ℝ)^(-(n : ℝ)/256)*(2 : ℝ)^((n : ℝ)/256) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      rw [show -(n : ℝ)/256+(n : ℝ)/256=0 by ring, Real.rpow_zero]

/-- One complete finite menu at a given width. The weighted hypothesis is
`Σ D/a ≤ 2^(w²/128+H)` with `w=2*h`. No cardinality bound on the menu and
no count of actual subgroups are substituted for this original-weight sum. -/
theorem fusionDirect_width_sum_le {ι : Type*} [Fintype ι]
    (b h : ℕ) (hh : 1≤h) (r : ι → ℕ) (D a e : ι → ℝ) (H : ℝ)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i)
    (hprefix : ∀ i, 16*r i≤13*h)
    (hgap : ∀ i, ((2*h : ℕ) : ℝ)/32≤16*e i)
    (hmass : (∑ i, D i/a i)≤(2 : ℝ)^((h : ℝ)^2/32+H))
    (hpoly : ((b+2*h+1 : ℕ) : ℝ)^3*(2 : ℝ)^(1/2 : ℝ) ≤
      (2 : ℝ)^(((b+2*h : ℕ) : ℝ)/256)) :
    (∑ i, fusionDirectKernel b h (2*r i) (D i) (a i) (e i)) ≤
      (eulerProduct⁻¹^2*(2 : ℝ)^H)*
        (2 : ℝ)^(-(h : ℝ)*((b+2*h : ℕ) : ℝ)/256) := by
  let X : ℝ := ((b+2*h+1 : ℕ) : ℝ)
  let E : ℝ := -(h : ℝ)*(b : ℝ)/128-87*(h : ℝ)^2/1024+(h : ℝ)/2
  have hX : 1≤X := by dsimp [X]; exact_mod_cast (show 1≤b+2*h+1 by omega)
  have hX0 : 0≤X := zero_le_one.trans hX
  have hhr : (1 : ℝ)≤h := by exact_mod_cast hh
  have hentry (i : ι) : fusionDirectKernel b h (2*r i) (D i) (a i) (e i) ≤
      (D i/a i)*(eulerProduct⁻¹^2*X^(3*h)*(2 : ℝ)^E) := by
    have hDi := hD i
    have hai := ha i
    have hr : r i≤h := by have := hprefix i; omega
    have hp : h+r i+1≤3*h := by omega
    have he : -((2*h : ℕ) : ℝ)*(b : ℝ)/256-
        87*((2*h : ℕ) : ℝ)^2/4096+((2*h : ℕ) : ℝ)/8+1/4≤E := by
      dsimp [E]
      push_cast
      linarith
    calc
      _ ≤ (eulerProduct⁻¹^2*(D i/a i))*X^(h+r i+1)*
          (2 : ℝ)^(-((2*h : ℕ) : ℝ)*(b : ℝ)/256-
            87*((2*h : ℕ) : ℝ)^2/4096+((2*h : ℕ) : ℝ)/8+1/4) :=
        fusionDirectKernel_le_wide b h (r i) (hprefix i) (hD i) (ha i) (hgap i)
      _ ≤ (eulerProduct⁻¹^2*(D i/a i))*X^(3*h)*(2 : ℝ)^E := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hp) (by positivity)
        · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he
        · positivity
        · positivity
      _ = _ := by ring
  have hmassBound : (∑ i, fusionDirectKernel b h (2*r i) (D i) (a i) (e i)) ≤
      (2 : ℝ)^((h : ℝ)^2/32+H)*(eulerProduct⁻¹^2*X^(3*h)*(2 : ℝ)^E) := by
    calc
      _ ≤ ∑ i, (D i/a i)*(eulerProduct⁻¹^2*X^(3*h)*(2 : ℝ)^E) :=
        Finset.sum_le_sum (fun i _ => hentry i)
      _ = (∑ i, D i/a i)*(eulerProduct⁻¹^2*X^(3*h)*(2 : ℝ)^E) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (by positivity)
  calc
    _ ≤ (2 : ℝ)^((h : ℝ)^2/32+H)*(eulerProduct⁻¹^2*X^(3*h)*(2 : ℝ)^E) :=
      hmassBound
    _ = (eulerProduct⁻¹^2*(2 : ℝ)^H)*(X^3*(2 : ℝ)^(1/2 : ℝ))^h*
        (2 : ℝ)^(-(h : ℝ)*(b : ℝ)/128-55*(h : ℝ)^2/1024) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2)]
      dsimp [E]
      rw [Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      have hexp : (h : ℝ)^2/32 +
          (-(h : ℝ)*(b : ℝ)/128-87*(h : ℝ)^2/1024+(h : ℝ)/2) =
          (1/2 : ℝ)*(h : ℝ)+(-(h : ℝ)*(b : ℝ)/128-55*(h : ℝ)^2/1024) := by ring
      have hp := congrArg (fun t : ℝ => (2 : ℝ)^t) hexp
      dsimp only at hp
      simp only [Real.rpow_add (by norm_num : (0 : ℝ)<2)] at hp ⊢
      linear_combination (eulerProduct⁻¹^2*(2 : ℝ)^H*X^(3*h))*hp
    _ ≤ (eulerProduct⁻¹^2*(2 : ℝ)^H)*(X^3*(2 : ℝ)^(1/2 : ℝ))^h*
        (2 : ℝ)^(-(h : ℝ)*((b+2*h : ℕ) : ℝ)/128) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith [sq_nonneg (h : ℝ)]
    _ ≤ (eulerProduct⁻¹^2*(2 : ℝ)^H)*
        ((2 : ℝ)^(((b+2*h : ℕ) : ℝ)/256))^h*
          (2 : ℝ)^(-(h : ℝ)*((b+2*h : ℕ) : ℝ)/128) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpoly h)
        (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2), mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      congr 2
      ring

/-- The actual numerical entry sum, with each half-width and each of its
original weighted labels retained. Widths below64 are deliberately absent. -/
def fusionWideDirectSum {ι : ℕ → Type*} [∀ h, Fintype (ι h)]
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ) (n : ℕ) : ℝ :=
  ∑ h ∈ Finset.range (n+1), if 32≤h ∧ 2*h≤n then
    ∑ i, fusionDirectKernel (n-2*h) h (2*r h i) (D h i) (a h i) (e h i) else 0

/-- A uniform original weighted menu-mass bound suffices for exponential
aggregate decay. It is explicit input; neither a catalogue cover nor the
group-theoretic weighted menu bound is asserted by this numerical theorem. -/
theorem fusionWideDirectSum_eventually {ι : ℕ → Type*} [∀ h, Fintype (ι h)]
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ) (H : ℝ)
    (hD : ∀ h i, 0≤D h i) (ha : ∀ h i, 0<a h i)
    (hprefix : ∀ h i, 16*r h i≤13*h)
    (hgap : ∀ h i, ((2*h : ℕ) : ℝ)/32≤16*e h i)
    (hmass : ∀ h, 32≤h → (∑ i, D h i/a h i)≤(2 : ℝ)^((h : ℝ)^2/32+H)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      fusionWideDirectSum r D a e n ≤ C*(2 : ℝ)^(-(n : ℝ)/16) := by
  let A : ℝ := eulerProduct⁻¹^2*(2 : ℝ)^H
  have hφ := euler_positive
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨2*A, by positivity, ?_⟩
  filter_upwards [fusionDirect_polynomial_base_eventually,
    eventually_shifted_natpow_mul_exponential_le 1 1
      (show (0 : ℝ)<1/8 by norm_num)] with n hpoly hdecay
  have hentry (h : ℕ) :
      (if 32≤h ∧ 2*h≤n then
        ∑ i, fusionDirectKernel (n-2*h) h (2*r h i) (D h i) (a h i) (e h i)
      else 0) ≤ A*(2 : ℝ)^(-(n : ℝ)/8) := by
    split_ifs with hh
    · have hn : n-2*h+2*h = n := Nat.sub_add_cancel hh.2
      have hb := fusionDirect_width_sum_le (n-2*h) h (by omega)
        (r h) (D h) (a h) (e h) H (hD h) (ha h) (hprefix h) (hgap h)
        (hmass h hh.1) (by simpa only [hn] using hpoly)
      rw [hn] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hhr : (32 : ℝ)≤h := by exact_mod_cast hh.1
      nlinarith [mul_nonneg (sub_nonneg.mpr hhr) (Nat.cast_nonneg (α := ℝ) n)]
    · positivity
  have hsum : fusionWideDirectSum r D a e n ≤
      A*(((n+1 : ℕ) : ℝ)*(2 : ℝ)^(-(n : ℝ)/8)) := by
    unfold fusionWideDirectSum
    apply (Finset.sum_le_sum (fun h _ => hentry h)).trans_eq
    simp
    ring
  apply hsum.trans
  have hd : ((n+1 : ℕ) : ℝ)*(2 : ℝ)^(-(n : ℝ)/8) ≤
      2*(2 : ℝ)^(-(n : ℝ)/16) := by
    have he8 : -(1/8 : ℝ)*(n : ℝ) = -(n : ℝ)/8 := by ring
    have he16 : -((1/8 : ℝ)/2)*(n : ℝ) = -(n : ℝ)/16 := by ring
    simpa only [pow_one, Nat.reduceAdd, Nat.cast_ofNat, he8, he16] using hdecay
  calc
    _ ≤ A*(2*(2 : ℝ)^(-(n : ℝ)/16)) := mul_le_mul_of_nonneg_left hd hA.le
    _ = _ := by ring

end SymmetricSubgroupAsymptotics
