import SymmetricSubgroupAsymptotics.LMMHomogeneousSupportNumerics

/-! Large-local-degree scalar budget for the complete restricted simple
extension count: every quotient image, every support, every twist and
every lift remain charged. The outer logarithm is an explicit actual
input to this numerical lemma, not replaced by the larger Aut logarithm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics.LMMRestrictedSimpleExtensionNumerics
open LMMHomogeneousSupportNumerics

def restrictedCount (m u d s : ℕ) : ℕ :=
  2^(d*d)*supportCount m u*s^(m*d)

theorem extension_exponent_large_local (B : ℝ) (hB : 0  ≤  B) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r t m d s : ℕ, R  ≤  r → 2  ≤  r → 2  ≤  t → 1  ≤  s →
      (m : ℝ)  ≤  (t : ℝ)*Real.logb 2 (r : ℝ) →
      (d : ℝ)  ≤  B*(m : ℝ)*Real.logb 2 (r : ℝ) →
      Real.logb 2 (s : ℝ)  ≤  (r : ℝ)*Real.logb 2 (r : ℝ) →
      (d : ℝ)^2+(m : ℝ)*(d : ℝ)*Real.logb 2 (s : ℝ)  ≤
        ε*((r*t : ℕ) : ℝ)^2 := by
  have hlim : Tendsto (fun r : ℕ =>
      (B^2+B)*(Real.logb 2 (r : ℝ))^4/(r : ℝ)) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero,mul_div_assoc] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 4 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul (B^2+B)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  refine ⟨R,?_⟩
  intro r t m d s hRr hr ht hs hm hd horder
  let l := Real.logb 2 (r : ℝ)
  have hrR : (2 : ℝ)  ≤  r := by exact_mod_cast hr
  have hrp : 0  <  (r : ℝ) := by linarith only [hrR]
  have hl : 0  ≤  l := Real.logb_nonneg (by norm_num) (by linarith only [hrR])
  have hsmall : (B^2+B)*l^4  ≤  ε*(r : ℝ) :=
    ((div_lt_iff₀ hrp).mp (hR r hRr)).le
  have hd' : (d : ℝ)  ≤  B*(t : ℝ)*l^2 := by
    calc
      _  ≤  B*(m : ℝ)*l := hd
      _  ≤  B*((t : ℝ)*l)*l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hB) hl
      _ = _ := by ring
  have hdsq : (d : ℝ)^2  ≤  B^2*(t : ℝ)^2*l^4 := by
    convert pow_le_pow_left₀ (Nat.cast_nonneg d) hd' 2 using 1 <;> ring
  have hlogs : 0  ≤  Real.logb 2 (s : ℝ) := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast hs : (1 : ℝ) ≤ s)
  have hmd : (m : ℝ)*(d : ℝ)  ≤  ((t : ℝ)*l)*(B*(t : ℝ)*l^2) :=
    mul_le_mul hm hd' (Nat.cast_nonneg d) (by positivity)
  have hprod : (m : ℝ)*(d : ℝ)*Real.logb 2 (s : ℝ)  ≤
      B*(t : ℝ)^2*(r : ℝ)*l^4 := by
    calc
      _  ≤  (((t : ℝ)*l)*(B*(t : ℝ)*l^2))*((r : ℝ)*l) :=
        mul_le_mul hmd horder hlogs (by positivity)
      _ = _ := by ring
  have hquad : B^2*(t : ℝ)^2*l^4  ≤  B^2*(t : ℝ)^2*(r : ℝ)*l^4 := by
    have hh := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ B^2*(t : ℝ)^2*l^4)
      (by linarith only [hrR] : (1 : ℝ) ≤ r)
    convert hh using 1 <;> ring
  calc
    _  ≤  (B^2+B)*(r : ℝ)*l^4*(t : ℝ)^2 := by nlinarith only [hdsq,hprod,hquad]
    _  ≤  (ε*(r : ℝ))*((r : ℝ)*(t : ℝ)^2) := by
      convert mul_le_mul_of_nonneg_right hsmall
        (by positivity : (0 : ℝ) ≤ (r : ℝ)*(t : ℝ)^2) using 1 <;> ring
    _ = ε*((r*t : ℕ) : ℝ)^2 := by push_cast; ring

theorem restrictedCount_large_local (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r t m u d s : ℕ, R  ≤  r → 2  ≤  r → 2  ≤  t → 1  ≤  u → 1  ≤  s →
      (m : ℝ)  ≤  (t : ℝ)*Real.logb 2 (r : ℝ) →
      Real.logb 2 (u : ℝ)  ≤  A*(r : ℝ)*(Real.logb 2 (r : ℝ))^3 →
      (d : ℝ)  ≤  B*(m : ℝ)*Real.logb 2 (r : ℝ) →
      Real.logb 2 (s : ℝ)  ≤  (r : ℝ)*Real.logb 2 (r : ℝ) →
      (restrictedCount m u d s : ℝ)  ≤  (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
  obtain ⟨R₀,hR⟩ := extension_exponent_large_local B hB (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (support_envelope_eventually A (ε/2) (by positivity))
  refine ⟨max R₀ N,?_⟩
  intro r t m u d s hlocal hr ht hu hs hm hauto hd horder
  have hnr : N  ≤  r := (le_max_right _ _).trans hlocal
  have hnt : N  ≤  r*t := hnr.trans (Nat.le_mul_of_pos_right r (by omega))
  have hsupport := (log_supportCount_le A hA r t m u hr ht hu hm hauto).trans (hN (r*t) hnt)
  have hext := hR r t m d s ((le_max_left _ _).trans hlocal) hr ht hs hm hd horder
  have hspos : 0  <  (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hsupportpos : 0  <  (supportCount m u : ℝ) := by dsimp only [supportCount]; positivity
  have hlog : Real.logb 2 (restrictedCount m u d s : ℝ) =
      (d : ℝ)^2+Real.logb 2 (supportCount m u : ℝ)+
        (m : ℝ)*(d : ℝ)*Real.logb 2 (s : ℝ) := by
    simp only [restrictedCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.logb_mul (by positivity : (2 : ℝ)^(d*d)*(supportCount m u : ℝ) ≠ 0)
        (by positivity : (s : ℝ)^(m*d) ≠ 0),
      Real.logb_mul (by positivity : (2 : ℝ)^(d*d) ≠ 0) (ne_of_gt hsupportpos),
      Real.logb_pow,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    push_cast
    ring
  have hsNat : 0 < s := by omega
  have hsupportNat : 0 < supportCount m u := by dsimp only [supportCount]; positivity
  have hcountNat : 0 < restrictedCount m u d s := by dsimp only [restrictedCount]; positivity
  have hcountPos : (0 : ℝ) < (restrictedCount m u d s : ℝ) := by exact_mod_cast hcountNat
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hcountPos).mp
  rw [hlog]
  linarith only [hsupport,hext]

end SymmetricSubgroupAsymptotics.LMMRestrictedSimpleExtensionNumerics
