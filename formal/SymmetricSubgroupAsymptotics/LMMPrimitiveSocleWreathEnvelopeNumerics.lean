import SymmetricSubgroupAsymptotics.LMMRestrictedSimpleExtensionNumerics
import SymmetricSubgroupAsymptotics.LMMPolylogRectangularLiftCost

/-! The complete factor-sensitive primitive-socle wreath envelope.
The actual quotient rank q is retained. Every quotient image, support,
twist and lift in the literal envelope is charged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LMMPrimitiveSocleWreathEnvelopeNumerics
open LMMHomogeneousSupportNumerics LMMRestrictedSimpleExtensionNumerics

def wholeCount (t k a q s b u : ℕ) : ℕ :=
  (2^((t*a)^2)*s^(t*q))*(supportCount (t*k) u*b^((t*k)*(t*a+q)))

theorem wholeCount_large_local (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r t k a q s b u : ℕ, R ≤ r → 2 ≤ r → 2 ≤ t →
      1 ≤ s → 1 ≤ b → 1 ≤ u →
      (k : ℝ) ≤ Real.logb 2 (r : ℝ) →
      (a : ℝ) ≤ B*(k : ℝ)*Real.logb 2 (r : ℝ) →
      Real.logb 2 (s : ℝ) ≤ a →
      Real.logb 2 (b : ℝ) ≤ (r : ℝ)*Real.logb 2 (r : ℝ) →
      Real.logb 2 (u : ℝ) ≤ A*(r : ℝ)*(Real.logb 2 (r : ℝ))^3 →
      (q : ℝ) ≤ C*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) →
      (wholeCount t k a q s b u : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
  obtain ⟨R₀,hR⟩ := restrictedCount_large_local A B hA hB (ε/3) (by positivity)
  obtain ⟨N₁,hN₁⟩ := LMMPolylogRectangularLiftCost.whole_base_lift_exponent
    C hC 2 (ε/3) (by positivity)
  obtain ⟨N₂,hN₂⟩ := LMMPolylogRectangularLiftCost.whole_base_lift_exponent
    (B*C) (mul_nonneg hB hC) 2 (ε/3) (by positivity)
  refine ⟨max R₀ (max N₁ N₂),?_⟩
  intro r t k a q s b u hlarge hr ht hs hb hu hk ha hslog hblog hulog hq
  let L := Real.logb 2 (r : ℝ)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by linarith only [hrR])
  have hslog0 : 0 ≤ Real.logb 2 (s : ℝ) := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast hs : (1 : ℝ) ≤ s)
  have hblog0 : 0 ≤ Real.logb 2 (b : ℝ) := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast hb : (1 : ℝ) ≤ b)
  have hroot : 0 < Real.sqrt (Real.logb 2 (t : ℝ)) :=
    Real.sqrt_pos.mpr (Real.logb_pos (by norm_num) (by exact_mod_cast (show 1<t by omega)))
  have hN₁r : N₁ ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hN₂r : N₂ ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hrt : r ≤ r*t := Nat.le_mul_of_pos_right r (by omega)
  have hm : ((t*k : ℕ) : ℝ) ≤ (t : ℝ)*L := by
    simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg t)
  have hd : ((t*a : ℕ) : ℝ) ≤ B*((t*k : ℕ) : ℝ)*L := by
    have hh := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg t)
    push_cast
    nlinarith only [hh]
  have hrestricted := hR r t (t*k) u (t*a) b ((le_max_left _ _).trans hlarge)
    hr ht hu hb hm hulog hd hblog
  have hsimplelog : ((t*k : ℕ) : ℝ)*(q : ℝ)*Real.logb 2 (b : ℝ) ≤
      C*(t : ℝ)^2*(r : ℝ)*L^2/Real.sqrt (Real.logb 2 (t : ℝ)) := by
    have hmkq := mul_le_mul hm hq (Nat.cast_nonneg q) (by positivity)
    have hh := mul_le_mul hmkq hblog hblog0 (by positivity)
    convert hh using 1 <;> ring
  have hsbound : Real.logb 2 (s : ℝ) ≤ B*(r : ℝ)*L^2 := by
    have hh : (a : ℝ) ≤ B*L^2 := by
      calc
        _ ≤ B*(k : ℝ)*L := ha
        _ ≤ B*L*L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hB) hL
        _ = _ := by ring
    have hh' := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ B*L^2)
      (by linarith only [hrR] : (1 : ℝ) ≤ r)
    exact (hslog.trans hh).trans (by nlinarith only [hh'])
  have hquotlog : (t : ℝ)*(q : ℝ)*Real.logb 2 (s : ℝ) ≤
      (B*C)*(t : ℝ)^2*(r : ℝ)*L^2/Real.sqrt (Real.logb 2 (t : ℝ)) := by
    have htq := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg t)
    have hh := mul_le_mul htq hsbound hslog0 (by positivity)
    convert hh using 1 <;> ring
  have hsimple : ((b^((t*k)*q) : ℕ) : ℝ) ≤ (2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2) := by
    have hb0 : 0 < b := by omega
    have hbpow : 0 < (b^((t*k)*q) : ℕ) := by positivity
    have hbpowR : (0 : ℝ) < ((b^((t*k)*q) : ℕ) : ℝ) := by exact_mod_cast hbpow
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) hbpowR).mp
    rw [Nat.cast_pow,Real.logb_pow]
    simpa only [Nat.cast_mul] using hsimplelog.trans (hN₁ r t hr ht (hN₁r.trans hrt))
  have hquot : ((s^(t*q) : ℕ) : ℝ) ≤ (2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2) := by
    have hs0 : 0 < s := by omega
    have hspow : 0 < (s^(t*q) : ℕ) := by positivity
    have hspowR : (0 : ℝ) < ((s^(t*q) : ℕ) : ℝ) := by exact_mod_cast hspow
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) hspowR).mp
    rw [Nat.cast_pow,Real.logb_pow]
    simpa only [Nat.cast_mul] using hquotlog.trans (hN₂ r t hr ht (hN₂r.trans hrt))
  have hfactor : wholeCount t k a q s b u =
      restrictedCount (t*k) u (t*a) b*s^(t*q)*b^((t*k)*q) := by
    dsimp only [wholeCount,restrictedCount]
    rw [Nat.mul_add,pow_add]
    simp only [pow_two]
    ring
  have hbound : (wholeCount t k a q s b u : ℝ) ≤
      (2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2)*
        (2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2)*(2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2) := by
    have hh := mul_le_mul (mul_le_mul hrestricted hquot (by positivity) (by positivity))
      hsimple (by positivity) (by positivity)
    rw [hfactor]
    simpa only [Nat.cast_mul] using hh
  have heq : (2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2)*
        (2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2)*(2 : ℝ)^((ε/3)*((r*t : ℕ) : ℝ)^2) =
      (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
    rw [←Real.rpow_add (by norm_num : (0 : ℝ)<2),
      ←Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    ring
  exact hbound.trans heq.le

end SymmetricSubgroupAsymptotics.LMMPrimitiveSocleWreathEnvelopeNumerics
