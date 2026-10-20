import SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
import Mathlib.Data.Nat.Choose.Bounds

/-! The exact prime-power and half-degree fields for the least actual
uniform capacity, obtained from literal Sylow orbits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

theorem characteristic_primePower (e : ℕ) (hindex : H.index=p^e) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index*
      ((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1)) := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,hval,hs⟩ := inducedMackeySylow_indices H p P
  have hje (q) : j q=e := by
    apply Nat.le_antisymm
    · apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      rw [←hindex,←hs]
      exact Finset.single_le_sum (f := fun q => p^j q)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    · have h := hval q
      simpa only [hindex,Nat.factorization_pow_self (Fact.out : p.Prime)] using h
  have hcard : Fintype.card (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))=1 := by
    have heq : Fintype.card (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))*p^e=1*p^e := by
      simpa only [hje,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hindex,one_mul] using hs
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) heq
  have hn := le_of_uniform H rho (induced_sylow_middle_uniform H P rho j hj)
  simp only [hje,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard] at hn
  have hn0 : capacity H rho ≤ Module.finrank (ZMod p) V*primeGridMiddleWidth p e := by
    simpa using hn
  calc
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*(primeGridMiddleWidth p e : ℝ) := by
      exact_mod_cast hn0
    _ ≤ (Module.finrank (ZMod p) V : ℝ)*
        ((p : ℝ)^e*((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1))) :=
      mul_le_mul_of_nonneg_left
        (primeGridMiddleWidth_normalized p e (Fact.out : p.Prime).pos) (by positivity)
    _ = (Module.finrank (ZMod p) V : ℝ)*H.index*
        ((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1)) := by
      rw [hindex,Nat.cast_pow]
      ring

theorem half_of_characteristic_dvd (hdiv : p∣H.index) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index/2 := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,hval,hs⟩ := inducedMackeySylow_indices H p P
  have hhalf := le_of_sylow_middle H rho P j hj hs (1/2) (by
    intro q
    have hv : 1≤H.index.factorization p :=
      ((Fact.out : p.Prime).pow_dvd_iff_le_factorization H.index_ne_zero_of_finite).mp
        (by simpa only [pow_one] using hdiv)
    have hr : 1≤j q := hv.trans (hval q)
    have hpm : 1≤p-1 := by have := (Fact.out : p.Prime).two_le; omega
    have hK : 1≤j q*(p-1) := by
      simpa only [one_mul] using Nat.mul_le_mul hr hpm
    have hc : 2*(j q*(p-1)).choose ((j q*(p-1))/2)≤2^(j q*(p-1)) := by
      obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j q*(p-1)≠0)
      rw [ha,pow_succ]
      simpa only [Nat.mul_comm] using
        Nat.mul_le_mul_left 2 (Nat.choose_succ_le_two_pow a ((a+1)/2))
    have hcR : (((j q*(p-1)).choose ((j q*(p-1))/2) : ℕ) : ℝ)/
        (2 : ℝ)^(j q*(p-1))≤1/2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^(j q*(p-1)))).mpr
      have h : 2*((j q*(p-1)).choose ((j q*(p-1))/2) : ℝ)≤
          (2 : ℝ)^(j q*(p-1)) := by exact_mod_cast hc
      linarith
    calc
      (primeGridMiddleWidth p (j q) : ℝ)≤(p : ℝ)^j q*
          (((j q*(p-1)).choose ((j q*(p-1))/2) : ℝ)/(2 : ℝ)^(j q*(p-1))) := by
        simpa only [mul_div_assoc] using primeGridMiddleWidth_normalized p (j q) (Fact.out : p.Prime).pos
      _ ≤ (p : ℝ)^j q*(1/2) := mul_le_mul_of_nonneg_left hcR (by positivity))
  simpa only [mul_one_div] using hhalf

end SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
