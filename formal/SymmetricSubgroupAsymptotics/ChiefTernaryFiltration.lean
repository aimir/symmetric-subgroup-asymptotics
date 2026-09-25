import SymmetricSubgroupAsymptotics.ChiefNormalStep
import SymmetricSubgroupAsymptotics.PrimeRelativeFiltration

/-! Actual local elementary evaluations and actual vanishing quotient
layers install the ternary chief-series recurrence. The evidence below
contains group/module maps, exact kernels, or perfect/coprime groups;
it never contains the desired numerical head inequality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
variable {A : Type} [Group A] [Finite A]

inductive TernaryChiefStep (B C H : Subgroup A) [B.Normal] [C.Normal] : ℕ→Prop where
  | elementary {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
      [FiniteDimensional (ZMod 3) V]
      (ρ : Representation (ZMod 3) H V) (φ : C→*Multiplicative V)
      (he : ∀ (h:H) (n:C),(φ (MulAut.conjNormal (h:A) n)).toAdd=ρ h (φ n).toAdd)
      (hkernel : localChiefAmbientKernel C H ρ φ he=B) :
      TernaryChiefStep B C H (Module.finrank (ZMod 3) V)
  | perfect (hBC : B≤C) (hQ : Group.IsPerfect (normalChainQuotient B C)) :
      TernaryChiefStep B C H 0
  | coprime (hBC : B≤C) (q : ℕ) (hq : (q:ZMod 3)≠0)
      (hQ : IsPGroup q (normalChainQuotient B C)) : TernaryChiefStep B C H 0

theorem ternaryChiefStep_le
    (B C H : Subgroup A) [B.Normal] [C.Normal] (a : ℕ)
    (step : TernaryChiefStep B C H a) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 C):ℝ)≤
      (a:ℝ)*(ternaryIndexWidth H.index:ℝ)+
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3 B):ℝ) := by
  cases step with
  | elementary ρ φ he hkernel =>
    subst B
    exact localChief_ternary_normal_step C H ρ φ he
  | perfect hBC hQ =>
    letI := hQ
    have h := primeRelativeHead_chain_le B C 3 hBC
    rw [primeRelativeHead_perfect 3 (normalChainQuotient B C),Nat.add_zero] at h
    simpa only [Nat.cast_zero,zero_mul,zero_add] using
      (show (Module.finrank (ZMod 3) (primeRelativeCharacters 3 C):ℝ)≤
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3 B):ℝ) by exact_mod_cast h)
  | coprime hBC q hq hQ =>
    have h := primeRelativeHead_chain_le B C 3 hBC
    rw [primeRelativeHead_power_group 3 (normalChainQuotient B C) q hq hQ,Nat.add_zero] at h
    simpa only [Nat.cast_zero,zero_mul,zero_add] using
      (show (Module.finrank (ZMod 3) (primeRelativeCharacters 3 C):ℝ)≤
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3 B):ℝ) by exact_mod_cast h)

/-- Aggregate a literal ambient-normal chain with actual local quotient
data. The local fibre dimensions are added once across this same chain. -/
theorem ternaryChiefFiltration_le
    (N : ℕ→Subgroup A) [∀i,(N i).Normal] (H : Subgroup A)
    (hzero : N 0=⊥) (a : ℕ→ℕ) (n : ℕ)
    (steps : ∀i<n,TernaryChiefStep (N i) (N (i+1)) H (a i)) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (N n)):ℝ)≤
      (∑i∈Finset.range n,(a i:ℝ))*(ternaryIndexWidth H.index:ℝ) := by
  induction n with
  | zero =>
    have hN : Subsingleton (N 0) := by rw [hzero]; infer_instance
    letI := hN
    have h := primeRelativeHead_perfect 3 (N 0)
    simp only [h,Nat.cast_zero,Finset.range_zero,Finset.sum_empty,zero_mul,le_refl]
  | succ n ih =>
    have hi := ih (fun i hi=>steps i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hs := ternaryChiefStep_le (N n) (N (n+1)) H (a n)
      (steps n (Nat.lt_succ_self n))
    rw [Finset.sum_range_succ]
    calc
      _≤(a n:ℝ)*(ternaryIndexWidth H.index:ℝ)+
          (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (N n)):ℝ) := hs
      _≤(a n:ℝ)*(ternaryIndexWidth H.index:ℝ)+
          (∑i∈Finset.range n,(a i:ℝ))*(ternaryIndexWidth H.index:ℝ) :=
        add_le_add le_rfl hi
      _=((∑i∈Finset.range n,(a i:ℝ))+(a n:ℝ))*(ternaryIndexWidth H.index:ℝ) := by ring

/-- The actual original top quotient is appended after the single
local chief chain. No independently enlarged source or product is used. -/
theorem ternaryChiefFiltration_with_top
    (N : ℕ→Subgroup A) [∀i,(N i).Normal] (H C : Subgroup A) [C.Normal]
    (hzero : N 0=⊥) (a : ℕ→ℕ) (n : ℕ) (hNC : N n≤C)
    (steps : ∀i<n,TernaryChiefStep (N i) (N (i+1)) H (a i)) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 C):ℝ)≤
      (∑i∈Finset.range n,(a i:ℝ))*(ternaryIndexWidth H.index:ℝ)+
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (normalChainQuotient (N n) C)):ℝ) := by
  have hc := primeRelativeHead_chain_le (N n) C 3 hNC
  have hc' : (Module.finrank (ZMod 3) (primeRelativeCharacters 3 C):ℝ)≤
      (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (N n)):ℝ)+
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (normalChainQuotient (N n) C)):ℝ) := by
    exact_mod_cast hc
  exact hc'.trans (add_le_add (ternaryChiefFiltration_le N H hzero a n steps) le_rfl)

end SymmetricSubgroupAsymptotics
