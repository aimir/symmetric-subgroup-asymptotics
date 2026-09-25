import SymmetricSubgroupAsymptotics.C1LowNormalized
import SymmetricSubgroupAsymptotics.C1NumericalRows
import SymmetricSubgroupAsymptotics.FusionWidthContinuation

/-! The full numerical c=1 continuation row: the low triple entry and
every finite earlier-owner row, at its actual complete complement degree.
This is a proved numerical aggregate, not a claim of group-theoretic owner
coverage or of the high-cone classification. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter
namespace SymmetricSubgroupAsymptotics
variable {ι : Type*} [Fintype ι]

def c1MenuWidth (r : ι → C1EarlierRow) : Option ι → ℕ
  | none => 3
  | some i => c1EarlierWidth (r i)

def c1MenuKernel (r : ι → C1EarlierRow) (D a : ι → ℝ) : Option ι → ℕ → ℝ
  | none => c1LowKernel
  | some i => fun b => c1EarlierKernel b (r i) (D i) (a i)

def c1ForwardRow (r : ι → C1EarlierRow) (D a : ι → ℝ) (n b : ℕ) : ℝ :=
  fusionForwardRow (c1MenuWidth r) (c1MenuKernel r D a) n b

omit [Fintype ι] in
theorem c1MenuWidth_pos (r : ι → C1EarlierRow) (i : Option ι) : 0<c1MenuWidth r i := by
  cases i with
  | none => norm_num [c1MenuWidth]
  | some i => exact c1EarlierWidth_pos (r i)

omit [Fintype ι] in
theorem c1MenuKernel_nonneg (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (hD : ∀ i,0≤D i) (ha : ∀ i,0<a i) (i : Option ι) (b : ℕ) :
    0≤c1MenuKernel r D a i b := by
  cases i with
  | none => exact c1LowKernel_nonneg b
  | some i => exact c1EarlierKernel_nonneg b (r i) (hD i) (ha i)

omit [Fintype ι] in
theorem c1MenuKernel_decay (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (hD : ∀ i,0≤D i) (ha : ∀ i,0<a i) (i : Option ι) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ b : ℕ in atTop,
      c1MenuKernel r D a i b≤C*(2:ℝ)^(-κ*(b:ℝ)) := by
  cases i with
  | none =>
    obtain ⟨C,hC,hb⟩ := c1LowKernel_eventually
    exact ⟨C,1/200,hC,by norm_num,hb⟩
  | some i =>
    obtain ⟨C,hC,hb⟩ := c1EarlierKernel_eventually (r i) (hD i) (ha i)
    exact ⟨C,1/36,hC,by norm_num,hb⟩

theorem c1ForwardRow_nonneg (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (hD : ∀ i,0≤D i) (ha : ∀ i,0<a i) (n b : ℕ) :
    0≤c1ForwardRow r D a n b :=
  fusionForwardRow_nonneg _ _ (c1MenuKernel_nonneg r D a hD ha) n b

theorem c1ForwardRow_forward (r : ι → C1EarlierRow) (D a : ι → ℝ)
    {n b : ℕ} (hn : n≤b) : c1ForwardRow r D a n b=0 :=
  fusionForwardRow_forward _ _ (c1MenuWidth_pos r) hn

/-- Every term retains s at its own untouched complement, including the
external triple inside every earlier-owner source. -/
theorem c1ForwardRow_weighted_sum (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (s : ℕ → ℝ) (n : ℕ) (hn3 : 3≤n) (hn : ∀ i,c1EarlierWidth (r i)≤n) :
    ∑ b ∈ Finset.range n,c1ForwardRow r D a n b*s b =
      c1LowKernel (n-3)*s (n-3) +
        ∑ i,c1EarlierKernel (n-c1EarlierWidth (r i)) (r i) (D i) (a i)*
          s (n-c1EarlierWidth (r i)) := by
  have h := fusionForwardRow_weighted_sum (c1MenuWidth r) (c1MenuKernel r D a)
    (c1MenuWidth_pos r) s n (by
      intro i
      cases i with
      | none => exact hn3
      | some i => exact hn i)
  simpa only [c1ForwardRow,Fintype.sum_option,c1MenuWidth,c1MenuKernel] using h

theorem c1ForwardRow_decay (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (hD : ∀ i,0≤D i) (ha : ∀ i,0<a i) :
    ∃ C κ : ℝ,0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,c1ForwardRow r D a n b≤C*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionForwardRow_decay _ _ (c1MenuWidth_pos r) (c1MenuKernel_decay r D a hD ha)

/-- Contractivity is established before bounding normalized subgroup
counts; it is not an assumed inductive boundedness statement. -/
theorem c1ForwardRow_contractive (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (hD : ∀ i,0≤D i) (ha : ∀ i,0<a i) :
    ∀ᶠ n : ℕ in atTop,∑ b ∈ Finset.range n,c1ForwardRow r D a n b≤1/2 :=
  fusionForwardRow_contractive _ _ (c1MenuWidth_pos r) (c1MenuKernel_decay r D a hD ha)

end SymmetricSubgroupAsymptotics
