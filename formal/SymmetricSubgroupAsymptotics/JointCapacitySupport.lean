import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite support functions for the coupled retained-character/normal-head
polygon. The first weight may be negative, as it is after subtracting the
terminal cohomology mark. All maxima range over the same coupled polygon. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

def jointCapacityPolygon (k n m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (k+1)).product (Finset.range (m+1))).filter
    (fun q => q.1+q.2≤n)

@[simp] theorem mem_jointCapacityPolygon {k n m δ ε : ℕ} :
    (δ,ε) ∈ jointCapacityPolygon k n m ↔ δ≤k ∧ ε≤m ∧ δ+ε≤n := by
  simp only [jointCapacityPolygon,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,
    Finset.mem_range,Nat.lt_succ_iff,and_assoc]

theorem jointCapacityPolygon_nonempty (k n m : ℕ) :
    (jointCapacityPolygon k n m).Nonempty :=
  ⟨(0,0),mem_jointCapacityPolygon.mpr ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩⟩

def jointCapacitySupport (k n m : ℕ) (x y : ℝ) : ℝ :=
  (jointCapacityPolygon k n m).sup' (jointCapacityPolygon_nonempty k n m)
    (fun q => x*(q.1 : ℝ)+y*(q.2 : ℝ))

theorem le_jointCapacitySupport {k n m δ ε : ℕ} (x y : ℝ)
    (hδ : δ≤k) (hε : ε≤m) (hjoint : δ+ε≤n) :
    x*(δ : ℝ)+y*(ε : ℝ) ≤ jointCapacitySupport k n m x y :=
  Finset.le_sup' (fun q : ℕ × ℕ => x*(q.1 : ℝ)+y*(q.2 : ℝ))
    (mem_jointCapacityPolygon.mpr ⟨hδ,hε,hjoint⟩)

theorem jointCapacitySupport_le {k n m : ℕ} {x y a : ℝ}
    (h : ∀ δ ε : ℕ, δ≤k → ε≤m → δ+ε≤n → x*(δ : ℝ)+y*(ε : ℝ)≤a) :
    jointCapacitySupport k n m x y≤a := by
  apply Finset.sup'_le
  intro q hq
  obtain ⟨hδ,hε,hjoint⟩ := mem_jointCapacityPolygon.mp hq
  exact h q.1 q.2 hδ hε hjoint

theorem jointCapacitySupport_nonneg (k n m : ℕ) (x y : ℝ) :
    0≤jointCapacitySupport k n m x y := by
  simpa using le_jointCapacitySupport (δ := 0) (ε := 0) x y
    (Nat.zero_le k) (Nat.zero_le m) (Nat.zero_le n)

theorem jointCapacitySupport_subadd (k n m : ℕ) (x y u v : ℝ) :
    jointCapacitySupport k n m (x+u) (y+v) ≤
      jointCapacitySupport k n m x y + jointCapacitySupport k n m u v := by
  apply jointCapacitySupport_le
  intro δ ε hδ hε hjoint
  have h1 := le_jointCapacitySupport x y hδ hε hjoint
  have h2 := le_jointCapacitySupport u v hδ hε hjoint
  calc
    _ = (x*(δ : ℝ)+y*(ε : ℝ))+(u*(δ : ℝ)+v*(ε : ℝ)) := by ring
    _ ≤ _ := add_le_add h1 h2

/-- A negative first mark costs nothing when the second mark is zero. -/
theorem jointCapacitySupport_zero_second_le (k n m : ℕ) (x : ℝ) :
    jointCapacitySupport k n m x 0 ≤ (k : ℝ)*max x 0 := by
  apply jointCapacitySupport_le
  intro δ ε hδ _ _
  have hδr : (δ : ℝ)≤k := Nat.cast_le.mpr hδ
  calc
    _ = x*(δ : ℝ) := by ring
    _ ≤ max x 0*(δ : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    _ ≤ max x 0*(k : ℝ) :=
      mul_le_mul_of_nonneg_left hδr (le_max_right _ _)
    _ = _ := mul_comm _ _

/-- The joint numerical transition controls arbitrary first marks and
nonnegative normal-head and H² marks. Natural subtraction is used only
after the retained dimension is proved at most k. -/
theorem jointCapacity_marked_transition
    {d₀ d₁ ρ₀ ρ₁ τ₀ τ₁ δ ε k n m a₂ : ℕ}
    (hd : d₁=d₀+δ) (hρ : ρ₁≤ρ₀+ε) (hτ : τ₁≤τ₀+(k-δ)+a₂)
    (hδ : δ≤k) (hε : ε≤m) (hjoint : δ+ε≤n)
    (x y z : ℝ) (hy : 0≤y) (hz : 0≤z) :
    x*(d₁ : ℝ)+y*(ρ₁ : ℝ)+z*(τ₁ : ℝ) ≤
      x*(d₀ : ℝ)+y*(ρ₀ : ℝ)+z*(τ₀ : ℝ) +
      z*((k : ℝ)+(max m a₂ : ℕ))+jointCapacitySupport k n m (x-z) y := by
  have hdr : (d₁ : ℝ)=(d₀ : ℝ)+δ := by exact_mod_cast hd
  have hρr : (ρ₁ : ℝ)≤(ρ₀ : ℝ)+ε := by exact_mod_cast hρ
  have hτr : (τ₁ : ℝ)≤(τ₀ : ℝ)+((k-δ : ℕ) : ℝ)+a₂ := by exact_mod_cast hτ
  rw [Nat.cast_sub hδ] at hτr
  have ha : (a₂ : ℝ)≤(max m a₂ : ℕ) := Nat.cast_le.mpr (le_max_right _ _)
  have hsupport := le_jointCapacitySupport (x-z) y hδ hε hjoint
  have hrho := mul_le_mul_of_nonneg_left hρr hy
  have htau := mul_le_mul_of_nonneg_left hτr hz
  have hrad := mul_le_mul_of_nonneg_left ha hz
  rw [hdr]
  nlinarith

end SymmetricSubgroupAsymptotics
