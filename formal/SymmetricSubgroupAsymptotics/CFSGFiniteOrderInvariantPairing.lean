import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A nondegenerate invariant bilinear pairing restricts nondegenerately
to the actual fixed space of a finite-order linear operator when the
order is nonzero in the coefficient field. The proof uses an orbit sum,
so its characteristic restriction is explicit rather than hidden in a
recognition or fixed-point lifting hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFiniteOrderInvariantPairing

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def orbitSum (T : Module.End K M) (n : ℕ) (y : M) : M :=
  ∑ i ∈ Finset.range n, (T^i) y

theorem orbitSum_fixed (T : Module.End K M) (n : ℕ) (hT : T^n = 1) (y : M) :
    T (orbitSum T n y) = orbitSum T n y := by
  have hn : (T^n) y = y := by rw [hT]; rfl
  have hzero : (T^0) y = y := rfl
  have hs : (∑ i ∈ Finset.range n, (T^(i+1)) y) + y = orbitSum T n y + y := by
    calc
      _ = ∑ i ∈ Finset.range (n+1), (T^i) y := by
        simpa only [hzero] using (Finset.sum_range_succ' (fun i => (T^i) y) n).symm
      _ = orbitSum T n y + (T^n) y := Finset.sum_range_succ _ _
      _ = _ := congrArg (fun z => orbitSum T n y + z) hn
  calc
    T (orbitSum T n y) = ∑ i ∈ Finset.range n, T ((T^i) y) := map_sum T _ _
    _ = ∑ i ∈ Finset.range n, (T^(i+1)) y := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ']
      rfl
    _ = _ := add_right_cancel hs

theorem pairing_orbitSum (T : Module.End K M) (n : ℕ)
    (B : M →ₗ[K] M →ₗ[K] K)
    (hB : ∀ x y, B (T x) (T y) = B x y)
    (x : M) (hx : T x = x) (y : M) :
    B x (orbitSum T n y) = (n : K) * B x y := by
  have hstep (z : M) : B x (T z) = B x z := by
    simpa only [hx] using hB x z
  have hi : ∀ i : ℕ, B x ((T^i) y) = B x y := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ']
      change B x (T ((T^i) y)) = _
      exact (hstep _).trans ih
  simp only [orbitSum,map_sum,hi,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem separating_on_fixed (T : Module.End K M) (n : ℕ)
    (hn : (n : K) ≠ 0) (hT : T^n = 1)
    (B : M →ₗ[K] M →ₗ[K] K)
    (hB : ∀ x y, B (T x) (T y) = B x y)
    (hsep : ∀ x, (∀ y, B x y = 0) → x = 0)
    (x : M) (hx : T x = x)
    (hzero : ∀ y, T y = y → B x y = 0) : x = 0 := by
  apply hsep x
  intro y
  have hz := hzero (orbitSum T n y) (orbitSum_fixed T n hT y)
  have hm : (n : K) * B x y = 0 := (pairing_orbitSum T n B hB x hx y).symm.trans hz
  exact (mul_eq_zero.mp hm).resolve_left hn

end SymmetricSubgroupAsymptotics.CFSGFiniteOrderInvariantPairing
