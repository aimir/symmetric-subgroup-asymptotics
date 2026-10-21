import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialPureLongExtraction
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare

/-! For every finite field of order at least four, the two explicit
initial elements recover the complete actual second long-root group.
This is a subgroup statement on the same elementary C model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def secondLongRootParameters (K : Type) [Field K] (r : ℕ)
    (H : Subgroup (elementaryRootGroup K (r + 1))) : AddSubgroup K where
  carrier := {a | secondLongRoot K r a ∈ H}
  zero_mem' := by
    change secondLongRoot K r 0 ∈ H
    rw [secondLongRoot_zero]
    exact H.one_mem
  add_mem' := by
    intro a b ha hb
    change secondLongRoot K r (a + b) ∈ H
    rw [secondLongRoot_add]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    change secondLongRoot K r (-a) ∈ H
    have he : secondLongRoot K r (-a) = (secondLongRoot K r a)⁻¹ := by
      symm
      apply inv_eq_of_mul_eq_one_right
      rw [← secondLongRoot_add, add_neg_cancel, secondLongRoot_zero]
    rw [he]
    exact H.inv_mem ha

theorem all_secondLong_parameters_of_initialTorus (K : Type) [Field K] [Finite K]
    (r : ℕ) (hr : 0 < r) (H : Subgroup (elementaryRootGroup K (r + 1))) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g) (hx : initialTorus K r g ∈ H)
    (m : K) (hm : m ≠ 0) (hM : secondLongRoot K r m ∈ H) :
    ∀ a : K, secondLongRoot K r a ∈ H := by
  let B := secondLongRootParameters K r H
  have hscale : ∀ a : K, a ∈ B → (g : K) ^ 2 * a ∈ B := by
    intro a ha
    change secondLongRoot K r ((g : K) ^ 2 * a) ∈ H
    rw [← initialTorus_long_conjugation K r hr]
    exact H.mul_mem (H.mul_mem hx ha) (H.inv_mem hx)
  have hpow : ∀ k : ℕ, m * (g : K) ^ (2 * k) ∈ B := by
    intro k
    induction k with
    | zero => simpa only [Nat.mul_zero, pow_zero, mul_one] using hM
    | succ k ih =>
      have he : m * (g : K) ^ (2 * (k + 1)) =
          (g : K) ^ 2 * (m * (g : K) ^ (2 * k)) := by
        rw [Nat.mul_add, pow_add]
        ring
      rw [he]
      exact hscale _ ih
  have he := CFSGFiniteFieldSquareSpan.eq_top_of_scaled_even_powers B g hg m hm hpow
  intro a
  have ha : a ∈ B := by rw [he]; trivial
  exact ha

theorem all_secondLong_parameters_of_initial_pair (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (r : ℕ) (hr : 0 < r) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hx : initialTorus K r g ∈ H) (hy : initialMixedWeyl K r ∈ H) :
    ∀ a : K, secondLongRoot K r a ∈ H := by
  have hg2 := CFSGTypeAPrimitiveUnitSquare.square_ne_one hcard g hg
  have hm : (1 - (g : K) ^ 2) ^ 2 ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hg2))
  exact all_secondLong_parameters_of_initialTorus K r hr H g hg hx _ hm
    (initial_pure_long_mem K r hr g H hx hy)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
