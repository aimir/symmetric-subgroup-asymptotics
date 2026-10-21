import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareSpan
import Mathlib.Algebra.Group.Subgroup.Basic

/-! A single nonzero parameter and a genuine primitive scalar action
recover a complete additive root line. This generic group lemma will be
applied to literal D root elements and their actual diagonal tori. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPrimitiveRootSaturation
variable {K G : Type*} [Field K] [Group G]

def rootParameters (root : K → G) (hzero : root 0 = 1)
    (hadd : ∀ a b, root (a + b) = root a * root b) (H : Subgroup G) : AddSubgroup K where
  carrier := {a | root a ∈ H}
  zero_mem' := by change root 0 ∈ H; rw [hzero]; exact H.one_mem
  add_mem' := by
    intro a b ha hb
    change root (a + b) ∈ H
    rw [hadd]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    change root (-a) ∈ H
    have he : root (-a) = (root a)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← hadd, neg_add_cancel, hzero]
    rw [he]
    exact H.inv_mem ha

theorem all_parameters_of_primitive_scaling [Finite K]
    (root : K → G) (hzero : root 0 = 1)
    (hadd : ∀ a b, root (a + b) = root a * root b)
    (H : Subgroup G) (T : G) (hT : T ∈ H) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (hscale : ∀ a : K, T * root a * T⁻¹ = root ((g : K) * a))
    (m : K) (hm : m ≠ 0) (hM : root m ∈ H) : ∀ a : K, root a ∈ H := by
  let B := rootParameters root hzero hadd H
  have hs : ∀ a : K, a ∈ B → (g : K) * a ∈ B := by
    intro a ha
    change root ((g : K) * a) ∈ H
    rw [← hscale]
    exact H.mul_mem (H.mul_mem hT ha) (H.inv_mem hT)
  have hs2 : ∀ a : K, a ∈ B → (g : K) ^ 2 * a ∈ B := by
    intro a ha
    have hh := hs _ (hs _ ha)
    simpa only [pow_two, mul_assoc] using hh
  have hp : ∀ k : ℕ, m * (g : K) ^ (2 * k) ∈ B := by
    intro k
    induction k with
    | zero => simpa only [Nat.mul_zero, pow_zero, mul_one] using hM
    | succ k ih =>
      have he : m * (g : K) ^ (2 * (k + 1)) = (g : K) ^ 2 * (m * (g : K) ^ (2 * k)) := by
        rw [Nat.mul_add, pow_add]
        ring
      rw [he]
      exact hs2 _ ih
  have ht := CFSGFiniteFieldSquareSpan.eq_top_of_scaled_even_powers B g hg m hm hp
  intro a
  have ha : a ∈ B := by rw [ht]; trivial
  exact ha

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPrimitiveRootSaturation
