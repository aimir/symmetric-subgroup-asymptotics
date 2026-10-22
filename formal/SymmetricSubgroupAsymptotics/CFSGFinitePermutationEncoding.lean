import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index

/-! A faithful permutation family can be counted by chosen normalizations
and actual realization images. Neither a canonical representative nor
uniqueness of the decomposition is needed. The subgroup version retains
the literal index when passing to the full automorphism group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFinitePermutationEncoding

theorem card_le_normalization_mul_realization
    {H F R X : Type*} [Finite F] [Finite R]
    (action : H → Equiv.Perm X) (faithful : Function.Injective action)
    (normalization : F → Equiv.Perm X) (realization : R → Equiv.Perm X)
    (decompose : ∀ h, ∃ f r, ∀ x,
      normalization f (action h x) = realization r x) :
    Nat.card H ≤ Nat.card F * Nat.card R := by
  classical
  choose f r hr using decompose
  let code (h : H) : F × R := (f h, r h)
  have hi : Function.Injective code := by
    intro a b hab
    have hf : f a = f b := congrArg Prod.fst hab
    have he : r a = r b := congrArg Prod.snd hab
    apply faithful
    apply Equiv.ext
    intro x
    apply (normalization (f a)).injective
    rw [hr a x, he, ← hr b x, hf]
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective code hi

theorem card_le_index_mul_normalization_mul_realization
    {G F R X : Type*} [Group G] [Finite G] [Finite F] [Finite R]
    (H : Subgroup G) (k : ℕ) (hindex : H.index ≤ k)
    (action : H → Equiv.Perm X) (faithful : Function.Injective action)
    (normalization : F → Equiv.Perm X) (realization : R → Equiv.Perm X)
    (decompose : ∀ h, ∃ f r, ∀ x,
      normalization f (action h x) = realization r x) :
    Nat.card G ≤ k * (Nat.card F * Nat.card R) := by
  have hc := card_le_normalization_mul_realization action faithful
    normalization realization decompose
  calc
    Nat.card G = H.index * Nat.card H := by
      rw [mul_comm]
      exact H.card_mul_index.symm
    _ ≤ k * (Nat.card F * Nat.card R) := Nat.mul_le_mul hindex hc

end SymmetricSubgroupAsymptotics.CFSGFinitePermutationEncoding
