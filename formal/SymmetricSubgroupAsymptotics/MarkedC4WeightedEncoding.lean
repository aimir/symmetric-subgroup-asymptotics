import SymmetricSubgroupAsymptotics.MarkedC4GenerationExtension

/-!
# Weighted finite encodings for the marked `C4` moment

The unmarked Roney-Dougal--Tracey reductions encode each source object by a
bounded-word object, with a uniform bound on every encoding fibre.  Marks are
transported along the same encoding.  This file records the elementary joint
summation step: the fibre multiplicity and the mark-extension cost are charged
together before summing over encoded objects.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- A finite encoding with fibres of size at most `M` transports a pointwise
weight bound with factor `C` to the corresponding bound on total weights. -/
theorem sum_le_uniformFiber_mul_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (code : A → B) (sourceWeight : A → ℝ) (targetWeight : B → ℝ)
    (M : ℕ) (C : ℝ)
    (hpoint : ∀ a, sourceWeight a ≤ C * targetWeight (code a))
    (hC : 0 ≤ C) (htarget : ∀ b, 0 ≤ targetWeight b)
    (hfibre : ∀ b, Nat.card {a : A // code a = b} ≤ M) :
    (∑ a, sourceWeight a) ≤ (M : ℝ) * C * ∑ b, targetWeight b := by
  calc
    (∑ a, sourceWeight a) =
        ∑ b, ∑ a : {a : A // code a = b}, sourceWeight a.1 := by
      exact (Fintype.sum_fiberwise code sourceWeight).symm
    _ ≤ ∑ b, ∑ _a : {a : A // code a = b}, C * targetWeight b := by
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro a ha
      simpa [a.2] using hpoint a.1
    _ = ∑ b, (Fintype.card {a : A // code a = b} : ℝ) *
          (C * targetWeight b) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [nsmul_eq_mul]
    _ ≤ ∑ b, (M : ℝ) * (C * targetWeight b) := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right
      · have hcard := hfibre b
        rw [Nat.card_eq_fintype_card] at hcard
        exact_mod_cast hcard
      · exact mul_nonneg hC (htarget b)
    _ = (M : ℝ) * C * ∑ b, targetWeight b := by
      rw [Finset.mul_sum]
      congr 1
      funext b
      ring

/-- The same transport when the pointwise cost is a power of two. -/
theorem sum_le_uniformFiber_mul_twoPow_mul_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (code : A → B) (sourceWeight : A → ℝ) (targetWeight : B → ℝ)
    (M e : ℕ)
    (hpoint : ∀ a, sourceWeight a ≤ (2 : ℝ) ^ e * targetWeight (code a))
    (htarget : ∀ b, 0 ≤ targetWeight b)
    (hfibre : ∀ b, Nat.card {a : A // code a = b} ≤ M) :
    (∑ a, sourceWeight a) ≤
      (M : ℝ) * (2 : ℝ) ^ e * ∑ b, targetWeight b := by
  exact sum_le_uniformFiber_mul_sum code sourceWeight targetWeight M
    ((2 : ℝ) ^ e) hpoint (by positivity) htarget hfibre

/-- Weighted form of a relative-generator encoding.  Each source object `a`
comes with a finite group `G a`, a subgroup `K a`, and at most `l` displayed
generators modulo `K a`.  The unmarked encoding has fibres of size at most
`M`; the target weight dominates the marked weight of the restriction to
`K a`.  Then all `r` marks pass through the encoding at the joint cost
`4^(r*l)`. -/
theorem homMoment_sum_le_of_relativeGenerator_encoding
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A → Type*) [∀ a, Group (G a)] [∀ a, Finite (G a)]
    (K : ∀ a, Subgroup (G a)) (S : ∀ a, Finset (G a))
    (code : A → B) (targetWeight : B → ℝ)
    (M l r : ℕ)
    (hgen : ∀ a, Subgroup.closure (((S a : Finset (G a)) : Set (G a)) ∪ K a) = ⊤)
    (hcard : ∀ a, (S a).card ≤ l)
    (htarget : ∀ b, 0 ≤ targetWeight b)
    (hrestrict : ∀ a,
      (Nat.card (K a →* Multiplicative (ZMod 4)) : ℝ) ^ r ≤
        targetWeight (code a))
    (hfibre : ∀ b, Nat.card {a : A // code a = b} ≤ M) :
    (∑ a, (Nat.card (G a →* Multiplicative (ZMod 4)) : ℝ) ^ r) ≤
      (M : ℝ) * (2 : ℝ) ^ (2 * r * l) * ∑ b, targetWeight b := by
  apply sum_le_uniformFiber_mul_twoPow_mul_sum code
    (fun a => (Nat.card (G a →* Multiplicative (ZMod 4)) : ℝ) ^ r)
    targetWeight M (2 * r * l) ?_ htarget hfibre
  intro a
  have hext := card_hom_cyclicFour_pow_le_real (K a) (S a) (hgen a) r
  have hexp : 2 * r * (S a).card ≤ 2 * r * l :=
    Nat.mul_le_mul_left (2 * r) (hcard a)
  have hpow : (2 : ℝ) ^ (2 * r * (S a).card) ≤
      (2 : ℝ) ^ (2 * r * l) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  calc
    (Nat.card (G a →* Multiplicative (ZMod 4)) : ℝ) ^ r ≤
        (Nat.card (K a →* Multiplicative (ZMod 4)) : ℝ) ^ r *
          (2 : ℝ) ^ (2 * r * (S a).card) := hext
    _ ≤ targetWeight (code a) * (2 : ℝ) ^ (2 * r * l) :=
      mul_le_mul (hrestrict a) hpow (by positivity) (htarget (code a))
    _ = (2 : ℝ) ^ (2 * r * l) * targetWeight (code a) := mul_comm _ _

end MarkedC4
end SymmetricSubgroupAsymptotics
