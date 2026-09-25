import SymmetricSubgroupAsymptotics.OrderedCosetTransversal
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Index

/-! Actual cyclic coset data from a normal prime-index inclusion.
The generator is lifted from the actual quotient. Its order in the
original group is unrestricted, so nonsplit extensions are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- A normal subgroup of prime index has a literal power transversal,
with exact right-coset uniqueness and the original quotient order. -/
theorem normal_primeIndex_power_transversal [Finite G]
    (H : Subgroup G) [H.Normal] (hindex : H.index = p) :
    ∃ x : G, orderOf (QuotientGroup.mk' H x) = p ∧
      (∀ y : G, ∃ h : G, h ∈ H ∧ ∃ i : Fin p, y = h * x ^ i.val) ∧
      (∀ i j : Fin p, x ^ i.val * (x ^ j.val)⁻¹ ∈ H → i = j) := by
  classical
  have hcard : Nat.card (G ⧸ H) = p := hindex
  letI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ H)
  have horder : orderOf z = p := (orderOf_eq_card_of_forall_mem_zpowers hz).trans hcard
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective H z
  refine ⟨x, by rw [hx]; exact horder, ?_, ?_⟩
  · intro y
    obtain ⟨i, hi⟩ := (finEquivZPowers (isOfFinOrder_of_finite z)).surjective
      ⟨QuotientGroup.mk' H y, hz _⟩
    have hp : z ^ i.val = QuotientGroup.mk' H y := congrArg Subtype.val hi
    let j : Fin p := ⟨i.val, by simpa only [horder] using i.isLt⟩
    have hh : y * (x ^ j.val)⁻¹ ∈ H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' H (y * (x ^ j.val)⁻¹) = 1
      rw [map_mul, map_inv, map_pow, hx]
      change QuotientGroup.mk' H y * (z ^ i.val)⁻¹ = 1
      rw [hp, mul_inv_cancel]
    exact ⟨y * (x ^ j.val)⁻¹, hh, j, by group⟩
  · intro i j hij
    have hq := (QuotientGroup.eq_one_iff (x ^ i.val * (x ^ j.val)⁻¹)).mpr hij
    change QuotientGroup.mk' H (x ^ i.val * (x ^ j.val)⁻¹) = 1 at hq
    rw [map_mul, map_inv, map_pow, map_pow, hx, mul_inv_eq_one] at hq
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by simpa only [horder] using i.isLt)
      (by simpa only [horder] using j.isLt) hq

/-- Concrete data for one original subgroup inclusion. These fields
contain actual representatives and coset equations, not a head bound. -/
structure PrimeIndexCosetStep (p : ℕ) (K L : Subgroup G) where
  le : K ≤ L
  generator : G
  generator_mem : generator ∈ L
  normalizes : generator ∈ Subgroup.normalizer K
  factor : ∀ y : G, y ∈ L → ∃ z : G, z ∈ K ∧ ∃ i : Fin p,
    y = z * generator ^ i.val
  unique : ∀ i j : Fin p,
    generator ^ i.val * (generator ^ j.val)⁻¹ ∈ K → i = j

/-- Install the actual normal inclusion into the ambient group. Only
normality inside L is used; K may be nonnormal in the larger group G. -/
theorem primeIndexCosetStep_exists [Finite G] (K L : Subgroup G)
    (hKL : K ≤ L) (hnormal : (K.subgroupOf L).Normal) (hindex : K.relIndex L = p) :
    Nonempty (PrimeIndexCosetStep p K L) := by
  letI := hnormal
  obtain ⟨x, hxorder, hfactor, hunique⟩ :=
    normal_primeIndex_power_transversal (K.subgroupOf L) hindex
  have hxnorm : (x : G) ∈ Subgroup.normalizer K := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro k
    constructor
    · intro hk
      exact (Subgroup.normal_subgroupOf_iff hKL).mp hnormal k x hk x.property
    · intro hk
      have h := (Subgroup.normal_subgroupOf_iff hKL).mp hnormal
        ((x : G) * k * (x : G)⁻¹) ((x : G)⁻¹) hk (L.inv_mem x.property)
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
        inv_mul_cancel, mul_one] using h
  refine ⟨⟨hKL, x, x.property, hxnorm, ?_, ?_⟩⟩
  · intro y hy
    obtain ⟨z, hz, i, hi⟩ := hfactor ⟨y, hy⟩
    refine ⟨z, hz, i, ?_⟩
    exact congrArg Subtype.val hi
  · intro i j hij
    apply hunique i j
    exact hij

end SymmetricSubgroupAsymptotics
