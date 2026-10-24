import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Subgroup.Basic

/-! A linear spanning set gives membership in an actual subgroup under
an additive-parameter group hom, provided every scalar multiple of each
spanning generator is realized. No scalar action on the target group is assumed. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.ScalarSpanMultiplicativeHomRange

variable {K W G : Type*} [Semiring K] [AddCommGroup W] [Module K W] [Group G]

def scalarSaturatedPreimage (h : Multiplicative W →* G) (S : Subgroup G) : Submodule K W where
  carrier := {z | ∀ a : K, h (Multiplicative.ofAdd (a • z)) ∈ S}
  zero_mem' := by
    intro a
    change h (Multiplicative.ofAdd (a • (0 : W))) ∈ S
    rw [smul_zero]
    change h 1 ∈ S
    rw [map_one]
    exact S.one_mem
  add_mem' := by
    intro z t hz ht a
    change h (Multiplicative.ofAdd (a • (z + t))) ∈ S
    rw [smul_add]
    change h (Multiplicative.ofAdd (a • z) * Multiplicative.ofAdd (a • t)) ∈ S
    rw [map_mul]
    exact S.mul_mem (hz a) (ht a)
  smul_mem' := by
    intro b z hz a
    simpa only [smul_smul] using hz (a * b)

theorem mem_of_span (h : Multiplicative W →* G) (S : Subgroup G) (A : Set W)
    (hA : ∀ z ∈ A, ∀ a : K, h (Multiplicative.ofAdd (a • z)) ∈ S)
    (z : W) (hz : z ∈ Submodule.span K A) : h (Multiplicative.ofAdd z) ∈ S := by
  have hle : Submodule.span K A ≤ scalarSaturatedPreimage h S :=
    Submodule.span_le.mpr hA
  have h := hle hz (1 : K)
  simpa only [one_smul] using h

theorem mem_of_span_eq_top (h : Multiplicative W →* G) (S : Subgroup G) (A : Set W)
    (hA : ∀ z ∈ A, ∀ a : K, h (Multiplicative.ofAdd (a • z)) ∈ S)
    (hspan : Submodule.span K A = ⊤) (z : W) : h (Multiplicative.ofAdd z) ∈ S := by
  apply mem_of_span h S A hA z
  rw [hspan]
  trivial

end SymmetricSubgroupAsymptotics.ScalarSpanMultiplicativeHomRange
