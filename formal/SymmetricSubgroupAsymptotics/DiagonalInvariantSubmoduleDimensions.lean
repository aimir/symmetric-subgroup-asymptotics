import SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod

/-! The actual stable submodule is linearly equivalent to the product
of its encoded subspaces on distinct coordinate isotypes. Dimensions and
quotient weights therefore factor exactly. All repeated coordinates with
one scalar label remain together, including arbitrary correlations in
their encoded subspace. No dimension or cardinality formula is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules

open DiagonalIsotypeProjection

variable {k ι J : Type*} [Field k] [Fintype ι] (scalar : ι → J → k)

/-- Every original coordinate occurs in exactly one actual scalar fibre. -/
def coordinateEquiv : ι ≃ Σ a : Label scalar, Coordinate scalar a where
  toFun i := ⟨coordinateLabel scalar i,⟨i,rfl⟩⟩
  invFun j := j.2.val
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨a,⟨i,hi⟩⟩
    have ha : coordinateLabel scalar i=a := Subtype.ext hi
    subst a
    rfl

theorem card_eq_sum_coordinates :
    Fintype.card ι=∑ a : Label scalar, Fintype.card (Coordinate scalar a) :=
  (Fintype.card_congr (coordinateEquiv scalar)).trans Fintype.card_sigma

theorem restriction_mem_encode (K : Stable scalar) (a : Label scalar)
    (v : K.1) : restriction scalar a v.val∈encode scalar K a := by
  change extension scalar a (restriction scalar a v.val)∈K.1
  rw [extension_restriction]
  exact isotypeProjection_mem scalar K.1 K.2 a v.val v.property

/-- Explicit restriction and extension-by-zero reconstruction on the
literal original K, not only a bijection between submodule labels. -/
def componentsEquiv (K : Stable scalar) :
    K.1 ≃ₗ[k] (∀ a : Label scalar, encode scalar K a) where
  toFun v a := ⟨restriction scalar a v.val,restriction_mem_encode scalar K a v⟩
  invFun w := ⟨∑ a, extension scalar a (w a).val,
    K.1.sum_mem (fun a _ => (w a).property)⟩
  left_inv v := by
    apply Subtype.ext
    change (∑ a : Label scalar, extension scalar a (restriction scalar a v.val))=v.val
    simp_rw [extension_restriction]
    exact sum_isotypeProjection scalar v.val
  right_inv w := by
    funext a
    apply Subtype.ext
    change restriction scalar a (∑ b, extension scalar b (w b).val)=(w a).val
    rw [map_sum]
    calc
      (∑ b : Label scalar, restriction scalar a (extension scalar b (w b).val)) =
          restriction scalar a (extension scalar a (w a).val) := by
        apply Finset.sum_eq_single a
        · intro b _ hb
          exact restriction_extension_of_ne scalar a b (Ne.symm hb) (w b).val
        · simp
      _ = (w a).val := restriction_extension scalar a (w a).val
  map_add' v w := by
    funext a
    apply Subtype.ext
    exact map_add (restriction scalar a) v.val w.val
  map_smul' c v := by
    funext a
    apply Subtype.ext
    exact map_smul (restriction scalar a) c v.val

@[simp] theorem componentsEquiv_apply (K : Stable scalar) (v : K.1) (a : Label scalar) :
    (componentsEquiv scalar K v a).val=restriction scalar a v.val := rfl

@[simp] theorem componentsEquiv_symm_apply (K : Stable scalar)
    (w : ∀ a : Label scalar, encode scalar K a) :
    ((componentsEquiv scalar K).symm w).val=∑ a, extension scalar a (w a).val := rfl

theorem finrank_eq_sum_encode (K : Stable scalar) :
    Module.finrank k K.1=∑ a : Label scalar, Module.finrank k (encode scalar K a) := by
  rw [(componentsEquiv scalar K).finrank_eq,Module.finrank_pi_fintype]

theorem encode_finrank_le_coordinates (K : Stable scalar) (a : Label scalar) :
    Module.finrank k (encode scalar K a)≤Fintype.card (Coordinate scalar a) := by
  simpa only [Module.finrank_pi] using Submodule.finrank_le (encode scalar K a)

/-- Natural subtraction is justified separately in every original
coordinate fibre before summing; no truncated-subtraction inequality is used. -/
theorem codimension_eq_sum_encode (K : Stable scalar) :
    Fintype.card ι-Module.finrank k K.1=
      ∑ a : Label scalar,
        (Fintype.card (Coordinate scalar a)-Module.finrank k (encode scalar K a)) := by
  rw [card_eq_sum_coordinates scalar,finrank_eq_sum_encode scalar K]
  exact (Finset.sum_tsub_distrib Finset.univ
    (fun a _ => encode_finrank_le_coordinates scalar K a)).symm

/-- The exact quotient-weight identity works for any multiplicative
weight base, so both natural and real ternary counts use the same formula. -/
theorem quotient_weight_factorization (K : Stable scalar)
    {R : Type*} [CommMonoid R] (b : R) :
    b^(Fintype.card ι-Module.finrank k K.1)=
      ∏ a : Label scalar,
        b^(Fintype.card (Coordinate scalar a)-Module.finrank k (encode scalar K a)) := by
  rw [codimension_eq_sum_encode scalar K,Finset.prod_pow_eq_pow_sum]

end SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules

namespace SymmetricSubgroupAsymptotics.DiagonalInvariantSubmoduleDimensions

open DiagonalInvariantSubmodules

variable {ι J : Type*} [Fintype ι] (scalar : ι → J → ZMod 3)

/-- Ternary quotient weights retain the actual subspace dimension in
each distinct original sign isotype. -/
theorem ternary_quotient_weight (K : Stable scalar) :
    (3:ℕ)^(Fintype.card ι-Module.finrank (ZMod 3) K.1)=
      ∏ a : Label scalar,
        (3:ℕ)^(Fintype.card (Coordinate scalar a)-Module.finrank (ZMod 3) (encode scalar K a)) :=
  quotient_weight_factorization scalar K (3:ℕ)

end SymmetricSubgroupAsymptotics.DiagonalInvariantSubmoduleDimensions
