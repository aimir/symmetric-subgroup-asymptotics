import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
import Mathlib.Algebra.Group.Subgroup.Basic

/-! The additive carrier of literal two-by-two Hermitian matrices.
This is the exact coefficient group for the root-star cone argument,
with the field involution retained as an explicit ring automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def parameters (sigma : K ≃+* K) : AddSubgroup (Matrix (Fin 2) (Fin 2) K) where
  carrier := Hermitian sigma
  zero_mem' := by intro i j; change sigma 0 = 0; exact map_zero sigma
  add_mem' := by
    intro A B hA hB i j
    change sigma (A j i + B j i) = A i j + B i j
    rw [map_add, hA i j, hB i j]
  neg_mem' := by
    intro A hA i j
    change sigma (-A j i) = -A i j
    rw [map_neg, hA i j]

theorem mem_parameters (sigma : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) :
    A ∈ parameters sigma ↔ Hermitian sigma A := Iff.rfl

def rankOneParameter (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (a : K) (ha : sigma a = a) (v : Fin 2 → K) : parameters sigma :=
  ⟨rankOne sigma a v, rankOne_hermitian sigma hsigma a ha v⟩

theorem parameter_det_zero_iff_rankOne (sigma : K ≃+* K)
    (A : parameters sigma) (hne : A.val ≠ 0) :
    A.val.det = 0 ↔ ∃ (a : K) (v : Fin 2 → K),
      a ≠ 0 ∧ sigma a = a ∧ v ≠ 0 ∧ A.val = rankOne sigma a v := by
  constructor
  · exact fun h => hermitian_det_zero_rankOne sigma A.val A.property h hne
  · rintro ⟨a, v, _, _, _, he⟩
    rw [he, rankOne_det]

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
