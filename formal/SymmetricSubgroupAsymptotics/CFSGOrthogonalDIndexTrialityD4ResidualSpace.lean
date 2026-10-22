import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailDecomposition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection

/-! Literal extension of a residual split D2 submodule through the
original D4 root plane <e0,e1>. The two negative head coordinates are
retained as equations, so all quadratic identities include char2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexResidualCorrection
variable (K : Type) [Field K]

def head0 : Index 4 → K := Pi.single (Sum.inl 0) 1
def head1 : Index 4 → K := Pi.single (Sum.inl (tailSecondIndex 2)) 1
def rootPlane : Submodule K (Index 4 → K) := Submodule.span K {head0 K, head1 K}

def extension (L : Submodule K (Index 2 → K)) : Submodule K (Index 4 → K) where
  carrier := {x | x (Sum.inr 0) = 0 ∧ x (Sum.inr (tailSecondIndex 2)) = 0 ∧
    twiceTailRestriction K 2 x ∈ L}
  zero_mem' := ⟨rfl, rfl, by simpa only [map_zero] using L.zero_mem⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply, hx.1, hy.1, zero_add]
    · simp only [Pi.add_apply, hx.2.1, hy.2.1, zero_add]
    · rw [map_add]
      exact L.add_mem hx.2.2 hy.2.2
  smul_mem' := by
    intro a x hx
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, hx.1, smul_zero]
    · simp only [Pi.smul_apply, hx.2.1, smul_zero]
    · rw [map_smul]
      exact L.smul_mem a hx.2.2

theorem head0_mem_extension (L : Submodule K (Index 2 → K)) : head0 K ∈ extension K L := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [head0, Pi.single_apply, Sum.inr_ne_inl, if_false]
  · simp only [head0, Pi.single_apply, Sum.inr_ne_inl, if_false]
  · rw [head0, twiceTailRestriction_first]
    exact L.zero_mem

theorem head1_mem_extension (L : Submodule K (Index 2 → K)) : head1 K ∈ extension K L := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [head1, Pi.single_apply, Sum.inr_ne_inl, if_false]
  · simp only [head1, Pi.single_apply, Sum.inr_ne_inl, if_false]
  · rw [head1, twiceTailRestriction_second]
    exact L.zero_mem

theorem twiceTail_mem_extension (L : Submodule K (Index 2 → K)) (z : Index 2 → K) (hz : z ∈ L) :
    twiceTailExtension K 2 z ∈ extension K L :=
  ⟨twiceTail_negative_zero K 2 z, twiceTail_negative_second K 2 z,
    by simpa only [twiceTail_leftInverse] using hz⟩

theorem rootPlane_le_extension (L : Submodule K (Index 2 → K)) : rootPlane K ≤ extension K L := by
  apply Submodule.span_le.mpr
  rintro x (rfl | rfl)
  · exact head0_mem_extension K L
  · exact head1_mem_extension K L

theorem quadratic_eq_tail_of_heads_zero (x : Index 4 → K)
    (h0 : x (Sum.inr 0) = 0) (h1 : x (Sum.inr (tailSecondIndex 2)) = 0) :
    splitQuadraticForm K 4 x = splitQuadraticForm K 2 (twiceTailRestriction K 2 x) := by
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
  have ht := splitQ_tail_of_negative_head_zero K 3 x h0
  have htail : tailRestriction K 3 x (Sum.inr 0) = 0 := h1
  exact ht.trans (splitQ_tail_of_negative_head_zero K 2 (tailRestriction K 3 x) htail)

theorem extension_singular (L : Submodule K (Index 2 → K))
    (hL : ∀ z ∈ L, splitQuadraticForm K 2 z = 0) :
    ∀ x ∈ extension K L, splitQuadraticForm K 4 x = 0 := by
  intro x hx
  exact (quadratic_eq_tail_of_heads_zero K x hx.1 hx.2.1).trans (hL _ hx.2.2)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
