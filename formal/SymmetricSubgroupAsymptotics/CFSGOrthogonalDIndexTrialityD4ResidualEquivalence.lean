import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
import Mathlib.Tactic.Abel

/-! The original D4 extension has exactly its two original positive
head coefficients and its actual residual vector. The displayed inverse
is coordinate restriction, giving dimension+2 without a Witt assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexResidualCorrection
variable (K : Type) [Field K]

def assemble (L : Submodule K (Index 2 → K)) (a : Fin 2 → K) (z : L) : extension K L :=
  ⟨a 0 • head0 K + a 1 • head1 K + twiceTailExtension K 2 z.val,
    (extension K L).add_mem
      ((extension K L).add_mem
        ((extension K L).smul_mem (a 0) (head0_mem_extension K L))
        ((extension K L).smul_mem (a 1) (head1_mem_extension K L)))
      (twiceTail_mem_extension K L z.val z.property)⟩

theorem assemble_head0 (L : Submodule K (Index 2 → K)) (a : Fin 2 → K) (z : L) :
    (assemble K L a z).val (Sum.inl 0) = a 0 := by
  change (a 0 • head0 K + a 1 • head1 K + twiceTailExtension K 2 z.val) (Sum.inl 0) = a 0
  simp only [Pi.add_apply, Pi.smul_apply, twiceTail_positive_zero, smul_eq_mul]
  simp [head0, head1, tailSecondIndex]

theorem assemble_head1 (L : Submodule K (Index 2 → K)) (a : Fin 2 → K) (z : L) :
    (assemble K L a z).val (Sum.inl (tailSecondIndex 2)) = a 1 := by
  change (a 0 • head0 K + a 1 • head1 K + twiceTailExtension K 2 z.val)
    (Sum.inl (tailSecondIndex 2)) = a 1
  simp only [Pi.add_apply, Pi.smul_apply, twiceTail_positive_second, smul_eq_mul]
  simp [head0, head1, tailSecondIndex]

theorem assemble_restriction (L : Submodule K (Index 2 → K)) (a : Fin 2 → K) (z : L) :
    twiceTailRestriction K 2 (assemble K L a z).val = z.val := by
  change twiceTailRestriction K 2 (a 0 • head0 K + a 1 • head1 K + twiceTailExtension K 2 z.val) = z.val
  simp only [map_add, map_smul, head0, head1, twiceTailRestriction_first,
    twiceTailRestriction_second, twiceTail_leftInverse, smul_zero, zero_add]

def extensionEquiv (L : Submodule K (Index 2 → K)) :
    ((Fin 2 → K) × L) ≃ₗ[K] extension K L where
  toFun p := assemble K L p.1 p.2
  invFun x := (![x.val (Sum.inl 0), x.val (Sum.inl (tailSecondIndex 2))],
    ⟨twiceTailRestriction K 2 x.val, x.property.2.2⟩)
  left_inv p := by
    rcases p with ⟨a, z⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [assemble_head0, assemble_head1]
    · apply Subtype.ext
      exact assemble_restriction K L a z
  right_inv x := by
    apply Subtype.ext
    change x.val (Sum.inl 0) • head0 K +
      x.val (Sum.inl (tailSecondIndex 2)) • head1 K +
      twiceTailExtension K 2 (twiceTailRestriction K 2 x.val) = x.val
    exact (twice_head_tail_decomposition K 2 x.val x.property.1 x.property.2.1).symm
  map_add' p q := by
    rcases p with ⟨a, z⟩
    rcases q with ⟨b, w⟩
    apply Subtype.ext
    change (a + b) 0 • head0 K + (a + b) 1 • head1 K +
      twiceTailExtension K 2 (z.val + w.val) =
      (a 0 • head0 K + a 1 • head1 K + twiceTailExtension K 2 z.val) +
      (b 0 • head0 K + b 1 • head1 K + twiceTailExtension K 2 w.val)
    simp only [Pi.add_apply, add_smul, map_add] <;> abel
  map_smul' c p := by
    rcases p with ⟨a, z⟩
    apply Subtype.ext
    change (c * a 0) • head0 K + (c * a 1) • head1 K +
      twiceTailExtension K 2 (c • z.val) =
      c • (a 0 • head0 K + a 1 • head1 K + twiceTailExtension K 2 z.val)
    simp only [map_smul, smul_add, smul_smul]

theorem extension_finrank (L : Submodule K (Index 2 → K)) :
    Module.finrank K (extension K L) = 2 + Module.finrank K L := by
  simpa using (extensionEquiv K L).finrank_eq.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
