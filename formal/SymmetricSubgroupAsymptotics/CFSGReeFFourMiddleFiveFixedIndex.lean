import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedOriginalImage
import SymmetricSubgroupAsymptotics.FiveAutomorphismBinaryFixedIndex
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The actual order-five middle word has fixed-subgroup index at least
sixteen on the literal derived graded two-kernel and its faithful image in
the original full-centre quotient. This is an internal centralizer bound,
not a proper-subgroup index bound for the whole original group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFiveFixedIndex
open CFSGReeFFourMiddleGradedDerivedAction CFSGReeFFourMiddleGradedOriginalImage
open CFSGReeFFourMiddleDerivedFiveSurvival FiveAutomorphismBinaryFixedIndex

theorem derived_fixed_index (m : ℕ) :
    16 ≤ (fixedSubgroup (fiveAction m)).index :=
  sixteen_le_index (derivedGradedKernel_isPGroup m) (fiveAction m) (fiveAction_order m)

theorem derived_fixed_card (m : ℕ) :
    16 * Nat.card (fixedSubgroup (fiveAction m)) ≤ Nat.card (derivedGradedKernel m) :=
  sixteen_mul_card_fixed_le (derivedGradedKernel_isPGroup m) (fiveAction m) (fiveAction_order m)

theorem imageFiveAction_val (m : ℕ) (u : kernelImage m) :
    (imageFiveAction m u).val =
      originalFiveWord m * u.val * (originalFiveWord m)⁻¹ := by
  change kernelToOriginal m (fiveAction m ((kernelEquivImage m).symm u)) = _
  have hu := congrArg (fun z : kernelImage m => z.val)
    ((kernelEquivImage m).apply_symm_apply u)
  change kernelToOriginal m ((kernelEquivImage m).symm u) = u.val at hu
  exact (kernelToOriginal_fiveAction m ((kernelEquivImage m).symm u)).trans (by rw [hu])

def imageCentralizer (m : ℕ) : Subgroup (kernelImage m) :=
  (Subgroup.centralizer ({originalFiveWord m} : Set (CFSG.Models.ReeF4 m))).comap
    (kernelImage m).subtype

theorem fixed_eq_imageCentralizer (m : ℕ) :
    fixedSubgroup (imageFiveAction m) = imageCentralizer m := by
  ext u
  change imageFiveAction m u = u ↔
    u.val ∈ Subgroup.centralizer ({originalFiveWord m} : Set (CFSG.Models.ReeF4 m))
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hv := congrArg (fun z : kernelImage m => z.val) h
    dsimp only at hv
    rw [imageFiveAction_val] at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  · intro h
    apply Subtype.ext
    rw [imageFiveAction_val]
    exact mul_inv_eq_iff_eq_mul.mpr h.symm

theorem image_fixed_index (m : ℕ) :
    16 ≤ (fixedSubgroup (imageFiveAction m)).index :=
  sixteen_le_index (kernelImage_isPGroup m) (imageFiveAction m) (imageFiveAction_order m)

theorem image_fixed_card (m : ℕ) :
    16 * Nat.card (fixedSubgroup (imageFiveAction m)) ≤ Nat.card (kernelImage m) :=
  sixteen_mul_card_fixed_le (kernelImage_isPGroup m) (imageFiveAction m) (imageFiveAction_order m)

theorem imageCentralizer_index (m : ℕ) : 16 ≤ (imageCentralizer m).index := by
  rw [← fixed_eq_imageCentralizer]
  exact image_fixed_index m

theorem imageCentralizer_card (m : ℕ) :
    16 * Nat.card (imageCentralizer m) ≤ Nat.card (kernelImage m) := by
  rw [← fixed_eq_imageCentralizer]
  exact image_fixed_card m

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFiveFixedIndex
