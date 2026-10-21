import SymmetricSubgroupAsymptotics.CFSGRootSubgroupExtraction

/-! The double-commutator root extraction identity for a genuine
additive parameter group. Distinct commuting root coordinates may scale
differently; the identity retains every coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveRootExtraction
variable {V G : Type*} [AddCommGroup V] [Group G]

theorem double_commutator (root : V → G)
    (hAdd : ∀ a b : V, root (a + b) = root a * root b) (hZero : root 0 = 1)
    (h w : G) (f g : V →+ V) (v : V)
    (hScale : ∀ a : V, h * root a * h⁻¹ = root (f a))
    (hScale' : ∀ a : V, (w * h * w⁻¹) * root a * (w * h * w⁻¹)⁻¹ = root (g a))
    (hComm : Commute (w * h * w⁻¹) h) :
    ⁅(root v * w) * h * (root v * w)⁻¹, h⁆ = root (v - g v - f (v - g v)) := by
  have hNeg : ∀ a : V, root (-a) = (root a)⁻¹ := by
    intro a
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← hAdd, add_neg_cancel, hZero]
  let t := w * h * w⁻¹
  have hScaleT : ∀ a : V, t * root a * t⁻¹ = root (g a) := hScale'
  have ht : t * h * t⁻¹ = h := by
    change (w * h * w⁻¹) * h * (w * h * w⁻¹)⁻¹ = h
    rw [hComm.eq]
    group
  have hy : (root v * w) * h * (root v * w)⁻¹ = root (v - g v) * t := by
    calc
      (root v * w) * h * (root v * w)⁻¹ = root v * t * root (-v) := by
        rw [hNeg]
        dsimp [t]
        group
      _ = root v * (t * root (-v) * t⁻¹) * t := by group
      _ = root v * root (g (-v)) * t := by rw [hScaleT]
      _ = root (v - g v) * t := by rw [map_neg, ← hAdd, sub_eq_add_neg]
  rw [hy, commutatorElement_def]
  calc
    (root (v - g v) * t) * h * (root (v - g v) * t)⁻¹ * h⁻¹ =
        root (v - g v) * (t * h * t⁻¹) * (root (v - g v))⁻¹ * h⁻¹ := by group
    _ = root (v - g v) * h * (root (v - g v))⁻¹ * h⁻¹ := by rw [ht]
    _ = root (v - g v) * (h * root (-(v - g v)) * h⁻¹) := by rw [hNeg]; group
    _ = root (v - g v) * root (f (-(v - g v))) := by rw [hScale]
    _ = root (v - g v - f (v - g v)) := by
      rw [map_neg, ← hAdd]
      simp only [sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGAdditiveRootExtraction
