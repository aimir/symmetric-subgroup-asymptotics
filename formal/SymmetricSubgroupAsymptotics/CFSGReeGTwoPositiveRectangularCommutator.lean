import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCommutatorSeeds

/-! The literal commutator pairing between an arbitrary first-coordinate
representative and an arbitrary element of its first-coordinate kernel.
Both elements can therefore be taken in the same arbitrary subgroup.
No extension-field linearity of their coordinate images is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveRectangularCommutator

open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveFirstQuotient
open scoped commutatorElement

theorem kernel_commutator (m : ℕ) (x y : fixedPositiveGroup m)
    (hy : y ∈ firstKernel m) :
    ⁅y, x⁆ = centralHom m (Multiplicative.ofAdd
      (-(coordinates m x 0) * coordinates m y 1)) := by
  obtain ⟨a, rfl⟩ := fixedPositiveChart_surjective m x
  obtain ⟨b, rfl⟩ := fixedPositiveChart_surjective m y
  have hb : b 0 = 0 := (chart_mem_firstKernel_iff m b).mp hy
  simp only [coordinates_chart]
  have he : fixedPositiveChart m b * fixedPositiveChart m a =
      centralHom m (Multiplicative.ofAdd (-(a 0) * b 1)) *
        (fixedPositiveChart m a * fixedPositiveChart m b) := by
    change fixedPositiveChart m b * fixedPositiveChart m a =
      fixedPositiveChart m ![0, 0, -(a 0) * b 1] *
        (fixedPositiveChart m a * fixedPositiveChart m b)
    rw [chart_mul, chart_mul, chart_mul]
    apply congrArg (fixedPositiveChart m)
    funext i
    fin_cases i <;> simp [productCoordinates, hb] <;> ring
  rw [commutatorElement_def, he]
  group

theorem product_mem_central_preimage (m : ℕ) (L : Subgroup (fixedPositiveGroup m))
    (x y : fixedPositiveGroup m) (hx : x ∈ L) (hy : y ∈ L)
    (hy0 : y ∈ firstKernel m) :
    Multiplicative.ofAdd (coordinates m x 0 * coordinates m y 1) ∈
      L.comap (centralHom m) := by
  have hh : ⁅y, x⁆ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem hy hx) (L.inv_mem hy)) (L.inv_mem hx)
  rw [kernel_commutator m x y hy0] at hh
  have hn := L.inv_mem hh
  change centralHom m (Multiplicative.ofAdd _) ∈ L
  simpa only [← map_inv, ← ofAdd_neg, neg_mul, neg_neg] using hn

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveRectangularCommutator
