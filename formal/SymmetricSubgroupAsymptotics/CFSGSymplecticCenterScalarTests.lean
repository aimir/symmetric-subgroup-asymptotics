import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterTorusTests
import Mathlib.FieldTheory.Finite.Basic

/-! Every nonzero independent centre-coordinate scalar is realized
by an actual Borel conjugator, using finite characteristic-two
Frobenius surjectivity for the squared first weight. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_left_center_scalar (r : ℕ) (hr : 0 < r) (u : Kˣ) :
    ∃ g : borel K (r + 1), ∀ a b : K,
      g.val * (centerParameterElement r hr a b).val * g.val⁻¹ =
        (centerParameterElement r hr ((u : K) * a) b).val := by
  have hi : Function.Injective (fun x : K => x ^ 2) := by
    intro x y h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hi (u : K)
  change v ^ 2 = (u : K) at hv
  have hv0 : v ≠ 0 := by
    intro h
    have hzero : (u : K) = 0 := by simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hv.symm
    exact Units.ne_zero u hzero
  let w : Kˣ := Units.mk0 v hv0
  refine ⟨leftWeightTorus r hr w, ?_⟩
  intro a b
  have he : a * (w : K) ^ 2 = (u : K) * a := by
    change a * v ^ 2 = (u : K) * a
    rw [hv, mul_comm]
  have h := leftWeightTorus_center_action r hr w a b
  rwa [he] at h

theorem exists_right_center_scalar (r : ℕ) (hr : 0 < r) (u : Kˣ) :
    ∃ g : borel K (r + 1), ∀ a b : K,
      g.val * (centerParameterElement r hr a b).val * g.val⁻¹ =
        (centerParameterElement r hr a ((u : K) * b)).val := by
  let k : Fin (r + 1) := ⟨1, by omega⟩
  refine ⟨coordinateTorusInB r k u, ?_⟩
  intro a b
  simpa only [mul_comm b (u : K)] using secondTorus_center_action r hr u a b

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
