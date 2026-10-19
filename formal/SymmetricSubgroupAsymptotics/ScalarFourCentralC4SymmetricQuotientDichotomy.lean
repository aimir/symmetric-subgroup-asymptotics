import SymmetricSubgroupAsymptotics.ScalarFourCentralC4KilledSmallTop
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4RetainedQuotientCoordinates
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4SymmetricNormalImage

/-! Every original quotient of an actual S3 central-repeat target either
retains the same S3 top with smaller ranks or has binary order at most
2^(2*c+1). The binary branch explicitly allows non-elementary quotients. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H]
  [Finite Q] [Finite T] [Finite H] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)
  (e : T ≃* Equiv.Perm (Fin 3))

include D e

theorem symmetric_quotient_dichotomy (hcubic : orderOf D.cubic=3)
    (f : Q →* H) (hf : Function.Surjective f) :
    (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
      Nonempty (ScalarFourCentralC4TopCoordinates H T c' d')) ∨
    (IsPGroup 2 H ∧ Nat.card H≤2^(2*c+1)) := by
  by_cases hker : f.ker≤D.top.ker
  · left
    obtain ⟨n,hn⟩ := D.top_surjective D.cubic
    exact D.retained_quotient_coordinates f hf hker n hn
  · right
    have hcube : D.cubic^3=1 := by rw [←hcubic]; exact pow_orderOf_eq_one _
    obtain ⟨n,hn,hnt⟩ := D.symmetric_normal_image_kills_cubic e hcube f hker
    have hT : Nat.card T=6 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
      norm_num
    exact ⟨D.killed_small_top_isPGroup hT hcubic f hf n hnt hn,
      D.killed_small_top_card_le hT hcubic f hf n hnt hn⟩

/-- The menu is applied to each literal original normal denominator. -/
theorem symmetric_all_original_quotients (hcubic : orderOf D.cubic=3)
    (N : Subgroup Q) [N.Normal] :
    (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
      Nonempty (ScalarFourCentralC4TopCoordinates (Q ⧸ N) T c' d')) ∨
    (IsPGroup 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N)≤2^(2*c+1)) :=
  D.symmetric_quotient_dichotomy e hcubic (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
