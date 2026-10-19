import SymmetricSubgroupAsymptotics.ScalarFourCentralCubicQuotientDichotomy
import SymmetricSubgroupAsymptotics.ScalarFourCentralKilledTopBinaryChart

/-! A complete structural menu for EVERY original normal quotient of an
actual cubic central-repeat group. The small branch has a genuine binary
chart, rather than an order-based numerical capacity assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q : Type} [Group Q] [Finite Q] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q CyclicThree c d)
  (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))

include D hcubic

theorem all_original_quotients (N : Subgroup Q) [N.Normal] :
    (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
      Nonempty (ScalarFourCentralTopCoordinates (Q ⧸ N) CyclicThree c' d')) ∨
    (∃ r : ℕ, r≤c ∧ Nonempty ((Q ⧸ N) ≃* (Fin r → Multiplicative (ZMod 2)))) := by
  let f : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective N
  by_cases hker : f.ker≤D.top.ker
  · left
    obtain ⟨n,hn⟩ := D.top_surjective D.cubic
    exact D.retained_quotient_coordinates f hf hker n hn
  · right
    obtain ⟨g,hgf,hgt⟩ := Set.not_subset.mp hker
    have ht : D.top g=Multiplicative.ofAdd (1 : ZMod 3) ∨
        (D.top g)^2=Multiplicative.ofAdd (1 : ZMod 3) := by
      have hfinite : ∀ t : CyclicThree, t≠1 →
          t=Multiplicative.ofAdd (1 : ZMod 3) ∨ t^2=Multiplicative.ofAdd (1 : ZMod 3) := by
        decide +kernel
      exact hfinite (D.top g) hgt
    have hgen : Subgroup.zpowers D.cubic=⊤ := by
      rw [hcubic]
      apply top_unique
      intro t _
      have hfinite : ∀ t : CyclicThree,
          (Multiplicative.ofAdd (1 : ZMod 3))^t.toAdd.val=t := by decide +kernel
      rw [← hfinite t]
      exact Subgroup.npow_mem_zpowers _ _
    rcases ht with ht | ht
    · exact D.killed_top_binary_chart f hf g (ht.trans hcubic.symm) hgf hgen
    · apply D.killed_top_binary_chart f hf (g^2) _ _ hgen
      · rw [map_pow,ht,hcubic]
      · rw [map_pow,show f g=1 from hgf,one_pow]

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
