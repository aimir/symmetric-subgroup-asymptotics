import SymmetricSubgroupAsymptotics.ScalarFourCentralC4RetainedQuotientCoordinates
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4KilledCyclicTop
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead

/-! Every actual quotient of a cyclic cubic central-repeat target either
retains bounded central-repeat coordinates or is an image of the original
small central binary kernel. This covers every original normal denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates

private theorem cubic_nonidentity (t : CyclicThree) (ht : t≠1) :
    t=Multiplicative.ofAdd (1 : ZMod 3) ∨ t^2=Multiplicative.ofAdd (1 : ZMod 3) := by
  revert t
  decide +kernel

private theorem cubic_generates :
    Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 3))=⊤ := by
  apply top_unique
  intro t _
  have hfinite : ∀ s : CyclicThree, s=(Multiplicative.ofAdd (1 : ZMod 3))^s.toAdd.val := by
    decide +kernel
  have ht := hfinite t
  rw [ht]
  exact Subgroup.npow_mem_zpowers _ _

variable {Q H : Type} [Group Q] [Group H] [Finite Q] [Finite H] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q CyclicThree c d)
  (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))

include D hcubic

theorem quotient_dichotomy (f : Q →* H) (hf : Function.Surjective f) :
    (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
      Nonempty (ScalarFourCentralC4TopCoordinates H CyclicThree c' d')) ∨
      Nat.card H≤4^c := by
  by_cases hker : f.ker≤D.top.ker
  · left
    obtain ⟨n,hn⟩ := D.top_surjective D.cubic
    exact D.retained_quotient_coordinates f hf hker n hn
  · right
    obtain ⟨g,hgf,hgt⟩ := Set.not_subset.mp hker
    have ht : D.top g≠1 := hgt
    rcases cubic_nonidentity (D.top g) ht with hg | hg
    · apply D.killed_top_card_le f hf g
      · exact hg.trans hcubic.symm
      · exact hgf
      · rw [hcubic]; exact cubic_generates
    · apply D.killed_top_card_le f hf (g^2)
      · rw [map_pow,hg,hcubic]
      · rw [map_pow,show f g=1 from hgf,one_pow]
      · rw [hcubic]; exact cubic_generates

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
