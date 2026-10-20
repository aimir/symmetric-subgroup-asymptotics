import SymmetricSubgroupAsymptotics.BinarySquareActionStructure
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalGeneratorDensity

/-! A faithful original transitive exponent-two action is regular, so
every actual normal subgroup has normal rank at most the degree exponent.
This is the elementary-top branch of the binary excess induction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank

open BinarySquareActionStructure

variable {G X : Type} [Group G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]

/-- Evaluation at an original point is a bijection for the original
transitive elementary binary action. -/
theorem card_eq_degree
    (hel : SquaresActTrivially (G := G) (X := X)) (x : X) : Nat.card G = Nat.card X := by
  have hs : ∀ g : G, g ^ 2 = 1 := squaresActTrivially_iff_pow_two.mp hel
  have hc (a b : G) : a * b = b * a :=
    (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hs g)) a b).eq
  let ev : G → X := fun g => g • x
  have hi : Function.Injective ev := by
    intro a b hab
    apply eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    rw [← hg, ← mul_smul, ← mul_smul, hc a g, hc b g, mul_smul, mul_smul]
    exact congrArg (fun z : X => g • z) hab
  have ho : Function.Surjective ev := fun y => MulAction.exists_smul_eq G x y
  exact Nat.card_congr (Equiv.ofBijective ev ⟨hi, ho⟩)

/-- The actual normal rank is at most k when the same original faithful
transitive elementary action has degree2^k. -/
theorem normalGen_le_exponent [Finite G]
    (hel : SquaresActTrivially (G := G) (X := X)) (x : X)
    (k : ℕ) (hdegree : Nat.card X = 2 ^ k)
    (N : Subgroup G) [N.Normal] : MarkedC4.normalGen N ≤ k := by
  have hcard : Nat.card G = 2 ^ k := (card_eq_degree hel x).trans hdegree
  have hb := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card N
  have hn : 2 ^ MarkedC4.normalGen N ≤ 2 ^ k :=
    hb.trans ((Subgroup.card_le_card_group N).trans_eq hcard)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hn

end SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
