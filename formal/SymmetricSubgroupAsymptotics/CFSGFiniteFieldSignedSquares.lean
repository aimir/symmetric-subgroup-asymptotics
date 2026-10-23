import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! In a finite field of cardinality three modulo four, every nonzero
element is a square or the negative of a square. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldSignedSquares

theorem isSquare_or_neg (K : Type*) [Field K] [Finite K]
    (hcard : Nat.card K % 4=3) (a : K) : IsSquare a ∨ IsSquare (-a) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  by_cases ha : IsSquare a
  · exact Or.inl ha
  right
  by_contra hn
  have hneg : ¬IsSquare (-1:K) := by
    intro hs
    apply (FiniteField.isSquare_neg_one_iff.mp hs)
    simpa only [Nat.card_eq_fintype_card] using hcard
  have ha0 : a≠0 := by
    rintro rfl
    exact ha IsSquare.zero
  have h := quadraticCharFun_mul (-1:K) a
  norm_num only [neg_one_mul,quadraticCharFun,ha0,neg_ne_zero.mpr ha0,
    neg_ne_zero.mpr (one_ne_zero: (1:K)≠0),ha,hn,hneg,if_false] at h

theorem eq_square_or_neg_square (K : Type*) [Field K] [Finite K]
    (hcard : Nat.card K % 4=3) (a : K) (ha : a≠0) :
    ∃ t : Kˣ, a=(t:K)^2 ∨ a=-(t:K)^2 := by
  rcases isSquare_or_neg K hcard a with ⟨b,hb⟩ | ⟨b,hb⟩
  · have hb0 : b≠0 := by rintro rfl; exact ha (hb.trans (mul_zero _))
    exact ⟨Units.mk0 b hb0,Or.inl (by simpa only [Units.val_mk0,pow_two] using hb)⟩
  · have hb0 : b≠0 := by
      rintro rfl
      have hz : -a=0 := hb.trans (mul_zero _)
      exact ha (neg_eq_zero.mp hz)
    refine ⟨Units.mk0 b hb0,Or.inr ?_⟩
    simpa only [Units.val_mk0,pow_two,neg_neg] using congrArg Neg.neg hb

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldSignedSquares
