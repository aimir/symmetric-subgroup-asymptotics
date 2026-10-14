import SymmetricSubgroupAsymptotics.TernaryOddPartNonbinaryQuotient
import SymmetricSubgroupAsymptotics.TernaryCentralizerQuotientRank

/-!
# Central binary rank four for original nonbinary ternary-odd-part quotients

Let `G` act faithfully on twenty-four points, have order `2^a * 3`, and
have every nonidentity element of exponent three act without fixed points.
Every nonbinary original quotient of `G` has central binary rank at most
four.

Nonbinaryity forces the displayed quotient map's literal kernel to be
binary. Coprime Sylow centralizer lifting and the original eight ternary
orbits then give the rank bound. No action on the quotient itself is
assumed and no original kernel is replaced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A nonbinary quotient of the original twenty-four-point action has
central binary rank at most four. Its binary-kernel condition is derived
from the exact original order, rather than supplied as a new hypothesis. -/
theorem ternaryOddPart_nonbinary_quotient_central_finrank_le_four
    {G X Q : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q] [Finite Q] {a : ℕ}
    (hX : Nat.card X = 24) (hcard : Nat.card G = 2 ^ a * 3)
    (hfree : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : ¬ IsPGroup 2 Q) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4 := by
  have hthree : 3 ∣ Nat.card G := by
    rw [hcard]
    exact dvd_mul_left 3 (2 ^ a)
  have hnine : ¬ 9 ∣ Nat.card G := by
    intro h
    rw [hcard] at h
    have hc : Nat.Coprime 9 (2 ^ a) :=
      (by decide : Nat.Coprime 9 2).pow_right a
    exact (by decide : ¬ 9 ∣ 3) (hc.dvd_of_dvd_mul_left h)
  exact TernaryCentralizerQuotientRank.central_finrank_le_four_of_semiregular_twentyFour
    hX hthree hnine hfree pi hpi
    (ternaryOddPart_ker_isPGroup_two_of_not_isPGroup_two hcard pi hpi hQ)

/-- The same rank bound for the literal quotient by a displayed normal
subgroup of the original acting group. -/
theorem ternaryOddPart_nonbinary_normal_quotient_central_finrank_le_four
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] {a : ℕ}
    (hX : Nat.card X = 24) (hcard : Nat.card G = 2 ^ a * 3)
    (hfree : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (N : Subgroup G) [N.Normal] (hQ : ¬ IsPGroup 2 (G ⧸ N)) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega (G ⧸ N))) ≤ 4 :=
  ternaryOddPart_nonbinary_quotient_central_finrank_le_four hX hcard hfree
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hQ

end SymmetricSubgroupAsymptotics

end
