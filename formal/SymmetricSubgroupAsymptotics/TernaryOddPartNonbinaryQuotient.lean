import SymmetricSubgroupAsymptotics.TernaryOddPartKernelAnchor

/-!
# Nonbinary quotients of a group with odd part three have binary kernels

If a finite group's order divides `2^a * 3` and the group is not binary,
its order is divisible by three: otherwise coprime cancellation makes its
order a divisor of `2^a`, hence a power of two.

Applied to an actual surjective homomorphism from a group of order
`2^a * 3`, this leaves only a power of two in the original kernel. The
normal-subgroup corollary concerns the displayed subgroup itself.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Failure to be binary forces the only possible odd prime divisor.
The input is only an order divisibility, not an exact order formula. -/
theorem ternaryOddPart_three_dvd_card_of_not_isPGroup_two
    {Q : Type*} [Group Q] [Finite Q] {a : ℕ}
    (hdiv : Nat.card Q ∣ 2 ^ a * 3) (hQ : ¬ IsPGroup 2 Q) :
    3 ∣ Nat.card Q := by
  by_contra hthree
  have hcop : Nat.Coprime (Nat.card Q) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm
  have hbinaryOrder : Nat.card Q ∣ 2 ^ a :=
    hcop.dvd_of_dvd_mul_right hdiv
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbinaryOrder
  exact hQ (IsPGroup.of_card hb)

/-- An original nonbinary quotient retains the factor of three. -/
theorem ternaryOddPart_three_dvd_card_of_surjective_not_isPGroup_two
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : ¬ IsPGroup 2 Q) :
    3 ∣ Nat.card Q := by
  apply ternaryOddPart_three_dvd_card_of_not_isPGroup_two (a := a) _ hQ
  simpa only [hcard] using Subgroup.card_dvd_of_surjective pi hpi

/-- A nonbinary target forces the literal kernel of the displayed
surjection to be binary. The quotient-kernel equivalence is used only to
identify cardinalities, never to replace that kernel. -/
theorem ternaryOddPart_ker_isPGroup_two_of_not_isPGroup_two
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : ¬ IsPGroup 2 Q) :
    IsPGroup 2 pi.ker := by
  apply ternaryOddPart_isPGroup_two_of_three_dvd_quotient_card hcard pi.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective pi hpi).toEquiv]
  exact ternaryOddPart_three_dvd_card_of_surjective_not_isPGroup_two
    hcard pi hpi hQ

/-- In the literal normal-subgroup formulation, a nonbinary quotient
leaves a binary displayed normal subgroup. -/
theorem ternaryOddPart_normal_isPGroup_two_of_quotient_not_isPGroup_two
    {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (N : Subgroup G) [N.Normal] (hQ : ¬ IsPGroup 2 (G ⧸ N)) :
    IsPGroup 2 N := by
  apply ternaryOddPart_isPGroup_two_of_three_dvd_quotient_card hcard N
  apply ternaryOddPart_three_dvd_card_of_not_isPGroup_two (a := a) _ hQ
  simpa only [hcard] using N.card_quotient_dvd_card

end SymmetricSubgroupAsymptotics

end
