import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionImage

/-! If the full original mixed commutator is the derived intersection,
the relative radical equals that same intersection. All original powers
are included: their containment follows from the actual ambient evaluation
kernel. The resulting head is exactly the actual quotient-image dimension. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G]

theorem primeRelativeRadical_le_derivedIntersection
    (hker : (primeAbelianizationGroupMap p G).ker ≤ commutator G)
    (N : Subgroup G) [N.Normal] :
    primeRelativeRadical p N ≤ N ⊓ commutator G :=
  le_inf (primeRelativeRadical_le p N)
    ((primeRelativeRadical_le_ambient_evaluation_ker p N).trans hker)

/-- Exact commutator generation closes the whole radical, including the
original power part; vanishing mixed tests alone would not suffice. -/
theorem primeRelativeRadical_eq_intersection_of_mixed_eq
    (hker : (primeAbelianizationGroupMap p G).ker ≤ commutator G)
    (N : Subgroup G) [N.Normal]
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ = N ⊓ commutator G) :
    primeRelativeRadical p N = N ⊓ commutator G := by
  apply le_antisymm (primeRelativeRadical_le_derivedIntersection p hker N)
  rw [← hcomm]
  exact (primeRelativePowerCommutator_commutator_le p N).trans
    (primeRelativePowerCommutator_le_radical p N)

variable [Finite G]

/-- The same literal intersection is canceled in the two exact order
factorizations. No character extendibility assertion is assumed. -/
theorem primeRelativeCharacters_finrank_eq_image_of_mixed_eq
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (N : Subgroup G) [N.Normal]
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ = N ⊓ commutator G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p) (primeDerivedImage p N) := by
  have hR := primeRelativeRadical_card_factorization p N
  rw [primeRelativeRadical_eq_intersection_of_mixed_eq p hker.le N hcomm] at hR
  have hI := primeDerivedImage_pow_finrank_mul_intersection p hker N
  have hp := Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := ↥(N ⊓ commutator G))) (hR.symm.trans hI.symm)
  exact Nat.pow_right_injective (Fact.out : p.Prime).one_lt hp

end SymmetricSubgroupAsymptotics
