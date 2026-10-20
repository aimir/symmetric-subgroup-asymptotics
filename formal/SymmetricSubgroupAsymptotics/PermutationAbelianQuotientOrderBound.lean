import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBoundPGroup
import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction
import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-!
# The ordinary binary abelian-quotient bound is a theorem

An actual Sylow `p`-subgroup of the same faithful permutation group maps
onto every `p`-group quotient. For an abelian target, the full-order bound
on that Sylow subgroup's abelianization therefore controls the entire
quotient, including cyclic factors of higher `p`-power order.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

/-- The actual order of every abelian `p`-quotient of a finite faithful
permutation action is bounded by `p^(degree/p)`. -/
theorem abelian_pQuotient_card_le
    (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]
    (A : Type) [CommGroup A] [Finite A]
    (hA : IsPGroup p A) (f : G →* A) (hf : Function.Surjective f) :
    Nat.card A ≤ p ^ (Nat.card X / p) := by
  let P : Sylow p G := Classical.choice inferInstance
  let fp : (P : Subgroup G) →* A := f.comp (P : Subgroup G).subtype
  have hfp : Function.Surjective fp := sylow_restrict_surjective P hA f hf
  have hlift : Function.Surjective (Abelianization.lift fp) := by
    intro a
    obtain ⟨g, hg⟩ := hfp a
    exact ⟨Abelianization.of g, (Abelianization.lift_apply_of fp g).trans hg⟩
  exact (Nat.card_le_card_of_surjective _ hlift).trans
    (pGroup_abelianization_card_le p (P : Subgroup G) X P.isPGroup')

/-- The exact formerly published binary interface, with no literature,
generation, elementary-exponent, or splitting hypothesis. -/
theorem kovacsPraegerBinaryAbelianQuotientBound :
    KovacsPraegerBinaryAbelianQuotientBound := by
  intro b J A _ _ hA f hf
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnat : Nat.card A ≤ 2 ^ (b / 2) := by
    simpa only [Nat.card_fin] using abelian_pQuotient_card_le 2 J (Fin b) A hA f hf
  have hfloor : ((b / 2 : ℕ) : ℝ) ≤ (b : ℝ) / 2 := Nat.cast_div_le
  calc
    (Nat.card A : ℝ) ≤ (2 : ℝ) ^ (b / 2) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((b / 2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((b : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor

end SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

end
