import SymmetricSubgroupAsymptotics.SharpThreePointTopEpiEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine

/-! A cyclic residual top costs at most the original source abelianization.
Together with the derived-cubic S3 estimate this keeps one common sharp
slope for both retained and residual tops of a three-block action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SharpCyclicOrSymmetricThreeEpiEnvelope
open Non2UnipotentPrefixFiniteMenu
variable {T : Type} [Group T] [Finite T]

 theorem epi_card_le (hT : IsCyclic T ∨ Nonempty (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J T) : ℝ) ≤
      SharpThreePointTopEpiEnvelope.coefficient*(3 : ℝ)^((b : ℝ)/3) := by
  rcases hT with hcyc | he
  ·
    have hh := cyclicGroupEpimorphism_card_le_abelianization (J := J) hcyc
    have hhR : (Nat.card (GroupEpimorphism J T) : ℝ) ≤
        (Nat.card (Abelianization J) : ℝ) := by exact_mod_cast hh
    have hc : (1 : ℝ) ≤ SharpThreePointTopEpiEnvelope.coefficient := by
      unfold SharpThreePointTopEpiEnvelope.coefficient
      have hn := Nat.cast_nonneg (α := ℝ) (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3))
      linarith
    exact (hhR.trans (hKP b J)).trans
      (le_mul_of_one_le_left (by positivity) hc)
  · obtain ⟨e⟩ := he
    exact SharpThreePointTopEpiEnvelope.epi_card_le (.inr e) hKP b J

 theorem cyclic_of_card_le_two (h : Nat.card T≤2) : IsCyclic T := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : 0<Nat.card T := Nat.card_pos
  have hd : Nat.card T∣2 := by
    have he : Nat.card T=1 ∨ Nat.card T=2 := by omega
    rcases he with he | he <;> simp [he]
  exact isCyclic_of_card_dvd_prime hd

end SymmetricSubgroupAsymptotics.SharpCyclicOrSymmetricThreeEpiEnvelope
