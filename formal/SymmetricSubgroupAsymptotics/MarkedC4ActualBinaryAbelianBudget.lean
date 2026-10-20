import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-! Actual binary abelian budgets use the EXISTING acknowledged ordinary
Kovács--Praeger binary quotient input in PreE7CharacterLiterature.
No duplicate prime-bound or new column-capacity hypothesis is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryAbelianBudget

/-- The full actual abelianization of a binary source has the sharp physical
half-degree order budget, not merely its first character rank. -/
theorem abelianization_bound (hKP : KovacsPraegerBinaryAbelianQuotientBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) (hJ : IsPGroup 2 J) :
    (Nat.card (Abelianization J) : ℝ)≤(2 : ℝ)^((b : ℝ)/2) := by
  have hs : Function.Surjective (Abelianization.of : J →* Abelianization J) := by
    intro a
    induction a using Quotient.inductionOn' with
    | h g => exact ⟨g,rfl⟩
  exact hKP b J (Abelianization J) (hJ.of_surjective Abelianization.of hs)
    Abelianization.of hs

/-- Every SAME actual abelian quotient inherits that budget. This is the
hypothesis needed by actual all-column Hall compression. -/
theorem section_card_le (hKP : KovacsPraegerBinaryAbelianQuotientBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) (hJ : IsPGroup 2 J)
    {A : Type} [CommGroup A] [Finite A]
    (f : J →* A) (hf : Function.Surjective f) :
    (Nat.card A : ℝ)≤(2 : ℝ)^((b : ℝ)/2) :=
  hKP b J A (hJ.of_surjective f hf) f hf

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryAbelianBudget
