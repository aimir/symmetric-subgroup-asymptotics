import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.NonabelianSimpleQuotientChiefSaving
import SymmetricSubgroupAsymptotics.NonabelianMonolithicQuotientChiefSaving

/-! Exact source-map templates for finite affine complements. Simplicity
and an actual nontrivial image prove injectivity; no order identification
or chief-length receipt is assumed. Scalar extensions are treated through
their actual projective quotients, not a unique core in the extension. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds

variable {G H : Type} [Group G] [Group H]

theorem simple_hom_injective [IsSimpleGroup G] (f : G →* H)
    (hne : ∃ x : G, f x ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with h | h
  · exact h
  · obtain ⟨x,hx⟩ := hne
    exact False.elim (hx (show x ∈ f.ker by rw [h]; trivial))

theorem symmetric_hom_injective {n : ℕ} (hn : 5 ≤ n)
    (f : Equiv.Perm (Fin n) →* H)
    (hne : ∃ x : alternatingGroup (Fin n), f x.val ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  by_contra h
  letI : Nontrivial f.ker := f.ker.nontrivial_iff_ne_bot.mpr h
  have hle : alternatingGroup (Fin n) ≤ f.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance
  obtain ⟨x,hx⟩ := hne
  exact hx (hle x.property)

private theorem alternating_noncommutative (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsMulCommutative (alternatingGroup (Fin n)) := by
  rw [alternatingGroup.isMulCommutative_iff_card_le_three]
  simpa using (show ¬ n ≤ 3 by omega)

private theorem alternating_in_every_nontrivial_normal (n : ℕ) (hn : 5 ≤ n)
    (K : Subgroup (Equiv.Perm (Fin n))) (hK : K.Normal) (hne : K ≠ ⊥) :
    alternatingGroup (Fin n) ≤ K := by
  letI : K.Normal := hK
  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hne
  exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance

/-- The full order of the nonabelian simple quotient is saved on every
actual chief series, not merely one selected composition chain. -/
theorem alternating_quotient_saving [Finite G] (n : ℕ) (hn : 5 ≤ n)
    (f : G →* alternatingGroup (Fin n)) (hf : Function.Surjective f)
    (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength s +
      ArithmeticFunction.cardFactors (Nat.card (alternatingGroup (Fin n))) ≤
        ArithmeticFunction.cardFactors (Nat.card G) := by
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  exact actualChiefSeriesAbelianLength_add_simple_quotient_order_le s f hf
    (alternating_noncommutative n hn)

theorem symmetric_quotient_saving [Finite G] (n : ℕ) (hn : 5 ≤ n)
    (f : G →* Equiv.Perm (Fin n)) (hf : Function.Surjective f)
    (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength s +
      ArithmeticFunction.cardFactors (Nat.card (alternatingGroup (Fin n))) ≤
        ArithmeticFunction.cardFactors (Nat.card G) := by
  exact actualChiefSeriesAbelianLength_add_monolithic_quotient_order_le s f hf
    (alternatingGroup (Fin n)) (alternating_noncommutative n hn)
    (alternating_in_every_nontrivial_normal n hn)

theorem alternating_equiv_chief_bound [Finite G] (n : ℕ) (hn : 5 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength s ≤ 0 := by
  have h := alternating_quotient_saving n hn e.toMonoidHom e.surjective s
  have hc := Nat.card_congr e.toEquiv
  rw [hc] at h
  omega

theorem symmetric_equiv_chief_bound [Finite G] (n : ℕ) (hn : 5 ≤ n)
    (e : G ≃* Equiv.Perm (Fin n)) (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength s ≤ 1 := by
  have h := symmetric_quotient_saving n hn e.toMonoidHom e.surjective s
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card G=2*Nat.card (alternatingGroup (Fin n)) :=
    (Nat.card_congr e.toEquiv).trans (two_mul_nat_card_alternatingGroup (α := Fin n)).symm
  rw [hc,ArithmeticFunction.cardFactors_mul (by decide)
    (Nat.card_pos (α := alternatingGroup (Fin n))).ne'] at h
  norm_num at h
  omega

end SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds
