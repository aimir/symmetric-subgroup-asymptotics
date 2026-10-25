import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeParameterHoms
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.FiniteHomFamilyOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimeFieldBasisOrdinaryGenerators

/-! Ordinary generation of the actual relative D root group and its
same original full-centre quotient. Every signed chain parameter costs
f generators and every signed paired parameter costs 2f. Their literal
homomorphism ranges generate, yielding 2*(n+2)*f in relative rank n. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrdinaryGenerators
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeParameterHoms
open CFSGTwistedDRelativeProjectiveModel CFSGTwistedA2FixedField

abbrev ParameterIndex (n : ℕ) := (Bool × Fin n) ⊕ Bool

def ParameterGroup {n : ℕ} (q : CFSG.PrimePower) : ParameterIndex n → Type
  | Sum.inl _ => Multiplicative (fixedField q)
  | Sum.inr _ => Multiplicative (q.Extension 2)

instance parameterGroupGroup {n : ℕ} (q : CFSG.PrimePower) (j : ParameterIndex n) :
    Group (ParameterGroup q j) := by
  cases j <;> dsimp only [ParameterGroup] <;> infer_instance

instance parameterGroupFinite {n : ℕ} (q : CFSG.PrimePower) (j : ParameterIndex n) :
    Finite (ParameterGroup q j) := by
  cases j <;> dsimp only [ParameterGroup] <;> infer_instance

def parameterHom (n : ℕ) (q : CFSG.PrimePower) :
    (j : ParameterIndex n) → ParameterGroup q j →* relativeRootGroup n q
  | Sum.inl (neg, i) => chainParameterHom n q neg i
  | Sum.inr neg => pairedParameterHom n q neg

theorem parameter_ranges_generate (n : ℕ) (q : CFSG.PrimePower) :
    (⨆ j : ParameterIndex n, (parameterHom n q j).range) = ⊤ := by
  apply top_unique
  rw [← relative_generators_closure n q]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨neg, i, a, he⟩ | ⟨neg, a, he⟩
  · have hle : (parameterHom n q (Sum.inl (neg, i))).range ≤
        ⨆ j : ParameterIndex n, (parameterHom n q j).range :=
      le_iSup_of_le (Sum.inl (neg, i)) le_rfl
    exact hle ⟨Multiplicative.ofAdd a, Subtype.ext he.symm⟩
  · have hle : (parameterHom n q (Sum.inr neg)).range ≤
        ⨆ j : ParameterIndex n, (parameterHom n q j).range :=
      le_iSup_of_le (Sum.inr neg) le_rfl
    exact hle ⟨Multiplicative.ofAdd a, Subtype.ext he.symm⟩

private theorem fixed_finrank (q : CFSG.PrimePower) :
    Module.finrank (ZMod q.prime) (fixedField q) = q.exponent := by
  apply Nat.pow_right_injective q.prime_isPrime.two_le
  have hh := Module.natCard_eq_pow_finrank (K := ZMod q.prime) (V := fixedField q)
  rw [fixedField_card, Nat.card_zmod] at hh
  exact hh.symm

private theorem extension_finrank (q : CFSG.PrimePower) :
    Module.finrank (ZMod q.prime) (q.Extension 2) = 2*q.exponent :=
  GaloisField.finrank q.prime (by have := q.exponent_pos; omega)

theorem genRank_le_twice_rank_mul_exponent (n : ℕ) (q : CFSG.PrimePower) :
    MarkedC4.genRank (relativeRootGroup n q) ≤ (2*(n+2))*q.exponent := by
  have hh := FiniteHomFamilyOrdinaryGenerators.genRank_le_sum
    (ParameterGroup q) (parameterHom n q) (parameter_ranges_generate n q)
  have hlocal : ∀ j : ParameterIndex n, MarkedC4.genRank (ParameterGroup q j) ≤
      match j with
      | Sum.inl _ => q.exponent
      | Sum.inr _ => 2*q.exponent := by
    intro j
    cases j with
    | inl j =>
      exact (PrimeFieldBasisOrdinaryGenerators.genRank_le_finrank q.prime
        (V := fixedField q)).trans_eq (fixed_finrank q)
    | inr j =>
      exact (PrimeFieldBasisOrdinaryGenerators.genRank_le_finrank q.prime
        (V := q.Extension 2)).trans_eq (extension_finrank q)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (ParameterIndex n))) =>
    hlocal j)
  have hvalue : (∑ j : ParameterIndex n, match j with
      | Sum.inl _ => q.exponent
      | Sum.inr _ => 2*q.exponent) = (2*(n+2))*q.exponent := by
    simp only [Fintype.sum_sum_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    ring
  exact hh.trans (hsum.trans_eq hvalue)

theorem exists_generating_finset (n : ℕ) (q : CFSG.PrimePower) :
    ∃ S : Finset (relativeRootGroup n q), Subgroup.closure (S : Set (relativeRootGroup n q)) = ⊤ ∧
      S.card ≤ (2*(n+2))*q.exponent := by
  obtain ⟨S, hS, hgen⟩ := MarkedC4.genRank_spec (G := relativeRootGroup n q)
  exact ⟨S, hgen, hS.le.trans (genRank_le_twice_rank_mul_exponent n q)⟩

theorem original_exists_generating_finset (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s+4) q)] :
    ∃ S : Finset (CFSG.Models.TwistedD (s+4) q),
      Subgroup.closure (S : Set (CFSG.Models.TwistedD (s+4) q)) = ⊤ ∧
        S.card ≤ (2*(s+4))*q.exponent := by
  let R := relativeRootGroup (s+2) q
  let f : R →* CFSG.Models.TwistedD (s+4) q :=
    (originalRelativeProjectiveEquiv s q).symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center R))
  have hf : Function.Surjective f :=
    (originalRelativeProjectiveEquiv s q).symm.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨S, hS, hcard⟩ := exists_generating_finset (s+2) q
  refine ⟨S.image f, ?_, Finset.card_image_le.trans ?_⟩
  · rw [Finset.coe_image, ← MonoidHom.map_closure, hS,
      Subgroup.map_top_of_surjective f hf]
  · simpa only [Nat.add_assoc, show (2 : ℕ)+2 = 4 by decide] using hcard

theorem original_genRank_le_twice_rank_mul_exponent (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s+4) q)] :
    MarkedC4.genRank (CFSG.Models.TwistedD (s+4) q) ≤ (2*(s+4))*q.exponent := by
  obtain ⟨S, hS, hcard⟩ := original_exists_generating_finset s q
  exact (MarkedC4.genRank_le hS).trans hcard

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrdinaryGenerators
