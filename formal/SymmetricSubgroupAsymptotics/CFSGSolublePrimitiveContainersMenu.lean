import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersAffine
import Mathlib.Data.Fintype.Perm

/-! A finite native menu of actual labelled affine soluble groups.
Its parameters are a prime, a bounded dimension, a soluble subgroup of
the actual translation automorphism group, and a point permutation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers

structure TranslationParameter (n : ℕ) where
  prime : Fin (n + 1)
  dimension : Fin (logSize n)
  prime_isPrime : prime.val.Prime
  dimension_pos : 0 < dimension.val
  degree_eq : prime.val ^ dimension.val = n

@[ext] theorem TranslationParameter.ext {n : ℕ} {A B : TranslationParameter n}
    (hp : A.prime = B.prime) (hd : A.dimension = B.dimension) : A = B := by
  cases A
  cases B
  cases hp
  cases hd
  rfl

instance translationParameter_finite (n : ℕ) : Finite (TranslationParameter n) :=
  Finite.of_injective (fun P => (P.prime, P.dimension)) (by
    intro A B h
    exact TranslationParameter.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

instance translationParameter_primeFact {n : ℕ} (P : TranslationParameter n) :
    Fact P.prime.val.Prime := ⟨P.prime_isPrime⟩

instance translationParameter_neZero {n : ℕ} (P : TranslationParameter n) :
    NeZero P.prime.val := ⟨P.prime_isPrime.ne_zero⟩

abbrev CanonicalTranslation {n : ℕ} (P : TranslationParameter n) :=
  Multiplicative (Fin P.dimension.val → ZMod P.prime.val)

theorem canonicalTranslation_card {n : ℕ} (P : TranslationParameter n) :
    Nat.card (CanonicalTranslation P) = n := by
  calc
    Nat.card (CanonicalTranslation P) =
        Nat.card (Fin P.dimension.val → ZMod P.prime.val) :=
      Nat.card_congr Multiplicative.toAdd
    _ = P.prime.val ^ P.dimension.val := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    _ = n := P.degree_eq

def standardPoints {n : ℕ} (P : TranslationParameter n) : CanonicalTranslation P ≃ Fin n :=
  (Fintype.equivFin (CanonicalTranslation P)).trans (finCongr (by
    rw [← Nat.card_eq_fintype_card, canonicalTranslation_card]))

abbrev PrimitiveIndex (n : ℕ) :=
  Σ P : TranslationParameter n, SolubleComplement (CanonicalTranslation P) × Equiv.Perm (Fin n)

instance primitiveIndex_finite (n : ℕ) : Finite (PrimitiveIndex n) := inferInstance

def primitiveEnvelope {n : ℕ} (i : PrimitiveIndex n) : Subgroup (Equiv.Perm (Fin n)) :=
  labelledEnvelope (CanonicalTranslation i.1) i.2.1.val ((standardPoints i.1).trans i.2.2)

theorem primitiveEnvelope_soluble {n : ℕ} (i : PrimitiveIndex n) :
    IsSolvable (primitiveEnvelope i) := by
  letI solublePrimitiveMenu_complement : IsSolvable i.2.1.val := i.2.1.property
  exact labelledEnvelope_soluble _ _ _

theorem translationParameter_card_le (n : ℕ) :
    Nat.card (TranslationParameter n) ≤ (n + 1) * logSize n := by
  have hi : Function.Injective
      (fun P : TranslationParameter n => (P.prime, P.dimension)) := by
    intro A B h
    exact TranslationParameter.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have h := Nat.card_le_card_of_injective _ hi
  simpa only [Nat.card_prod, Nat.card_fin] using h

theorem primitiveIndex_card_le (n : ℕ) :
    Nat.card (PrimitiveIndex n) ≤
      (n + 1) * logSize n * (2 ^ (logSize n ^ 4) * n.factorial) := by
  letI solublePrimitiveMenu_parameters : Fintype (TranslationParameter n) := Fintype.ofFinite _
  change Nat.card (Σ P : TranslationParameter n,
    SolubleComplement (CanonicalTranslation P) × Equiv.Perm (Fin n)) ≤ _
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _P : TranslationParameter n, 2 ^ (logSize n ^ 4) * n.factorial := by
      apply Finset.sum_le_sum
      intro P _
      rw [Nat.card_prod]
      have h := solubleComplement_card_le (CanonicalTranslation P)
      rw [canonicalTranslation_card] at h
      have hc : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rw [hc]
      exact Nat.mul_le_mul_right _ h
    _ = Nat.card (TranslationParameter n) *
        (2 ^ (logSize n ^ 4) * n.factorial) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.mul_le_mul_right _ (translationParameter_card_le n)

end SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers
