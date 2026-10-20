import SymmetricSubgroupAsymptotics.CoprimeFaithfulSupportCompression
import SymmetricSubgroupAsymptotics.NilpotentPrimeFactorSplit
import SymmetricSubgroupAsymptotics.BlockKernelClassBound

/-! All mixed-prime nilpotent class counting reduces to the corresponding
prime-group estimates on faithful actions. Coprime compression charges the
prime actions to disjoint supports in the same original degree. This file
does not supply or assume a new published class-number theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NilpotentConjugacyClassPrimeReduction

private theorem class_card_congr {A B : Type} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) :
    Nat.card (ConjClasses A) = Nat.card (ConjClasses B) := by
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)

private def kernelSndEquiv (A B : Type) [Group A] [Group B] :
    (MonoidHom.snd A B).ker ≃* A where
  toFun k := k.val.1
  invFun a := ⟨(a, 1), rfl⟩
  left_inv k := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact k.property.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem class_card_product_le
    (A B : Type) [Group A] [Finite A] [Group B] [Finite B] :
    Nat.card (ConjClasses (A × B)) ≤
      Nat.card (ConjClasses A) * Nat.card (ConjClasses B) := by
  let f := MonoidHom.snd A B
  have hf : Function.Surjective f := fun b => ⟨(1, b), rfl⟩
  have h := conjugacyClass_card_le_normal_mul_quotient f.ker
  have hker := class_card_congr (kernelSndEquiv A B)
  have hquot := class_card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf)
  rw [hker, hquot] at h
  exact h

/-- A shared rate for prime groups extends to every actual nilpotent
permutation action. The prime hypotheses are genuine smaller proof
obligations, not an installed class-number input. -/
theorem class_bound_of_prime_bounds (c : ℝ) (hc : 1 ≤ c)
    (hprime : ∀ (p : ℕ) [Fact p.Prime] (P Y : Type)
      [Group P] [Finite P] [Finite Y] [MulAction P Y] [FaithfulSMul P Y],
      IsPGroup p P → (Nat.card (ConjClasses P) : ℝ) ≤ c ^ Nat.card Y)
    (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G]
    [Finite X] [MulAction G X] [FaithfulSMul G X] :
    (Nat.card (ConjClasses G) : ℝ) ≤ c ^ Nat.card X := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hmain : ∀ n : ℕ, ∀ (H Y : Type) [Group H] [Finite H]
      [Group.IsNilpotent H] [Finite Y] [MulAction H Y] [FaithfulSMul H Y],
      Nat.card H = n → (Nat.card (ConjClasses H) : ℝ) ≤ c ^ Nat.card Y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H Y _ _ _ _ _ _ hcard
      rcases subsingleton_or_nontrivial H with hH | hH
      · letI : Subsingleton H := hH
        have hcardH : Nat.card H = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        have hclass : Nat.card (ConjClasses H) ≤ 1 := by
          rw [← hcardH]
          exact Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective
        exact (by exact_mod_cast hclass : (Nat.card (ConjClasses H) : ℝ) ≤ 1).trans
          (one_le_pow₀ hc)
      · letI : Nontrivial H := hH
        have hne : Nat.card H ≠ 1 := by
          intro hone
          have hs := (Nat.card_eq_one_iff_unique.mp hone).1
          obtain ⟨a, b, hab⟩ := exists_pair_ne H
          exact hab (hs.elim a b)
        obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hne
        letI : Fact p.Prime := ⟨hp⟩
        let A := NilpotentPrimeFactorSplit.PrimePart p H
        let B := NilpotentPrimeFactorSplit.Complement p H
        let e : H ≃* A × B := NilpotentPrimeFactorSplit.equiv p H
        letI : Group.IsNilpotent B := NilpotentPrimeFactorSplit.complement_nilpotent p H
        letI : MulAction (A × B) Y := MulAction.compHom Y e.symm.toMonoidHom
        letI : FaithfulSMul (A × B) Y := {
          eq_of_smul_eq_smul := fun {a b} hab =>
            e.symm.injective (eq_of_smul_eq_smul (α := Y) hab) }
        have hcop := NilpotentPrimeFactorSplit.factors_coprime p H
        let YA := CoprimeFaithfulSupportCompression.LeftSupport A B Y
        let YB := CoprimeFaithfulSupportCompression.RightSupport A B Y
        letI : FaithfulSMul A YA := CoprimeFaithfulSupportCompression.faithful_left A B Y hcop
        letI : FaithfulSMul B YB := CoprimeFaithfulSupportCompression.faithful_right A B Y hcop
        have hA := hprime p A YA (NilpotentPrimeFactorSplit.primePart_isPGroup p H)
        have hlt : Nat.card B < Nat.card H :=
          NilpotentPrimeFactorSplit.complement_card_lt p H hpdiv
        have hB := ih (Nat.card B) (by omega) B YB rfl
        have hbudget := CoprimeFaithfulSupportCompression.support_budget A B Y hcop
        calc
          (Nat.card (ConjClasses H) : ℝ) = Nat.card (ConjClasses (A × B)) := by
            rw [class_card_congr e]
          _ ≤ (Nat.card (ConjClasses A) : ℝ) * Nat.card (ConjClasses B) := by
            exact_mod_cast class_card_product_le A B
          _ ≤ c ^ Nat.card YA * c ^ Nat.card YB :=
            mul_le_mul hA hB (Nat.cast_nonneg _) (pow_nonneg hc0 _)
          _ = c ^ (Nat.card YA + Nat.card YB) := (pow_add _ _ _).symm
          _ ≤ c ^ Nat.card Y := pow_le_pow_right₀ hc hbudget
  exact hmain (Nat.card G) G X rfl

end SymmetricSubgroupAsymptotics.NilpotentConjugacyClassPrimeReduction
