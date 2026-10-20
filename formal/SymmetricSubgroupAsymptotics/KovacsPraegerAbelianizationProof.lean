import SymmetricSubgroupAsymptotics.AbelianQuotientNilpotentSupplement
import SymmetricSubgroupAsymptotics.CoprimeFaithfulSupportCompression
import SymmetricSubgroupAsymptotics.NilpotentPrimeFactorSplit
import SymmetricSubgroupAsymptotics.KovacsPraegerCubeNumerics
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization

/-! The full mixed-prime abelianization bound. First pass to an actual
nilpotent subgroup onto the same abelianization. Coprime factors then act
faithfully on compressed disjoint supports within the original degree.
Only these disjoint support budgets are multiplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.KovacsPraegerAbelianizationProof
open KovacsPraegerCubeNumerics

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

private theorem abelianization_card_product_le
    (A B : Type) [Group A] [Finite A] [Group B] [Finite B] :
    Nat.card (Abelianization (A × B)) ≤
      Nat.card (Abelianization A) * Nat.card (Abelianization B) := by
  have h := PermutationAbelianQuotientOrderBound.abelianization_card_extension
    (MonoidHom.snd A B) (fun b => ⟨(1, b), rfl⟩)
  have hker := Nat.card_congr (kernelSndEquiv A B).abelianizationCongr.toEquiv
  rw [hker] at h
  exact h

/-- The nilpotent mixed-prime estimate uses one original physical budget. -/
theorem nilpotent_abelianization_cube_le
    (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G]
    [Finite X] [MulAction G X] [FaithfulSMul G X] :
    Nat.card (Abelianization G) ^ 3 ≤ 3 ^ Nat.card X := by
  have hmain : ∀ n : ℕ, ∀ (H Y : Type) [Group H] [Finite H]
      [Group.IsNilpotent H] [Finite Y] [MulAction H Y] [FaithfulSMul H Y],
      Nat.card H = n → Nat.card (Abelianization H) ^ 3 ≤ 3 ^ Nat.card Y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H Y _ _ _ _ _ _ hcard
      rcases subsingleton_or_nontrivial H with hH | hH
      · letI : Subsingleton H := hH
        letI : Subsingleton (Abelianization H) := by
          change Subsingleton (H ⧸ commutator H)
          infer_instance
        have hAb : Nat.card (Abelianization H) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        rw [hAb, one_pow]
        exact Nat.succ_le_of_lt (Nat.pow_pos (by decide))
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
        have hA := pGroup_abelianization_cube_le p A YA
          (NilpotentPrimeFactorSplit.primePart_isPGroup p H)
        have hlt : Nat.card B < Nat.card H :=
          NilpotentPrimeFactorSplit.complement_card_lt p H hpdiv
        have hB := ih (Nat.card B) (by omega) B YB rfl
        have hbudget := CoprimeFaithfulSupportCompression.support_budget A B Y hcop
        have hAb : Nat.card (Abelianization H) = Nat.card (Abelianization (A × B)) :=
          Nat.card_congr e.abelianizationCongr.toEquiv
        calc
          Nat.card (Abelianization H) ^ 3 = Nat.card (Abelianization (A × B)) ^ 3 := by rw [hAb]
          _ ≤ (Nat.card (Abelianization A) * Nat.card (Abelianization B)) ^ 3 :=
            Nat.pow_le_pow_left (abelianization_card_product_le A B) 3
          _ = Nat.card (Abelianization A) ^ 3 * Nat.card (Abelianization B) ^ 3 := mul_pow _ _ _
          _ ≤ 3 ^ Nat.card YA * 3 ^ Nat.card YB := Nat.mul_le_mul hA hB
          _ = 3 ^ (Nat.card YA + Nat.card YB) := (pow_add _ _ _).symm
          _ ≤ 3 ^ Nat.card Y := Nat.pow_le_pow_right (by decide) hbudget
  exact hmain (Nat.card G) G X rfl

/-- The actual full abelianization, including all prime powers, obeys the
same degree budget for every finite faithful permutation action. -/
theorem abelianization_cube_le
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :
    Nat.card (Abelianization G) ^ 3 ≤ 3 ^ Nat.card X := by
  let f : G →* Abelianization G := Abelianization.of
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective (commutator G)
  obtain ⟨H, hnil, honto⟩ := exists_nilpotent_subgroup_surjective_abelian f hf
  letI : Group.IsNilpotent H := hnil
  let fH : H →* Abelianization G := f.comp H.subtype
  have hlift : Function.Surjective (Abelianization.lift fH) := by
    intro a
    obtain ⟨h, hh⟩ := honto a
    exact ⟨Abelianization.of h, (Abelianization.lift_apply_of fH h).trans hh⟩
  have hc : Nat.card (Abelianization G) ≤ Nat.card (Abelianization H) :=
    Nat.card_le_card_of_surjective _ hlift
  exact (Nat.pow_le_pow_left hc 3).trans (nilpotent_abelianization_cube_le H X)

/-- The exact former Kovács--Praeger literature interface is unconditional. -/
theorem kovacsPraegerAbelianizationBound : KovacsPraegerAbelianizationBound := by
  intro b J
  apply real_card_bound_of_cube
  simpa only [Nat.card_fin] using abelianization_cube_le J (Fin b)

end SymmetricSubgroupAsymptotics.KovacsPraegerAbelianizationProof
