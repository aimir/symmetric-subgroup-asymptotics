import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignStructural
import SymmetricSubgroupAsymptotics.DegreeNineCentralProductComparator

/-!
# Complete quotient comparison through a central binary step

This is the action-free counting lemma used by the two-sign four-block
construction.  For every literal normal quotient X of a central binary
extension, its projective quotient A and A × C₂ are required only to be
quotients of one fixed comparator Q.  Central lifts and binary twists then
give

  Epi(J,X) ≤ (1 + |Hom(A,C₂)|) Z_J(Q).

Summing this theorem over the literal normal axes of a fixed group gives a
complete quotient-weight comparison.  No subgroup classification or
source-dependent optimization occurs in either statement.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev NormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- Structural data for one quotient of a central binary extension. -/
structure CentralBinaryAxisComparison
    (Q X : Type*) [Group Q] [Finite Q] [Group X] [Finite X] where
  A : Type
  [groupA : Group A]
  [finiteA : Finite A]
  projection : X →* A
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : X, z * x = x * z
  kernelCharacter : projection.ker →* C2
  kernelCharacter_injective : Function.Injective kernelCharacter
  baseQuotient : Q →* A
  baseQuotient_surjective : Function.Surjective baseQuotient
  productQuotient : Q →* (A × C2)
  productQuotient_surjective : Function.Surjective productQuotient

attribute [instance]
  CentralBinaryAxisComparison.groupA
  CentralBinaryAxisComparison.finiteA

namespace CentralBinaryAxisComparison

variable {Q X : Type*} [Group Q] [Finite Q] [Group X] [Finite X]
  (D : CentralBinaryAxisComparison Q X)

/-- Homomorphisms into the central kernel inject into binary characters. -/
theorem kernel_hom_card_le
    {J : Type*} [Group J] [Finite J] :
    Nat.card (J →* D.projection.ker) ≤ Nat.card (J →* C2) := by
  letI : Finite (J →* D.projection.ker) :=
    Finite.of_injective
      (fun f : J →* D.projection.ker ↦ (f : J → D.projection.ker))
      DFunLike.coe_injective
  letI : Finite (J →* C2) :=
    Finite.of_injective (fun f : J →* C2 ↦ (f : J → C2))
      DFunLike.coe_injective
  exact Nat.card_le_card_of_injective
    (fun f : J →* D.projection.ker ↦ D.kernelCharacter.comp f)
    (fun f g h ↦ MonoidHom.ext fun x ↦ D.kernelCharacter_injective
      (DFunLike.congr_fun h x))

/-- One quotient of a central binary extension is controlled by Q. -/
theorem epi_card_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
      (1 + Nat.card (D.A →* C2) : ℝ) *
        completeQuotientWeight (R := Q) J := by
  have hlift := epi_card_le_centralLift (J := J) D.projection
    D.projection_surjective D.central_kernel
  have hker := D.kernel_hom_card_le (J := J)
  have htwist := epi_mul_hom_two_le_general (J := J) (A := D.A)
  have hbase :
      (Nat.card (GroupEpimorphism J D.A) : ℝ) ≤
        completeQuotientWeight (R := Q) J := by
    have haxis :
        (Nat.card (GroupEpimorphism J D.A) : ℝ) ≤
          completeQuotientWeight (R := D.A) J := by
      let M : NormalAxis D.A := ⟨⊥, inferInstance⟩
      exact card_groupEpimorphism_le_completeQuotientWeight J M
        (QuotientGroup.quotientBot (G := D.A)).symm
    exact haxis.trans
      (completeQuotientWeight_le_of_surjective
        D.baseQuotient D.baseQuotient_surjective J)
  have hproduct :
      (Nat.card (GroupEpimorphism J (D.A × C2)) : ℝ) ≤
        completeQuotientWeight (R := Q) J := by
    have haxis :
        (Nat.card (GroupEpimorphism J (D.A × C2)) : ℝ) ≤
          completeQuotientWeight (R := D.A × C2) J := by
      let M : NormalAxis (D.A × C2) := ⟨⊥, inferInstance⟩
      exact card_groupEpimorphism_le_completeQuotientWeight J M
        (QuotientGroup.quotientBot (G := D.A × C2)).symm
    exact haxis.trans
      (completeQuotientWeight_le_of_surjective
        D.productQuotient D.productQuotient_surjective J)
  have hliftReal :
      (Nat.card (GroupEpimorphism J X) : ℝ) ≤
        (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* D.projection.ker) := by
    exact_mod_cast hlift
  have hkerReal :
      (Nat.card (J →* D.projection.ker) : ℝ) ≤
        Nat.card (J →* C2) := by
    exact_mod_cast hker
  have htwistReal :
      (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* C2) ≤
        Nat.card (GroupEpimorphism J (D.A × C2)) +
          (Nat.card (GroupEpimorphism J D.A) : ℝ) *
            Nat.card (D.A →* C2) := by
    exact_mod_cast htwist
  calc
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
        (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* D.projection.ker) :=
      hliftReal
    _ ≤ (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* C2) :=
      mul_le_mul_of_nonneg_left hkerReal (Nat.cast_nonneg _)
    _ ≤ Nat.card (GroupEpimorphism J (D.A × C2)) +
          (Nat.card (GroupEpimorphism J D.A) : ℝ) *
            Nat.card (D.A →* C2) :=
      htwistReal
    _ ≤ completeQuotientWeight (R := Q) J +
          completeQuotientWeight (R := Q) J *
            Nat.card (D.A →* C2) := by
      exact add_le_add hproduct
        (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg _))
    _ = (1 + Nat.card (D.A →* C2) : ℝ) *
          completeQuotientWeight (R := Q) J := by ring

end CentralBinaryAxisComparison

/-- Central-binary quotient data for every literal normal quotient of R. -/
structure CentralBinaryCompleteComparison
    (Q R : Type*) [Group Q] [Finite Q] [Group R] [Finite R] where
  quotient : ∀ M : NormalAxis R,
    CentralBinaryAxisComparison Q (R ⧸ M.1)

namespace CentralBinaryCompleteComparison

variable {Q R : Type*} [Group Q] [Finite Q] [Group R] [Finite R]
  (D : CentralBinaryCompleteComparison Q R)

/-- Explicit finite coefficient, summed over the actual normal axes. -/
def coefficient : ℕ :=
  ∑ M : NormalAxis R, (1 + Nat.card ((D.quotient M).A →* C2))

theorem coefficient_nonneg : (0 : ℝ) ≤ D.coefficient :=
  Nat.cast_nonneg _

/-- A transparent bound for the finite coefficient.  The first parameter
controls the order of R; the second controls the orders of the displayed
projective quotients. -/
theorem coefficient_le_two_pow
    (m a : ℕ)
    (hR : Nat.card R ≤ 2 ^ m)
    (hA : ∀ M : NormalAxis R, Nat.card (D.quotient M).A ≤ a) :
    D.coefficient ≤ 2 ^ (m * m + (a + 1)) := by
  have hnormal :
      Nat.card (NormalAxis R) ≤ 2 ^ (m * m) :=
    normalSubgroup_card_le_two_pow_sq m hR
  have hterm : ∀ M : NormalAxis R,
      1 + Nat.card ((D.quotient M).A →* C2) ≤ 2 ^ (a + 1) := by
    intro M
    have hhom :
        Nat.card ((D.quotient M).A →* C2) ≤
          Nat.card ((D.quotient M).A → C2) :=
      Nat.card_le_card_of_injective
        (fun f : (D.quotient M).A →* C2 ↦
          (f : (D.quotient M).A → C2))
        DFunLike.coe_injective
    have hfun :
        Nat.card ((D.quotient M).A → C2) =
          2 ^ Nat.card (D.quotient M).A := by
      rw [Nat.card_fun]
      norm_num [C2]
    have hpow : 2 ^ Nat.card (D.quotient M).A ≤ 2 ^ a :=
      Nat.pow_le_pow_right (by norm_num) (hA M)
    calc
      1 + Nat.card ((D.quotient M).A →* C2) ≤
          1 + 2 ^ a :=
        Nat.add_le_add_left (hhom.trans (hfun.le.trans hpow)) 1
      _ ≤ 2 ^ (a + 1) := by
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
  unfold coefficient
  calc
    (∑ M : NormalAxis R,
        (1 + Nat.card ((D.quotient M).A →* C2))) ≤
        ∑ _M : NormalAxis R, 2 ^ (a + 1) := by
      apply Finset.sum_le_sum
      intro M _
      exact hterm M
    _ = Nat.card (NormalAxis R) * 2 ^ (a + 1) := by
      simp [Finset.sum_const]
    _ ≤ 2 ^ (m * m) * 2 ^ (a + 1) :=
      Nat.mul_le_mul_right _ hnormal
    _ = 2 ^ (m * m + (a + 1)) :=
      (pow_add 2 (m * m) (a + 1)).symm

/-- Complete all-normal comparison through the same fixed comparator. -/
theorem completeQuotientWeight_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      (D.coefficient : ℝ) *
        completeQuotientWeight (R := Q) J := by
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ M : NormalAxis R,
        (Nat.card (GroupEpimorphism J (R ⧸ M.1)) : ℝ)) ≤
      ∑ M : NormalAxis R,
        (1 + Nat.card ((D.quotient M).A →* C2) : ℝ) *
          completeQuotientWeight (R := Q) J := by
      apply Finset.sum_le_sum
      intro M _
      exact (D.quotient M).epi_card_le J
    _ = (∑ M : NormalAxis R,
          (1 + Nat.card ((D.quotient M).A →* C2) : ℝ)) *
          completeQuotientWeight (R := Q) J := by
      rw [Finset.sum_mul]
    _ = (D.coefficient : ℝ) *
          completeQuotientWeight (R := Q) J := by
      congr 1
      unfold coefficient
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro M _
      norm_num

end CentralBinaryCompleteComparison
end SymmetricSubgroupAsymptotics

end
