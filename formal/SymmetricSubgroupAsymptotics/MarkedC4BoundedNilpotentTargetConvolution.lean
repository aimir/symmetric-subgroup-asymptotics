import SymmetricSubgroupAsymptotics.MarkedC4BoundedNilpotentProductReduction
import SymmetricSubgroupAsymptotics.MarkedC4SupportedRestrictionCutoff

/-! The filtered physical target maps injectively to the SAME-cutoff
canonical binary family. Odd choices remain unmarked finite multiplicities. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedNilpotentTargetConvolution
open OrbitCutoffFamilies SupportedPermutationRestriction BoundedNilpotentProductReduction

abbrev BinaryFamily (C a : ℕ) := {P : Subgroup (PermutationGroup a) //
  IsPGroup 2 P ∧ OrbitCutoff C P}
def binaryMoment (C a r : ℕ) : ℝ :=
  ∑ P : BinaryFamily C a, (Nat.card (P.1 →* Multiplicative (ZMod 4)) : ℝ)^r
abbrev Canonical (C b : ℕ) := Σ z : PhysicalOddConvolution.degrees b,
  BinaryFamily C z.1.1 × Subgroup (PermutationGroup z.1.2)

def forget {C b : ℕ} (z : Canonical C b) : NilpotentTargetConvolution.Canonical b :=
  ⟨z.1,(⟨z.2.1.1,z.2.1.2.1⟩,z.2.2)⟩

def canonicalMap {C b : ℕ} (z : BoundedTarget C b) : Canonical C b := by
  let c := NilpotentTargetConvolution.canonicalMap z.1
  have hc : OrbitCutoff C c.2.1.1 :=
    SupportedRestrictionCutoff.cutoff z.1.1.1 z.1.1.2.2.1 z.1.2.2.2.1 z.2.1
  exact ⟨c.1,(⟨c.2.1.1,c.2.1.2,hc⟩,c.2.2)⟩

theorem canonicalMap_injective (C b : ℕ) :
    Function.Injective (canonicalMap (C := C) (b := b)) := by
  intro z w h
  apply Subtype.ext
  apply NilpotentTargetConvolution.canonicalMap_injective b
  exact congrArg forget h

def restrictionEncoding (C b : ℕ) :
    ProductEncoding (BoundedTarget C b) (Canonical C b) Unit
      (fun z => z.1.1.2.2.1) (fun z => z.2.1.1) where
  code z := (canonicalMap z,())
  code_injective := by
    intro z w h
    exact canonicalMap_injective C b (congrArg Prod.fst h)
  hom_card z := (hom_card_eq z.1.1.1 z.1.1.2.2.1 z.1.2.2.2.1).le

theorem canonical_sum (C b r : ℕ) :
    (∑ z : Canonical C b,
      (Nat.card (z.2.1.1 →* Multiplicative (ZMod 4)) : ℝ)^r)=
      PhysicalOddConvolution.count (binaryMoment C) NilpotentTargetConvolution.oddCount b r := by
  rw [Fintype.sum_sigma]
  unfold PhysicalOddConvolution.count
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type]
  change (∑ P : BinaryFamily C z.val.1,
      ∑ _O : Subgroup (PermutationGroup z.val.2),
        (Nat.card (P.val →* Multiplicative (ZMod 4)) : ℝ)^r)=_
  unfold binaryMoment NilpotentTargetConvolution.oddCount
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Nat.card_eq_fintype_card (α := Subgroup (PermutationGroup z.val.2))]
  exact mul_comm _ _

theorem target_le_convolution (C b r : ℕ) : targetCount C b r≤
    PhysicalOddConvolution.count (binaryMoment C) NilpotentTargetConvolution.oddCount b r := by
  have h := (restrictionEncoding C b).homMoment_sum_le r
  simpa only [Fintype.card_unit,Nat.cast_one,one_mul,canonical_sum] using h

theorem nilpotent_moment_le {C : ℕ} (hC : 1<C) (b r : ℕ) : nilpotentCount C b r≤
    ((b+1 : ℕ)^(3*b) : ℝ) *
      PhysicalOddConvolution.count (binaryMoment C) NilpotentTargetConvolution.oddCount b r := by
  have h := (BoundedNilpotentProductReduction.encoding hC b).homMoment_sum_le r
  rw [PhysicalGridLabels.card_code] at h
  have hh := mul_le_mul_of_nonneg_left (target_le_convolution C b r)
    (Nat.cast_nonneg ((b+1)^(3*b)) : (0 : ℝ)≤((b+1)^(3*b) : ℕ))
  simpa only [Nat.cast_pow] using h.trans hh
end SymmetricSubgroupAsymptotics.MarkedC4.BoundedNilpotentTargetConvolution
