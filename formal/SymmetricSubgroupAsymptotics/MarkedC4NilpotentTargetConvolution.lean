import SymmetricSubgroupAsymptotics.MarkedC4SupportedPermutationRestriction
import SymmetricSubgroupAsymptotics.MarkedC4PhysicalOddConvolution

/-! Canonical physical target indices and their exact finite convolution.
Supported permutation images are restricted by actual group equivalences;
odd subgroup configurations remain in the target summation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentTargetConvolution
open NilpotentPhysicalProductEncoding SupportedPermutationRestriction

abbrev BinarySubgroups (a : ℕ) := {P : Subgroup (PermutationGroup a) // IsPGroup 2 P}
def binaryMoment (a r : ℕ) : ℝ :=
  ∑ P : BinarySubgroups a, (Nat.card (P.1 →* Multiplicative (ZMod 4)) : ℝ)^r
def oddCount (d : ℕ) : ℝ := Nat.card (Subgroup (PermutationGroup d))
abbrev Canonical (b : ℕ) := Σ z : PhysicalOddConvolution.degrees b,
  BinarySubgroups z.1.1 × Subgroup (PermutationGroup z.1.2)

def canonicalMap {b : ℕ} (z : Target b) : Canonical b := by
  let a := z.1.1
  let d := z.1.2.1
  let P := z.1.2.2.1
  let O := z.1.2.2.2
  have hdeg : (a.val,d.val)∈PhysicalOddConvolution.degrees b := by
    simp only [PhysicalOddConvolution.degrees,Finset.mem_filter,Finset.mem_product,
      Finset.mem_range]
    exact ⟨⟨a.isLt,d.isLt⟩,z.2.1⟩
  have hP : IsPGroup 2 (restrict a P) :=
    z.2.2.1.of_injective (groupEquiv a P z.2.2.2.1).toMonoidHom
      (groupEquiv a P z.2.2.2.1).injective
  exact ⟨⟨(a.val,d.val),hdeg⟩,(⟨restrict a P,hP⟩,restrict d O)⟩

theorem canonicalMap_injective (b : ℕ) : Function.Injective (canonicalMap (b := b)) := by
  rintro ⟨⟨a,d,P,O⟩,hz⟩ ⟨⟨a',d',P',O'⟩,hw⟩ h
  have hdeg := congrArg (fun w : Canonical b => w.1.1) h
  have ha : a=a' := Fin.ext (congrArg Prod.fst hdeg)
  have hd : d=d' := Fin.ext (congrArg Prod.snd hdeg)
  cases ha
  cases hd
  dsimp [canonicalMap] at h
  have hpairs := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hp : restrict a P=restrict a P' := congrArg (fun w => w.1.1) hpairs
  have ho : restrict d O=restrict d O' := congrArg Prod.snd hpairs
  have hP : P=P' := by
    calc
      P = (restrict a P).map (extension a) := (recover a P hz.2.2.1).symm
      _ = (restrict a P').map (extension a) := congrArg (Subgroup.map (extension a)) hp
      _ = P' := recover a P' hw.2.2.1
  have hO : O=O' := by
    calc
      O = (restrict d O).map (extension d) := (recover d O hz.2.2.2.1).symm
      _ = (restrict d O').map (extension d) := congrArg (Subgroup.map (extension d)) ho
      _ = O' := recover d O' hw.2.2.2.1
  cases hP
  cases hO
  rfl

/-- Restriction preserves the exact marked Hom count, and its injective
finite index map has no auxiliary multiplicity. -/
def restrictionEncoding (b : ℕ) :
    ProductEncoding (Target b) (Canonical b) Unit
      (fun z => z.1.2.2.1) (fun z => z.2.1.1) where
  code z := (canonicalMap z,())
  code_injective := by
    intro z w h
    exact canonicalMap_injective b (congrArg Prod.fst h)
  hom_card z := (hom_card_eq z.1.1 z.1.2.2.1 z.2.2.2.1).le

/-- Exact physical-degree convolution, including odd choices as index
multiplicities and including zero degrees and either parity. -/
theorem canonical_sum (b r : ℕ) :
    (∑ z : Canonical b,
      (Nat.card (z.2.1.1 →* Multiplicative (ZMod 4)) : ℝ)^r)=
      PhysicalOddConvolution.count binaryMoment oddCount b r := by
  rw [Fintype.sum_sigma]
  unfold PhysicalOddConvolution.count
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type]
  change (∑ P : BinarySubgroups z.val.1,
      ∑ _O : Subgroup (PermutationGroup z.val.2),
        (Nat.card (P.val →* Multiplicative (ZMod 4)) : ℝ)^r)=_
  unfold binaryMoment oddCount
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Nat.card_eq_fintype_card (α := Subgroup (PermutationGroup z.val.2))]
  exact mul_comm _ _

theorem target_sum_le (b r : ℕ) :
    (∑ z : Target b,
      (Nat.card (z.1.2.2.1 →* Multiplicative (ZMod 4)) : ℝ)^r)≤
      PhysicalOddConvolution.count binaryMoment oddCount b r := by
  have h := (restrictionEncoding b).homMoment_sum_le r
  simpa only [Fintype.card_unit,Nat.cast_one,one_mul,canonical_sum] using h

/-- Actual nilpotent sources now map to the degree-sensitive convolution;
only the explicit finite original-label alphabet remains as overhead. -/
theorem nilpotent_moment_le (b r : ℕ) :
    (∑ K : Source b, (Nat.card (K.1 →* Multiplicative (ZMod 4)) : ℝ)^r)≤
      ((b+1 : ℕ)^(3*b) : ℝ) *
        PhysicalOddConvolution.count binaryMoment oddCount b r :=
  (NilpotentPhysicalProductEncoding.moment_le b r).trans
    (mul_le_mul_of_nonneg_left (target_sum_le b r) (by positivity))
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentTargetConvolution
