import SymmetricSubgroupAsymptotics.MarkedC4BoundedNilpotentTargetConvolution

/-! Refine the existing actual binary/odd physical encoding. The odd
coordinate retains NILPOTENCE, odd order, and the SAME original orbit
cutoff. It is never enlarged to all subgroups of a symmetric group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNilpotentBinaryOddConvolution
open MarkedC4 OrbitCutoffFamilies SupportedPermutationRestriction

abbrev OddFamily (C d : ℕ) := {O : Subgroup (PermutationGroup d) //
  Group.IsNilpotent O ∧ ¬2 ∣ Nat.card O ∧ OrbitCutoff C O}
abbrev Canonical (C b : ℕ) := Σ z : PhysicalOddConvolution.degrees b,
  BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1 × OddFamily C z.1.2

def forget {C b : ℕ} (z : Canonical C b) : BoundedNilpotentTargetConvolution.Canonical C b :=
  ⟨z.1,z.2.1,z.2.2.val⟩

variable {C b : ℕ} (hC : 1<C) (K : NilpotentFamily C b)
local instance sourceNilpotent : Group.IsNilpotent K.val := K.property.1

/-- Both physical images are the original constructed ranges. -/
def actualCanonical : Canonical C b := by
  let z := BoundedNilpotentProductReduction.targetCode hC K
  let c := BoundedNilpotentTargetConvolution.canonicalMap z
  let d := z.val.val.2.1
  let O := z.val.val.2.2.2
  have hO : NilpotentPhysicalProductEncoding.supported d.val O := z.val.property.2.2.2.1
  have hn : Group.IsNilpotent O := by
    change Group.IsNilpotent (NilpotentLabelledActions.odd K.val).range
    exact Group.nilpotent_of_surjective (NilpotentLabelledActions.odd K.val).rangeRestrict
      (NilpotentLabelledActions.odd K.val).rangeRestrict_surjective
  have hnr : Group.IsNilpotent (restrict d O) := by
    letI := hn
    exact Group.nilpotent_of_mulEquiv (groupEquiv d O hO).symm
  have hcard : Nat.card (restrict d O)=Nat.card O := Nat.card_congr (groupEquiv d O hO).toEquiv
  have hodd : ¬2 ∣ Nat.card (restrict d O) := by
    rw [hcard]
    have hc : Nat.Coprime (Nat.card O) 2 :=
      Nat.Coprime.of_dvd_right (by decide : 2∣4) z.val.property.2.2.2.2
    exact Nat.prime_two.coprime_iff_not_dvd.mp hc.symm
  have hcut : OrbitCutoff C (restrict d O) := SupportedRestrictionCutoff.cutoff d O hO z.property.2
  exact ⟨c.1,c.2.1,⟨c.2.2,hnr,hodd,hcut⟩⟩

theorem forget_actualCanonical : forget (actualCanonical hC K)=
    BoundedNilpotentTargetConvolution.canonicalMap
      (BoundedNilpotentProductReduction.targetCode hC K) := rfl

def code : NilpotentFamily C b → Canonical C b × PhysicalGridLabels.Code b :=
  fun K => (actualCanonical hC K,NilpotentOriginalLabels.code K.val)

theorem code_injective : Function.Injective (code (b := b) hC) := by
  intro K L he
  apply (BoundedNilpotentProductReduction.encoding hC b).code_injective
  apply Prod.ext
  · apply BoundedNilpotentTargetConvolution.canonicalMap_injective C b
    have hh := congrArg (fun z : Canonical C b × PhysicalGridLabels.Code b => forget z.1) he
    simpa only [code,forget_actualCanonical] using hh
  · change NilpotentOriginalLabels.code K.val=NilpotentOriginalLabels.code L.val
    exact congrArg (fun z : Canonical C b × PhysicalGridLabels.Code b => z.2) he

theorem canonical_card_eq : Nat.card (Canonical C b)=∑ z : PhysicalOddConvolution.degrees b,
      Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1)*
        Nat.card (OddFamily C z.1.2) := by
  rw [Canonical,Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro z _
  exact Nat.card_prod _ _

theorem label_card_eq : Nat.card (PhysicalGridLabels.Code b)=(b+1)^(3*b) := by
  rw [Nat.card_eq_fintype_card,PhysicalGridLabels.card_code]

include hC

/-- Keep cardinal monotonicity separate from the literal sum calculation;
the latter never needs to unfold the original-group encoding. -/
theorem cardinal_le_code_target : Nat.card (NilpotentFamily C b) ≤
    Nat.card (Canonical C b) * Nat.card (PhysicalGridLabels.Code b) := by
  let f : NilpotentFamily C b → Canonical C b × PhysicalGridLabels.Code b := code hC
  have hf : Function.Injective f := code_injective hC
  have h : Nat.card (NilpotentFamily C b) ≤
      Nat.card (Canonical C b × PhysicalGridLabels.Code b) :=
    Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod] using h

/-- The finite physical convolution retains both original prime sectors,
with only the already-proved original-label alphabet as overhead. -/
theorem nilpotent_card_le : Nat.card (NilpotentFamily C b) ≤
    (b+1)^(3*b) * ∑ z : PhysicalOddConvolution.degrees b,
      Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1)*
        Nat.card (OddFamily C z.1.2) := by
  have h : Nat.card (NilpotentFamily C b) ≤
      Nat.card (Canonical C b) * Nat.card (PhysicalGridLabels.Code b) :=
    cardinal_le_code_target (C := C) (b := b) hC
  have ht : Nat.card (Canonical C b)=∑ z : PhysicalOddConvolution.degrees b,
      Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1)*
        Nat.card (OddFamily C z.1.2) := canonical_card_eq (C := C) (b := b)
  have hc : Nat.card (PhysicalGridLabels.Code b)=(b+1)^(3*b) := label_card_eq (b := b)
  apply h.trans_eq
  rw [ht,hc]
  exact Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGNilpotentBinaryOddConvolution
