import SymmetricSubgroupAsymptotics.BinaryCarrierMenuSlots

/-!
# Extracting exact normal axes from a full original-action word

Every coordinate axis of a full subgroup of a finite product is normal in
the corresponding coordinate group.  Quotienting by those axes therefore
places the subgroup canonically in `CarrierTransportSource`.  This is the
source-side bridge for original factors that remain unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierSourceExtraction

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryCarrierMenuSlots

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {U : ι → Type*} [∀ i, Group (U i)]

/-- Full projection makes the literal embedded coordinate axis normal. -/
theorem carrierAxis_normal (H : Subgroup (∀ i, U i))
    (hH : CarrierProductFull H) (i : ι) : (carrierAxis H i).Normal where
  conj_mem n hn u := by
    change MonoidHom.mulSingle U i (u*n*u⁻¹) ∈ H
    change MonoidHom.mulSingle U i n ∈ H at hn
    obtain ⟨h,hh⟩ := hH i u
    have hc := H.mul_mem (H.mul_mem h.2 hn) (H.inv_mem h.2)
    convert hc using 1
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.mul_apply,Pi.inv_apply,MonoidHom.mulSingle_apply,
        Pi.mulSingle_eq_same]
      rw [hh]
    · simp only [Pi.mul_apply,Pi.inv_apply,MonoidHom.mulSingle_apply,
        Pi.mulSingle_eq_of_ne hji, mul_one, mul_inv_cancel]

section LiteralActions

variable (color : ι → MixtureKind)
  (N : ∀ i, Subgroup (mixtureAction (color i)))
  [∀ i, (N i).Normal]

/-- One quotient identity slot for every literal original action. -/
def quotientIdentityWord
    (hN : ∀ i, (N i).Normal) (i : ι) : Slot := by
  letI : (N i).Normal := hN i
  exact quotientIdentitySlot (color i) (N i)

/-- The literal unmarked stratum with prescribed coordinate axes.  Its
elements are the original full subgroups themselves; the normal axes occur
only in the predicate defining the stratum. -/
abbrev ExactAxisFamily :=
  {H : Subgroup (∀ i, mixtureAction (color i)) //
    CarrierProductFull H ∧ ∀ i, carrierAxis H i = N i}

/-- Quotienting by the prescribed literal axes merely repackages the same
unmarked source stratum as the reversible-transport source family. -/
def exactAxisFamilyEquivSource :
    ExactAxisFamily color N ≃
      CarrierTransportSource
        (alphas (quotientIdentityWord color N (fun i => inferInstance))) where
  toFun H := by
    refine ⟨H.1,H.2.1,?_⟩
    intro i
    letI : (N i).Normal := inferInstance
    exact (H.2.2 i).trans (quotientIdentitySlot_alpha_ker (color i) (N i)).symm
  invFun H := by
    refine ⟨H.1,H.2.1,?_⟩
    intro i
    letI : (N i).Normal := inferInstance
    exact (H.2.2 i).trans (quotientIdentitySlot_alpha_ker (color i) (N i))
  left_inv H := Subtype.ext rfl
  right_inv H := Subtype.ext rfl

/-- Every fixed normal-axis word with at least one noncritical action is
absorbed by the exact completed mixture. -/
theorem quotient_identity_word_card_le_mixture
    (hnoncritical : ∃ i, ∃ t, color i = .inr t) :
    Nat.card (CarrierTransportSource
      (alphas (quotientIdentityWord color N (fun i => inferInstance)))) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter
          (cells (quotientIdentityWord color N (fun i => inferInstance)))
          (colors (quotientIdentityWord color N (fun i => inferInstance))))) := by
  apply slot_source_card_le_mixture
  obtain ⟨i,t,hi⟩ := hnoncritical
  change ∃ c : Σ _ : ι, Fin 1, ∃ t, color c.1 = .inr t
  exact ⟨⟨i,0⟩,t,hi⟩

/-- Counting form of the identity-word theorem stated directly for the
original full subgroups with their exact literal normal axes.  No quotient
map or source record is added to the counted object. -/
theorem exact_axis_family_card_le_mixture
    (hnoncritical : ∃ i, ∃ t, color i = .inr t) :
    Nat.card (ExactAxisFamily color N) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter
          (cells (quotientIdentityWord color N (fun i => inferInstance)))
          (colors (quotientIdentityWord color N (fun i => inferInstance))))) := by
  rw [Nat.card_congr (exactAxisFamilyEquivSource color N)]
  exact quotient_identity_word_card_le_mixture color N hnoncritical

variable (H : Subgroup (∀ i, mixtureAction (color i)))
  (hH : CarrierProductFull H)

/-- A full subgroup, with no extra chosen data, is a source record for the
literal quotient maps by its own exact axes. -/
def canonicalIdentitySource :
    CarrierTransportSource
      (alphas (quotientIdentityWord color (fun i => carrierAxis H i)
        (fun i => carrierAxis_normal H hH i))) := by
  refine ⟨H,hH,?_⟩
  intro i
  letI : (carrierAxis H i).Normal := carrierAxis_normal H hH i
  exact (quotientIdentitySlot_alpha_ker (color i) (carrierAxis H i)).symm

end LiteralActions

end SymmetricSubgroupAsymptotics.BinaryCarrierSourceExtraction
