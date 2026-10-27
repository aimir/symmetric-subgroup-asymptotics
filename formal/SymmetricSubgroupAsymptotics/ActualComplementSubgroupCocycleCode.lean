import SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFrame
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! ALL actual full-image subgroups with trivial kernel intersection are
encoded relative to ONE actual member of that same family. Sections are
derived from the literal restricted quotient isomorphisms. No splitting
of the ambient extension is assumed, and optional predicates are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualComplementSubgroupCocycleCode
open TwistedMonomialCocycleFrame

variable {E Q : Type*} [Group E] [Group Q] (π : E →* Q)

abbrev Family := {L : Subgroup E // L.map π=⊤ ∧ L⊓π.ker=⊥}

def restrictedHom (L : Family π) : L.val →* Q := π.comp L.val.subtype

theorem restrictedHom_bijective (L : Family π) : Function.Bijective (restrictedHom π L) := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply inv_mul_eq_one.mp
    have hh : a.val⁻¹*b.val∈L.val⊓π.ker := by
      refine ⟨L.val.mul_mem (L.val.inv_mem a.property) b.property,?_⟩
      change π (a.val⁻¹*b.val)=1
      change π a.val=π b.val at h
      rw [map_mul,map_inv,h,inv_mul_cancel]
    rwa [L.property.2,Subgroup.mem_bot] at hh
  · intro q
    have hq : q∈L.val.map π := by rw [L.property.1]; trivial
    obtain ⟨g,hg,he⟩ := hq
    exact ⟨⟨g,hg⟩,he⟩

def restrictedEquiv (L : Family π) : L.val ≃* Q :=
  MulEquiv.ofBijective (restrictedHom π L) (restrictedHom_bijective π L)

def sectionHom (L : Family π) : Q →* E :=
  L.val.subtype.comp (restrictedEquiv π L).symm.toMonoidHom

theorem section_right_inverse (L : Family π) (q : Q) : π (sectionHom π L q)=q :=
  (restrictedEquiv π L).apply_symm_apply q

theorem section_mem (L : Family π) (q : Q) : sectionHom π L q∈L.val :=
  ((restrictedEquiv π L).symm q).property

theorem section_range (L : Family π) : (sectionHom π L).range=L.val := by
  ext g
  constructor
  · rintro ⟨q,rfl⟩
    exact section_mem π L q
  · intro hg
    refine ⟨restrictedEquiv π L ⟨g,hg⟩,?_⟩
    exact congrArg Subtype.val ((restrictedEquiv π L).symm_apply_apply ⟨g,hg⟩)

variable (L0 : Family π)

def baselineAction : Q →* MulAut π.ker :=
  (MulAut.conjNormal : E →* MulAut π.ker).comp (sectionHom π L0)

def cocycleCode (L : Family π) : Cocycle (baselineAction π L0) :=
  ⟨fun q => ⟨sectionHom π L q*(sectionHom π L0 q)⁻¹,by
    change π (sectionHom π L q*(sectionHom π L0 q)⁻¹)=1
    rw [map_mul,map_inv,section_right_inverse,section_right_inverse,mul_inv_cancel]⟩,by
    intro p q
    apply Subtype.ext
    change sectionHom π L (p*q)*(sectionHom π L0 (p*q))⁻¹=
      (sectionHom π L p*(sectionHom π L0 p)⁻¹)*
        ↑(MulAut.conjNormal (sectionHom π L0 p)
          (⟨sectionHom π L q*(sectionHom π L0 q)⁻¹,by
            change π (sectionHom π L q*(sectionHom π L0 q)⁻¹)=1
            rw [map_mul,map_inv,section_right_inverse,section_right_inverse,mul_inv_cancel]⟩ : π.ker))
    rw [MulAut.conjNormal_apply,map_mul,map_mul]
    group⟩

theorem section_recovery (L : Family π) (q : Q) :
    ((cocycleCode π L0 L).val q : E)*sectionHom π L0 q=sectionHom π L q := by
  change (sectionHom π L q*(sectionHom π L0 q)⁻¹)*sectionHom π L0 q=sectionHom π L q
  group

theorem cocycleCode_injective : Function.Injective (cocycleCode π L0) := by
  intro L M h
  have hs : sectionHom π L=sectionHom π M := by
    ext q
    have hh := congrArg (fun c : Cocycle (baselineAction π L0) => (c.val q : E)) h
    change sectionHom π L q*(sectionHom π L0 q)⁻¹=
      sectionHom π M q*(sectionHom π L0 q)⁻¹ at hh
    exact mul_right_cancel hh
  apply Subtype.ext
  exact (section_range π L).symm.trans ((congrArg MonoidHom.range hs).trans (section_range π M))

def filteredCode (P : Cocycle (baselineAction π L0) → Prop)
    (L : {L : Family π // P (cocycleCode π L0 L)}) :
    {c : Cocycle (baselineAction π L0) // P c} :=
  ⟨cocycleCode π L0 L.val,L.property⟩

theorem filteredCode_injective (P : Cocycle (baselineAction π L0) → Prop) :
    Function.Injective (filteredCode π L0 P) := by
  intro L M h
  exact Subtype.ext (cocycleCode_injective π L0 (congrArg Subtype.val h))

theorem card_filtered_family_le (P : Cocycle (baselineAction π L0) → Prop)
    [Finite {c : Cocycle (baselineAction π L0) // P c}] :
    Nat.card {L : Family π // P (cocycleCode π L0 L)}≤
      Nat.card {c : Cocycle (baselineAction π L0) // P c} :=
  Nat.card_le_card_of_injective (filteredCode π L0 P) (filteredCode_injective π L0 P)

theorem empty_or_actual_baseline :
    IsEmpty (Family π) ∨ ∃ L0 : Family π,Function.Injective (cocycleCode π L0) := by
  by_cases h : Nonempty (Family π)
  · obtain ⟨L0⟩ := h
    exact Or.inr ⟨L0,cocycleCode_injective π L0⟩
  · exact Or.inl ⟨fun L => h ⟨L⟩⟩

theorem card_family_zero_or_le_actual_baseline [Finite E] [Finite Q] :
    Nat.card (Family π)=0 ∨ ∃ L0 : Family π,
      Nat.card (Family π)≤Nat.card (Cocycle (baselineAction π L0)) := by
  rcases empty_or_actual_baseline π with h | ⟨L0,hi⟩
  · letI := h
    exact Or.inl Nat.card_of_isEmpty
  · exact Or.inr ⟨L0,Nat.card_le_card_of_injective (cocycleCode π L0) hi⟩

end SymmetricSubgroupAsymptotics.ActualComplementSubgroupCocycleCode
