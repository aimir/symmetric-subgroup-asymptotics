import SymmetricSubgroupAsymptotics.CFSGPSLTwoOddTorusCardinality
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixRecognition
import Mathlib.Data.Fintype.Units

/-! The literal simple PSL2 over any five-element field is A5. Its
actual Borel-coset action has six points and its actual order is sixty.
Simplicity forces this faithful permutation image into A6. The existing
order-sixty subgroup recognition inside A6 then gives A5 through actual
coset actions, without a subgroup census or field-model substitution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFiveAlternatingEquiv

theorem simple_image_le_alternating {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {n : ℕ} (f : G →* Equiv.Perm (Fin n)) (hG : 2<Nat.card G) :
    f.range≤alternatingGroup (Fin n) := by
  let s : G →* ℤˣ := Equiv.Perm.sign.comp f
  have hk : s.ker=⊤ := by
    rcases (inferInstance : s.ker.Normal).eq_bot_or_eq_top with hb | ht
    · have hi : Function.Injective s := (MonoidHom.ker_eq_bot_iff s).mp hb
      have hc := Nat.card_le_card_of_injective s hi
      have hu : Nat.card ℤˣ=2 := by
        rw [Nat.card_eq_fintype_card,Fintype.card_units_int]
      rw [hu] at hc
      omega
    · exact ht
  rintro g ⟨x,rfl⟩
  apply Equiv.Perm.mem_alternatingGroup.mpr
  have hx : x∈s.ker := by rw [hk]; trivial
  exact hx

open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry
variable {F : Type} [Field F] [Finite F]

theorem field_card_five_char_ne_two (hcard : Nat.card F=5) : ringChar F≠2 := by
  intro hc
  letI : Fintype F := Fintype.ofFinite F
  have hf : Fintype.card F=5 := by simpa only [Nat.card_eq_fintype_card] using hcard
  have hh := FiniteField.even_card_of_char_two hc
  simpa [hf] using hh

theorem projective_card_eq_sixty (hcard : Nat.card F=5) :
    Nat.card (PSL (F:=F))=60 := by
  have hc := CFSGPSLTwoOddTorusCardinality.twice_projective_card_eq
    (field_card_five_char_ne_two hcard)
  rw [hcard] at hc
  omega

def equivAlternatingFive [IsSimpleGroup (PSL (F:=F))] (hcard : Nat.card F=5) :
    PSL (F:=F) ≃* alternatingGroup (Fin 5) := by
  letI : Fintype (Points (F:=F)) := Fintype.ofFinite _
  have hB : projectiveBorel (F:=F)≠⊤ := by
    intro he
    apply projectiveWeyl_not_mem_borel (F:=F)
    rw [he]
    trivial
  have hcore : (projectiveBorel (F:=F)).normalCore=⊥ := by
    rcases (inferInstance : (projectiveBorel (F:=F)).normalCore.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact False.elim (hB (top_unique (ht ▸ (projectiveBorel (F:=F)).normalCore_le)))
  have ha : Function.Injective (MulAction.toPermHom (PSL (F:=F)) (Points (F:=F))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← Subgroup.normalCore_eq_ker,hcore]
  let e : Points (F:=F) ≃ Fin 6 := Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card,points_card,hcard])
  let f : PSL (F:=F) →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL (F:=F)) (Points (F:=F)))
  have hf : Function.Injective f := e.permCongrHom.injective.comp ha
  let E : PSL (F:=F) ≃* f.range := MonoidHom.ofInjective hf
  have hR : Nat.card f.range=60 :=
    (Nat.card_congr E.symm.toEquiv).trans (projective_card_eq_sixty hcard)
  have hle : f.range≤alternatingGroup (Fin 6) :=
    simple_image_le_alternating f (by rw [projective_card_eq_sixty hcard]; decide)
  let H : Subgroup (alternatingGroup (Fin 6)) := f.range.subgroupOf (alternatingGroup (Fin 6))
  let EA : f.range ≃* H := (Subgroup.subgroupOfEquivOfLe hle).symm
  have hH : Nat.card H=60 := (Nat.card_congr EA.symm.toEquiv).trans hR
  exact E.trans (EA.trans (PrimitiveDegreeSixRecognition.alternatingSubgroupEquiv H hH))

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFiveAlternatingEquiv
