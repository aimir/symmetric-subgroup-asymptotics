import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Every literal simple PSL2 over a four-element field is identified
with A5 through its actual Borel-coset action. The checked two-cell
geometry gives five points and order sixty. The actual faithful image
therefore has index two in S5, where the existing alternating-group
index-two recognition applies. No subgroup census or small-field
isomorphism premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFourAlternatingEquiv
open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry
variable {F : Type} [Field F] [Finite F]

theorem field_card_four_char_two (hcard : Nat.card F=4) : ringChar F=2 := by
  letI : Fintype F := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  have hc : Fintype.card F=4 := by simpa only [Nat.card_eq_fintype_card] using hcard
  rw [hc]

theorem projective_card_eq_sixty (hcard : Nat.card F=4) :
    Nat.card (PSL (F:=F))=60 := by
  have hchar := field_card_four_char_two hcard
  rw [projective_card_eq_torus_mul,CFSGPSLTwoEvenOuterBound.pairTorus_card_eq_units hchar,
    Nat.card_units,hcard]

def equivAlternatingFive [IsSimpleGroup (PSL (F:=F))] (hcard : Nat.card F=4) :
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
  let e : Points (F:=F) ≃ Fin 5 := Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card,points_card,hcard])
  let f : PSL (F:=F) →* Equiv.Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL (F:=F)) (Points (F:=F)))
  have hf : Function.Injective f := e.permCongrHom.injective.comp ha
  let E : PSL (F:=F) ≃* f.range := MonoidHom.ofInjective hf
  have hR : Nat.card f.range=60 :=
    (Nat.card_congr E.symm.toEquiv).trans (projective_card_eq_sixty hcard)
  have hperm : Nat.card (Equiv.Perm (Fin 5))=120 := by
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have hi : f.range.index=2 := by
    have hc := f.range.card_mul_index
    rw [hR,hperm] at hc
    omega
  exact E.trans (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFourAlternatingEquiv
