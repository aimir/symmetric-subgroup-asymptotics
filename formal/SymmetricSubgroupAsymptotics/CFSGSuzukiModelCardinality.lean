import SymmetricSubgroupAsymptotics.CFSGSuzukiOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGRankOneTwoCellCardinality
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentProductCoordinates
import SymmetricSubgroupAsymptotics.CFSGSuzukiBruhatDecomposition
import SymmetricSubgroupAsymptotics.CFSGSuzukiGoodSylow

/-! The order of the pinned actual Suzuki matrix model, derived from
its original Borel and opposite-U Bruhat cells. No Suzuki order formula
or order-based group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality
open CFSGSuzukiUnipotent CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow
open CFSGSuzukiOppositeIntersection

theorem modelBorel_inf_opposite (m : ℕ) :
    modelBorel m ⊓ (modelUnipotent m).map
      (MulAut.conj (modelWeyl m)).toMonoidHom=⊥ := by
  apply bot_unique
  intro g hg
  have ha : g.val∈borelEnvelope m ⊓ (unipotentSubgroup m).map
      (MulAut.conj (CFSGSuzukiTorus.weylElement m)).toMonoidHom := by
    refine ⟨hg.1,?_⟩
    obtain ⟨u,hu,he⟩ := hg.2
    refine ⟨u.val,hu,?_⟩
    exact congrArg (fun x : ActualGroup m => x.val) he
  rw [borel_inf_opposite_unipotent] at ha
  change g.val=1 at ha
  change g=1
  exact Subtype.ext ha

theorem actual_model_two_cells (m : ℕ) (g : ActualGroup m) :
    g∈modelBorel m ∨ ∃ (b : modelBorel m) (u : modelUnipotent m),
      g=b.val*modelWeyl m*u.val := by
  rcases model_two_cells m g.val g.property with hb | ⟨b,hb,u,hu,he⟩
  · exact Or.inl hb
  · refine Or.inr ⟨⟨⟨b,borelEnvelope_le_model m hb⟩,hb⟩,
      ⟨⟨u,unipotentSubgroup_le_model m hu⟩,hu⟩,?_⟩
    exact Subtype.ext he

theorem model_card (m : ℕ) :
    Nat.card (CFSG.Models.Suzuki m)=
      Nat.card (CFSGSuzukiFieldParameters.Field m)^2*
        (Nat.card (CFSGSuzukiFieldParameters.Field m)-1)*
          (Nat.card (CFSGSuzukiFieldParameters.Field m)^2+1) := by
  have hUB : modelUnipotent m≤modelBorel m := fun _ hx =>
    unipotentSubgroup_le_borelEnvelope m hx
  have hw : modelWeyl m∉modelBorel m := fun h => weyl_not_mem_borel m h
  have hc := CFSGRankOneTwoCellCardinality.card_eq
    (modelBorel m) (modelUnipotent m) (modelWeyl m) hUB hw
    (modelBorel_inf_opposite m) (actual_model_two_cells m)
  have hB : Nat.card (modelBorel m)=Nat.card (borelEnvelope m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (borelEnvelope_le_model m)).toEquiv
  have hU : Nat.card (modelUnipotent m)=Nat.card (unipotentSubgroup m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (unipotentSubgroup_le_model m)).toEquiv
  rw [hB,hU,borelEnvelope_card,unipotentSubgroup_card,Nat.card_units] at hc
  simpa only [Nat.add_comm] using hc

theorem model_even_card (m : ℕ) : Even (Nat.card (CFSG.Models.Suzuki m)) := by
  apply even_iff_two_dvd.mpr
  rw [model_card]
  have hq : 2∣Nat.card (CFSGSuzukiFieldParameters.Field m) := by
    rw [CFSGSuzukiFieldParameters.field_card]
    exact dvd_pow_self 2 (by omega)
  have hs : 2∣Nat.card (CFSGSuzukiFieldParameters.Field m)^2 :=
    hq.trans (dvd_pow_self _ (by decide : 2≠0))
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hs _) _

end SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality
