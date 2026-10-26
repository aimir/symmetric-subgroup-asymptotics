import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualRepresentation

/-! Certified recovery of all three original generators makes the actual
representation surjective. Together with injectivity from inherited pinned
simplicity, this gives an equivalence and exact pinned order95040. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveActualRepresentation CFSGMathieuTwelveRecoveryWords

theorem representation_surjective : Function.Surjective representation := by
  let R := representation.range
  have ha : originalA ∈ R := by
    refine ⟨recoverAWord (PresentedGroup.of (0 : Fin 2))
      (PresentedGroup.of (1 : Fin 2)), ?_⟩
    simpa only [recoverAWord, map_mul, map_inv, representation_of_zero, representation_of_one]
      using recoverAWord_eq_originalA
  have hb : originalB ∈ R := by
    refine ⟨recoverBWord (PresentedGroup.of (0 : Fin 2))
      (PresentedGroup.of (1 : Fin 2)), ?_⟩
    simpa only [recoverBWord, map_mul, map_inv, representation_of_zero, representation_of_one]
      using recoverBWord_eq_originalB
  have hc : originalC ∈ R := by
    refine ⟨recoverCWord (PresentedGroup.of (0 : Fin 2))
      (PresentedGroup.of (1 : Fin 2)), ?_⟩
    simpa only [recoverCWord, map_mul, map_inv, representation_of_zero, representation_of_one]
      using recoverCWord_eq_originalC
  have hmap : M12Subgroup ≤ R.map M12Subgroup.subtype := by
    change Subgroup.closure ({m12a, m12b, m12c} : Set _) ≤ R.map M12Subgroup.subtype
    apply (Subgroup.closure_le (R.map M12Subgroup.subtype)).mpr
    rintro z (rfl | rfl | rfl)
    · exact ⟨originalA, ha, rfl⟩
    · exact ⟨originalB, hb, rfl⟩
    · exact ⟨originalC, hc, rfl⟩
  intro g
  obtain ⟨z, hz, he⟩ := hmap g.property
  have heq : z = g := Subtype.ext he
  exact heq ▸ hz

def actualEquivalence [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    CFSG.Models.Presentations.M12.Model ≃* M12 :=
  MulEquiv.ofBijective representation ⟨representation_injective, representation_surjective⟩

theorem card [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card CFSG.Models.Presentations.M12.Model = 95040 :=
  (Nat.card_congr actualEquivalence.toEquiv).trans M12Cardinality.card_M12

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence
