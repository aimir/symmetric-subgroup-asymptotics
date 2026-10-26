import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualRepresentation
import Mathlib.Tactic.FinCases

/-! A separate literal recovery certificate proves the representation is
onto the SAME original generated subgroup. Inherited pinned simplicity
then upgrades it to an equivalence and gives exact order7920. The primary
selected-word diagnostic is data only; the whole11-point equality below
supplies the recovery obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualEquivalence
open CFSG.Certificates.Mathieu11 CFSGMathieuElevenPresentationWords
open CFSGMathieuElevenActualRepresentation

def recoverAWord {G : Type*} [Group G] (u v : G) : G :=
  u*v⁻¹*u*v⁻¹*u*v^2*u*v*u*v*u*v*u*v⁻¹*u

theorem recoverAWord_eq_originalA : recoverAWord x y=originalA := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide +kernel

theorem representation_surjective : Function.Surjective representation := by
  let R := representation.range
  have ha : originalA∈R := by
    refine ⟨recoverAWord (PresentedGroup.of (0 : Fin 2))
      (PresentedGroup.of (1 : Fin 2)),?_⟩
    simpa only [recoverAWord,map_mul,map_inv,map_pow,representation_of_zero,representation_of_one]
      using recoverAWord_eq_originalA
  have hb : originalB∈R := ⟨PresentedGroup.of (1 : Fin 2),representation_of_one⟩
  have hmap : M11Subgroup≤R.map M11Subgroup.subtype := by
    change Subgroup.closure ({m11a,m11b} : Set _)≤R.map M11Subgroup.subtype
    apply (Subgroup.closure_le (R.map M11Subgroup.subtype)).mpr
    rintro z (rfl|rfl)
    · exact ⟨originalA,ha,rfl⟩
    · exact ⟨originalB,hb,rfl⟩
  intro g
  obtain ⟨z,hz,he⟩ := hmap g.property
  have heq : z=g := Subtype.ext he
  exact heq ▸ hz

def actualEquivalence [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    CFSG.Models.Presentations.M11.Model ≃* M11 :=
  MulEquiv.ofBijective representation ⟨representation_injective,representation_surjective⟩

theorem card [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Nat.card CFSG.Models.Presentations.M11.Model=7920 :=
  (Nat.card_congr actualEquivalence.toEquiv).trans M11Cardinality.card_M11

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualEquivalence
