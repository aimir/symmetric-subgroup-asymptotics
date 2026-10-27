import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFixedPointFreeCentralizerBound
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionCentralizerCard
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYMaskFullWhitelist
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveElevenConjugacyClasses
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCycleSeedClassBounds
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerUpperBounds

/-! Fifteen separated actual original-M12 classes exhaust order95040.
Only proved centralizer UPPER bounds are used. Their class-size lower
bounds sum to the whole order, forcing coverage and exactness. No advisory
class table, preservation-to-membership converse, or class-count premise.
The pinned model is reached only through its checked actual equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualClassCount
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveRecoveredPairRelations
open CFSGMathieuTwelveCycleSeedClassBounds

private def baseRepresentative (i : Fin 6) : M12 :=
  match i.val with
  | 0 => 1
  | 1 => originalC
  | 2 => x
  | 3 => y
  | 4 => firstElement
  | _ => firstElement ^ 2

def representative (i : Fin 15) : M12 :=
  if h : i.val < 6 then baseRepresentative ⟨i.val,h⟩
  else cycleRepresentative ⟨i.val-6,by omega⟩

def centralizerCeiling (i : Fin 15) : ℕ :=
  if h : i.val < 6 then (![95040,240,192,36,11,11] : Fin 6 → ℕ) ⟨i.val,h⟩
  else cycleCeiling ⟨i.val-6,by omega⟩

private def baseProfile (i : Fin 6) : Multiset ℕ :=
  match i.val with
  | 0 => 0
  | 1 => Multiset.replicate 6 2
  | 2 => Multiset.replicate 4 2
  | 3 => Multiset.replicate 4 3
  | _ => {11}

def profile (i : Fin 15) : Multiset ℕ :=
  if h : i.val < 6 then baseProfile ⟨i.val,h⟩
  else cycleProfile ⟨i.val-6,by omega⟩

private theorem x_cycleType : x.val.cycleType = Multiset.replicate 4 2 := by
  rw [x_coe_eq]
  decide +kernel

theorem representative_cycleType (i : Fin 15) :
    (representative i).val.cycleType = profile i := by
  fin_cases i
  · exact Equiv.Perm.cycleType_one
  · exact CFSGMathieuTwelveFixedPointFreeInvolutionChart.originalC_cycleType
  · exact x_cycleType
  · exact y_cycleType
  · exact CFSGMathieuTwelveOuterBudgetOfFixedCapacity.firstElement_cycleType
  · exact CFSGMathieuTwelveElevenConjugacyClasses.square_cycleType
  · exact cycleRepresentative_cycleType 0
  · exact cycleRepresentative_cycleType 1
  · exact cycleRepresentative_cycleType 2
  · exact cycleRepresentative_cycleType 3
  · exact cycleRepresentative_cycleType 4
  · exact cycleRepresentative_cycleType 5
  · exact cycleRepresentative_cycleType 6
  · exact cycleRepresentative_cycleType 7
  · exact cycleRepresentative_cycleType 8

private theorem profile_eq_cases (i j : Fin 15) (h : profile i = profile j) :
    i = j ∨ (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  revert i j
  decide +kernel

theorem representatives_separated (i j : Fin 15)
    (h : IsConj (representative i) (representative j)) : i = j := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have hp : IsConj (representative i).val (representative j).val :=
    isConj_iff.mpr ⟨g.val,congrArg (fun z : M12 => z.val) hg⟩
  have ht := Equiv.Perm.isConj_iff_cycleType_eq.mp hp
  rw [representative_cycleType,representative_cycleType] at ht
  rcases profile_eq_cases i j ht with he | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact he
  · exact (CFSGMathieuTwelveElevenConjugacyClasses.not_isConj_first_square h).elim
  · exact (CFSGMathieuTwelveElevenConjugacyClasses.not_isConj_first_square h.symm).elim

private theorem identity_centralizer_le :
    Nat.card (Subgroup.centralizer ({(1 : M12)} : Set M12)) ≤ 95040 := by
  exact (Nat.card_le_card_of_injective
    (fun g : Subgroup.centralizer ({(1 : M12)} : Set M12) => g.val)
    Subtype.val_injective).trans_eq M12Cardinality.card_M12

theorem centralizer_bounds (i : Fin 15) :
    Nat.card (Subgroup.centralizer ({representative i} : Set M12)) ≤ centralizerCeiling i := by
  fin_cases i
  · exact identity_centralizer_le
  · exact CFSGMathieuTwelveFixedPointFreeCentralizerBound.originalC_centralizer_card_le_twoForty
  · exact CFSGMathieuTwelveSelectedInvolutionCentralizerCard.original_x_centralizer_card.le
  · exact CFSGMathieuTwelveYMaskFullWhitelist.original_y_centralizer_card_le_thirtySix
  · exact CFSGMathieuTwelveElevenConjugacyClasses.first_centralizer_card.le
  · exact CFSGMathieuTwelveElevenConjugacyClasses.square_centralizer_card.le
  · exact nine_centralizer_bounds 0
  · exact nine_centralizer_bounds 1
  · exact nine_centralizer_bounds 2
  · exact nine_centralizer_bounds 3
  · exact nine_centralizer_bounds 4
  · exact nine_centralizer_bounds 5
  · exact nine_centralizer_bounds 6
  · exact nine_centralizer_bounds 7
  · exact nine_centralizer_bounds 8

theorem class_quotient_sum :
    (∑ i : Fin 15, Nat.card M12 / centralizerCeiling i) = Nat.card M12 := by
  simp only [M12Cardinality.card_M12]
  decide +kernel

def originalCardinalCover : FiniteConjugacyCentralizerCardinalCover representative :=
  FiniteConjugacyCentralizerUpperBounds.toCardinalCover representative
    representatives_separated centralizerCeiling centralizer_bounds class_quotient_sum

theorem original_centralizer_card (i : Fin 15) :
    Nat.card (Subgroup.centralizer ({representative i} : Set M12)) = centralizerCeiling i :=
  originalCardinalCover.centralizer_card i

theorem original_representative_cover (g : M12) :
    ∃ i : Fin 15, IsConj g (representative i) :=
  originalCardinalCover.toCardinalCover.covers g

theorem original_class_card_le_fifteen : Nat.card (ConjClasses M12) ≤ 15 := by
  let f : Fin 15 → ConjClasses M12 := fun i => ConjClasses.mk (representative i)
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨i,hi⟩ := original_representative_cover g
    exact ⟨i,(ConjClasses.mk_eq_mk_iff_isConj.mpr hi).symm⟩
  exact (Nat.card_le_card_of_surjective f hf).trans_eq (Nat.card_fin 15)

theorem class_card_le_fifteen [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card (ConjClasses CFSG.Models.Presentations.M12.Model) ≤ 15 := by
  letI : Finite M12 := Finite.of_injective
    (fun g : M12 => (g : Perm12)) Subtype.val_injective
  letI : Finite (ConjClasses M12) :=
    Finite.of_surjective (ConjClasses.mk : M12 → ConjClasses M12) ConjClasses.mk_surjective
  let e := CFSGMathieuTwelveActualEquivalence.actualEquivalence
  exact (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
    (ConjClasses.map_surjective e.symm.surjective)).trans original_class_card_le_fifteen

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualClassCount
