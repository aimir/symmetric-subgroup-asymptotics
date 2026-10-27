import SymmetricSubgroupAsymptotics.CharacterConjugacySeparation
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCard
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBudgetOfFixedCapacity
import SymmetricSubgroupAsymptotics.MathieuPrimeCycleOddNormalizerWitnesses
import SymmetricSubgroupAsymptotics.PrimeCycleSylowNormalizerSolvable

/-! Two actual original-M12 eleven-cycle classes. Their separation uses
the already checked odd ambient conjugator and original evenness. Their
centralizers and class sizes follow from the literal12-point action and
proved original order95040, without an ATLAS table or completeness claim.
No inherited pinned simplicity is required for these original-model facts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveElevenConjugacyClasses
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveRecoveredPairRelations
open CFSGMathieuTwelveOuterBudgetOfFixedCapacity
open MathieuPrimeCycleOddNormalizerWitnesses

private theorem first_coe : firstElement.val = m12Cycle := by
  change x.val * y.val = xPermutation * yPermutation
  rw [x_coe_eq,y_coe_eq]

private theorem sigma_conjugates :
    m12Sigma * firstElement.val * m12Sigma⁻¹ = (firstElement ^ 2).val := by
  change m12Sigma * firstElement.val * m12Sigma⁻¹ = firstElement.val ^ 2
  rw [first_coe]
  exact m12_conjugate_forward

theorem square_cycleType : (firstElement ^ 2).val.cycleType = {11} := by
  have hc : IsConj firstElement.val (firstElement ^ 2).val :=
    isConj_iff.mpr ⟨m12Sigma,sigma_conjugates⟩
  exact (Equiv.Perm.isConj_iff_cycleType_eq.mp hc).symm.trans firstElement_cycleType

private theorem centralizer_card_of_eleven_cycle (z : M12)
    (hz : z.val.cycleType = {11}) :
    Nat.card (Subgroup.centralizer ({z} : Set M12)) = 11 := by
  let C := Subgroup.centralizer ({z} : Set M12)
  let D := Subgroup.centralizer ({z.val} : Set Perm12)
  have hd : Nat.card D = 11 :=
    PrimeCycleSylowNormalizerSolvable.ambient_centralizer_card z.val (Or.inr rfl) hz
  let f : C →* D := {
    toFun := fun c => ⟨c.val.val,by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg (fun w : M12 => w.val)
        (Subgroup.mem_centralizer_singleton_iff.mp c.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have hval : a.val.val = b.val.val := congrArg (fun t : D => t.val) hab
    exact Subtype.ext (Subtype.ext hval)
  have hupper : Nat.card C ≤ 11 :=
    (Nat.card_le_card_of_injective f hf).trans_eq hd
  have ho : orderOf z = 11 := by
    rw [←Subgroup.orderOf_coe,←Equiv.Perm.lcm_cycleType,hz]
    simp
  have hle : Subgroup.zpowers z ≤ C :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hlower : 11 ≤ Nat.card C := by
    calc
      11 = Nat.card (Subgroup.zpowers z) := by rw [Nat.card_zpowers,ho]
      _ ≤ Nat.card C := Subgroup.card_le_of_le hle
  exact Nat.le_antisymm hupper hlower

theorem first_centralizer_card :
    Nat.card (Subgroup.centralizer ({firstElement} : Set M12)) = 11 :=
  centralizer_card_of_eleven_cycle firstElement firstElement_cycleType

theorem square_centralizer_card :
    Nat.card (Subgroup.centralizer ({firstElement ^ 2} : Set M12)) = 11 :=
  centralizer_card_of_eleven_cycle (firstElement ^ 2) square_cycleType

theorem not_isConj_first_square : ¬IsConj firstElement (firstElement ^ 2) := by
  apply CharacterConjugacySeparation.not_isConj_of_nontrivial_character_coset
    M12Subgroup.subtype Equiv.Perm.sign firstElement (firstElement ^ 2) m12Sigma
  · intro g
    exact Equiv.Perm.mem_alternatingGroup.mp (M12_toPerm_mem_alternatingGroup g)
  · intro c hc
    let D := Subgroup.centralizer ({firstElement.val} : Set Perm12)
    have hd : Nat.card D = 11 :=
      PrimeCycleSylowNormalizerSolvable.ambient_centralizer_card firstElement.val
        (Or.inr rfl) firstElement_cycleType
    let z : D := ⟨c,Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
    exact CharacterConjugacySeparation.character_eq_one_of_odd_card
      (Equiv.Perm.sign.comp D.subtype) (by rw [hd]; decide) z
  · exact sigma_conjugates
  · rw [m12_sign]
    decide

theorem first_class_card : Nat.card {g : M12 // IsConj g firstElement} = 8640 := by
  rw [SymmetricSubgroupAsymptotics.isConj_card_eq_div_centralizer,
    M12Cardinality.card_M12,first_centralizer_card]

theorem square_class_card : Nat.card {g : M12 // IsConj g (firstElement ^ 2)} = 8640 := by
  rw [SymmetricSubgroupAsymptotics.isConj_card_eq_div_centralizer,
    M12Cardinality.card_M12,square_centralizer_card]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveElevenConjugacyClasses
