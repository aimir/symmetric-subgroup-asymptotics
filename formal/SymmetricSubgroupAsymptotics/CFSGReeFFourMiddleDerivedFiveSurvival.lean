import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFiveSelectedNoncommutation

/-! The actual order-five derived word moves an actual positive derived
commutator, so it survives the FULL centre quotient. This includes the
Tits parameter without any perfectness, order, or simplicity hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveSurvival
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldVectorEvaluation
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourMiddleFiveSelectedNoncommutation
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalPositiveSylow
open CFSGFFourNormCertificateAction CFSGFFourOriginalFoldedEquivalence
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem fiveWord_positiveCommutator_ne (m : ℕ) :
    fiveWord m * positiveCommutator m ≠ positiveCommutator m * fiveWord m := by
  let e : ZMod 2 →+* Field m := ZMod.castHom (dvd_refl 2) (Field m)
  let v : Fin 26 → Field m := fun j => e (coordinates (ZMod 2) initial j)
  have hn := selected_evaluate_map_ne (Field m)
  change evaluate (Field m) (fiveLetters ++ positiveCommutatorLetters) v ≠
    evaluate (Field m) (positiveCommutatorLetters ++ fiveLetters) v at hn
  intro h
  have he := congrArg (fun g : originalModelFixed m =>
    linearAction (Field m) (modelEquivFolded (Field m) g.val) v) h
  have hleft : linearAction (Field m) (modelEquivFolded (Field m)
      (fiveWord m * positiveCommutator m).val) v =
      evaluate (Field m) (fiveLetters ++ positiveCommutatorLetters) v := by
    change linearAction (Field m) (modelEquivFolded (Field m)
      ((fiveWord m).val * (positiveCommutator m).val)) v = _
    rw [← fiveLetters_value, ← positiveCommutatorLetters_value, ← wordValue_append]
    exact wordValue_action (Field m) _ v
  have hright : linearAction (Field m) (modelEquivFolded (Field m)
      (positiveCommutator m * fiveWord m).val) v =
      evaluate (Field m) (positiveCommutatorLetters ++ fiveLetters) v := by
    change linearAction (Field m) (modelEquivFolded (Field m)
      ((positiveCommutator m).val * (fiveWord m).val)) v = _
    rw [← positiveCommutatorLetters_value, ← fiveLetters_value, ← wordValue_append]
    exact wordValue_action (Field m) _ v
  dsimp only at he
  rw [hleft, hright] at he
  exact hn he

theorem derivedFiveWord_not_mem_center (m : ℕ) :
    derivedFiveWord m ∉ Subgroup.center (commutator (originalModelFixed m)) := by
  intro hc
  have h := congrArg (fun z : commutator (originalModelFixed m) => z.val)
    (Subgroup.mem_center_iff.mp hc (derivedPositiveCommutator m).val)
  change positiveCommutator m * fiveWord m = fiveWord m * positiveCommutator m at h
  exact fiveWord_positiveCommutator_ne m h.symm

def originalFiveWord (m : ℕ) : CFSG.Models.ReeF4 m :=
  derivedReeHom m (derivedFiveWord m)

theorem originalFiveWord_ne_one (m : ℕ) : originalFiveWord m ≠ 1 := by
  intro he
  have hq : (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))))
      (derivedFiveWord m) = 1 := by
    apply (originalReeEquiv m).symm.injective
    calc
      _ = originalFiveWord m := rfl
      _ = 1 := he
      _ = (originalReeEquiv m).symm 1 := (map_one (originalReeEquiv m).symm).symm
  exact derivedFiveWord_not_mem_center m ((QuotientGroup.eq_one_iff _).mp hq)

theorem originalFiveWord_pow_five (m : ℕ) : (originalFiveWord m)^5 = 1 := by
  have h : (derivedFiveWord m)^5 = 1 := Subtype.ext (fiveWord_pow_five m)
  exact (map_pow (derivedReeHom m) (derivedFiveWord m) 5).symm.trans
    ((congrArg (derivedReeHom m) h).trans (map_one (derivedReeHom m)))

theorem originalFiveWord_order (m : ℕ) : orderOf (originalFiveWord m) = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (originalFiveWord_pow_five m) (originalFiveWord_ne_one m)

theorem titsFiveWord_order : orderOf (originalFiveWord 0) = 5 := originalFiveWord_order 0

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveSurvival
