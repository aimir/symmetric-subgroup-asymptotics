import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSourceActionTables
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedActionEntries

/-! Actual source action on all52 integral family vectors. The signed
28-slot source tables are converted to the four original H generators;
no representation injectivity or basis assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedSourceActions
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalRootFamilyProfile
open CFSGFFourOriginalFullCoefficientCertificate CFSGFFourOriginalSignedActionEntries
local notation "A" => CartanMatrix.F₄

theorem slot_value (neg:Bool) (j:Slot) :
    family neg j=(slotCoefficient neg j:ℚ) • vectors (slotIndex neg j) := by
  cases j with
  | inl j=>
    change (rootVectors neg j).val=(1:ℚ) • (rootVectors neg j).val
    rw [one_smul]
  | inr b=>
    cases neg
    · change generator A (.H b)=(1:ℚ) • generator A (.H b)
      rw [one_smul]
    · change -generator A (.H b)=(-1:ℚ) • generator A (.H b)
      rw [neg_one_smul]

theorem entry_value (neg:Bool) (u:Slot×ℤ) :
    (u.2:ℚ) • family neg u.1=
      ((convertEntry neg u).2:ℚ) • vectors (convertEntry neg u).1 := by
  change (u.2:ℚ) • family neg u.1=
    ((u.2*slotCoefficient neg u.1:ℤ):ℚ) • vectors (slotIndex neg u.1)
  rw [slot_value,smul_smul,Int.cast_mul]

private theorem root_action (neg s:Bool) (i:Fin 4) (j:Fin 24) :
    ⁅rootVector A neg i,vectors (.inl (s,j))⁆=
      ((signedEntry neg i (.inl (s,j))).2:ℚ) • vectors (signedEntry neg i (.inl (s,j))).1 := by
  by_cases hs:s=neg
  · subst s
    simp only [signedEntry,if_pos rfl]
    exact (CFSGFFourOriginalSourceActionTables.raising neg i (.inl j)).trans
      (entry_value neg (raisingEntry i (.inl j)))
  · have hn:neg=(!s):=by cases neg <;> cases s <;> simp_all
    subst neg
    simp only [signedEntry,if_neg hs]
    exact (CFSGFFourOriginalSourceActionTables.lowering s i (.inl j)
      (rootHeight_positive j)).trans (entry_value s (loweringEntry i (.inl j)))

theorem action (neg:Bool) (i:Fin 4) (j:BasisIndex) :
    ⁅rootVector A neg i,vectors j⁆=
      ((signedEntry neg i j).2:ℚ) • vectors (signedEntry neg i j).1 := by
  cases j with
  | inl z=>exact root_action neg z.1 i z.2
  | inr b=>
    have h:=CFSGFFourOriginalSourceActionTables.raising neg i (.inr b)
    rw [cartan_entries] at h
    cases neg
    · exact h
    · have hn:=congrArg (fun z:RationalLie A=> -z) h
      change -⁅rootVector A true i,-generator A (.H b)⁆=
        -(((-A b i:ℤ):ℚ) • (rootVectors true (simpleIndex i)).val) at hn
      change ⁅rootVector A true i,generator A (.H b)⁆=
        (A b i:ℚ) • (rootVectors true (simpleIndex i)).val
      simpa only [lie_neg,neg_neg,Int.cast_neg,neg_smul] using hn

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSignedSourceActions
