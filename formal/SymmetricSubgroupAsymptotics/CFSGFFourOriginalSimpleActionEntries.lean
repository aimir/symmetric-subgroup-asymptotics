import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyProfile
import SymmetricSubgroupAsymptotics.CFSGIntegralRootActionEntries

/-! Actual base rows for the whole F4 source-family certificate.
Cartan raises and simple opposite lowerings are the original Cartan/EF
relations with integer sparse entries. The height-zero/one slot
classification binds these rows to the finite-family induction bases. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleActionEntries
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGIntegralRootActionEntries
open CFSGFFourOriginalRootFamilyProfile
local notation "A" => CartanMatrix.F₄

def cartanRaise (i b:Fin 4) : Slot×ℤ := (.inl (simpleIndex i),-A b i)
def simpleLower (a i:Fin 4) : Slot×ℤ := (.inr a,if a=i then -1 else 0)

theorem cartan_source_raise (neg:Bool) (i b:Fin 4) :
    ⁅rootVector A neg i,family neg (.inr b)⁆=
      Fintype.linearCombination ℚ (family neg) (rationalRow (cartanRaise i b)) := by
  rw [combination_rationalRow]
  change ⁅rootVector A neg i,coroot A neg b⁆=
    ((-A b i:ℤ):ℚ) • family neg (.inl (simpleIndex i))
  rw [simple_value,←lie_skew (rootVector A neg i) (coroot A neg b),coroot_root,
    Int.cast_neg,neg_smul]

theorem simple_source_lower (neg:Bool) (a i:Fin 4) :
    ⁅oppositeVector A neg a,family neg (.inl (simpleIndex i))⁆=
      Fintype.linearCombination ℚ (family neg) (rationalRow (simpleLower a i)) := by
  rw [simple_value,combination_rationalRow]
  by_cases hai:a=i
  · subst a
    simp only [simpleLower,if_pos rfl]
    change ⁅oppositeVector A neg i,rootVector A neg i⁆=(-1:ℚ) • coroot A neg i
    rw [opposite_same,neg_one_smul]
  · simp only [simpleLower,if_neg hai,Int.cast_zero,zero_smul]
    exact opposite_distinct A neg a i hai

theorem height_zero_is_cartan (j:Slot) (hj:height j=0) : ∃b:Fin 4,j=.inr b := by
  cases j with
  | inl k=>exact ((rootHeight_positive k).ne' hj).elim
  | inr b=>exact ⟨b,rfl⟩

private theorem rootHeight_one_simple : ∀j:Fin 24,rootHeight j=1→
    ∃i:Fin 4,j=simpleIndex i := by decide +kernel

theorem height_one_is_simple (j:Slot) (hj:height j=1) :
    ∃i:Fin 4,j=.inl (simpleIndex i) := by
  cases j with
  | inl k=>
    obtain ⟨i,hi⟩:=rootHeight_one_simple k hj
    exact ⟨i,congrArg Sum.inl hi⟩
  | inr b=>exact (Nat.zero_ne_one hj).elim

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleActionEntries
