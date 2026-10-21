import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRotationArrays
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual binary Coxeter word is the literal cyclic permutation of
all positive then negative coordinates. Its matrix is retained, so later
root conjugations do not rely on an abstract Weyl-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryCoxeterMatrix
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGTypeAMonomialMatrices
variable {K : Type} [Field K] [CharP K 2]

def cyclePerm (s : ℕ) : Equiv.Perm (Index (s+1)) :=
  (Equiv.sumCongr (finRotate (s+1)) (finRotate (s+1))).trans
    (Equiv.swap (Sum.inl (0 : Fin (s+1))) (Sum.inr (0 : Fin (s+1))))

theorem cyclePerm_shift (s : ℕ) (side : Bool) (j : ℕ) (hj : j<s) :
    cyclePerm s (if side then Sum.inr (⟨j,by omega⟩ : Fin (s+1)) else Sum.inl ⟨j,by omega⟩)=
      if side then Sum.inr (⟨j+1,by omega⟩ : Fin (s+1)) else Sum.inl ⟨j+1,by omega⟩ := by
  cases side <;> simp [cyclePerm,finRotate_of_lt hj,Equiv.swap_apply_def,Fin.ext_iff]

theorem cyclePerm_positive_last (s : ℕ) :
    cyclePerm s (Sum.inl (Fin.last s))=Sum.inr (0 : Fin (s+1)) := by
  simp [cyclePerm]

theorem cyclePerm_negative_last (s : ℕ) :
    cyclePerm s (Sum.inr (Fin.last s))=Sum.inl (0 : Fin (s+1)) := by
  simp [cyclePerm]

theorem cyclePerm_paired (s : ℕ) (a : Index (s+1)) :
    cyclePerm s (paired a)=paired (cyclePerm s a) := by
  cases a with
  | inl i =>
    by_cases hi : i.val<s
    · have hh := cyclePerm_shift s false i.val hi
      have hh' := cyclePerm_shift s true i.val hi
      simpa only [paired,Bool.false_eq_true,if_false,if_true] using hh'.trans (congrArg paired hh).symm
    · have he : i=Fin.last s := Fin.ext (by simp only [Fin.val_last];omega)
      subst i
      rw [paired,cyclePerm_negative_last,cyclePerm_positive_last]
      rfl
  | inr i =>
    by_cases hi : i.val<s
    · have hh := cyclePerm_shift s false i.val hi
      have hh' := cyclePerm_shift s true i.val hi
      simpa only [paired,Bool.false_eq_true,if_false,if_true] using hh.trans (congrArg paired hh').symm
    · have he : i=Fin.last s := Fin.ext (by simp only [Fin.val_last];omega)
      subst i
      rw [paired,cyclePerm_positive_last,cyclePerm_negative_last]
      rfl

theorem coxeter_binary_basis (s : ℕ) (a : Index (s+1)) :
    ((coxeterWeyl K s).val : Mat K (s+1))*ᵥ Pi.single a 1=Pi.single (cyclePerm s a) 1 := by
  have hside (side : Bool) (i : Fin (s+1)) :
      ((coxeterWeyl K s).val : Mat K (s+1))*ᵥ
        Pi.single (if side then Sum.inr i else Sum.inl i) 1=
        Pi.single (cyclePerm s (if side then Sum.inr i else Sum.inl i)) 1 := by
    by_cases hi : i.val<s
    · have hh := coxeterWeyl_basis_shift K s side i.val hi
      rw [cyclePerm_shift s side i.val hi]
      simpa only [naturalCoordinateBasis_val K s side i,
        naturalCoordinateBasis_val K s side (⟨i.val+1,by omega⟩ : Fin (s+1)),coordinateBasis] using hh
    · have he : i=Fin.last s := Fin.ext (by simp only [Fin.val_last];omega)
      subst i
      cases side
      · change ((coxeterWeyl K s).val : Mat K (s+1))*ᵥ Pi.single (Sum.inl (Fin.last s)) 1=
          Pi.single (cyclePerm s (Sum.inl (Fin.last s))) 1
        rw [cyclePerm_positive_last]
        have hh := coxeterWeyl_binary_positive_last K s
        have h0 := naturalCoordinateBasis_val K s false (Fin.last s)
        have h1 := naturalCoordinateBasis_val K s true (0 : Fin (s+1))
        change naturalCoordinateBasis K s false s=Pi.single (Sum.inl (Fin.last s)) 1 at h0
        change naturalCoordinateBasis K s true 0=Pi.single (Sum.inr (0 : Fin (s+1))) 1 at h1
        rw [h0,h1] at hh
        exact hh
      · change ((coxeterWeyl K s).val : Mat K (s+1))*ᵥ Pi.single (Sum.inr (Fin.last s)) 1=
          Pi.single (cyclePerm s (Sum.inr (Fin.last s))) 1
        rw [cyclePerm_negative_last]
        have hh := coxeterWeyl_binary_negative_last K s
        have h0 := naturalCoordinateBasis_val K s true (Fin.last s)
        have h1 := naturalCoordinateBasis_val K s false (0 : Fin (s+1))
        change naturalCoordinateBasis K s true s=Pi.single (Sum.inr (Fin.last s)) 1 at h0
        change naturalCoordinateBasis K s false 0=Pi.single (Sum.inl (0 : Fin (s+1))) 1 at h1
        rw [h0,h1] at hh
        exact hh
  cases a with
  | inl i => exact hside false i
  | inr i => exact hside true i

theorem coxeter_binary_monomial (s : ℕ) :
    ((coxeterWeyl K s).val : Mat K (s+1))=monomial (cyclePerm s).symm (fun _=>1) := by
  ext i j
  have hh := congrArg (fun v : Index (s+1)→K => v i) (coxeter_binary_basis (K:=K) s j)
  simp only [Matrix.mulVec_single_one,Matrix.col_apply] at hh
  by_cases hi : i=cyclePerm s j
  · subst i
    simpa [monomial_apply] using hh
  · have hi' : (cyclePerm s).symm i≠j := by
      intro he
      apply hi
      exact ((cyclePerm s).apply_symm_apply i).symm.trans (congrArg (cyclePerm s) he)
    simpa [monomial_apply,hi',Pi.single_apply,hi,Ne.symm hi] using hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryCoxeterMatrix
