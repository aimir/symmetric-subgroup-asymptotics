import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith

/-! Literal natural simple-root matrices for the pinned D_r Cartan table.
The terminal root is e_(r-2)+e_(r-1), with no transpose convention change. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)
abbrev Index := Fin r ⊕ Fin r
abbrev Mat := Matrix (Index r) (Index r) R

def previous (i : Fin r) : Fin r :=
  ⟨i.val-1,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

@[simp] theorem previous_val (i : Fin r) : (previous r i).val=i.val-1 := rfl

def positive (i : Fin r) : Mat R r :=
  if h : i.val+1<r then
    Matrix.single (Sum.inl i) (Sum.inl (⟨i.val+1,h⟩ : Fin r)) 1-
      Matrix.single (Sum.inr (⟨i.val+1,h⟩ : Fin r)) (Sum.inr i) 1
  else
    Matrix.single (Sum.inl (previous r i)) (Sum.inr i) 1-
      Matrix.single (Sum.inl i) (Sum.inr (previous r i)) 1

def negative (i : Fin r) : Mat R r := (positive R r i).transpose

def cartan (i : Fin r) : Mat R r := ⁅positive R r i,negative R r i⁆

theorem previous_ne_of_last (hr : 4≤r) (i : Fin r) (hi : ¬i.val+1<r) : previous r i≠i := by
  intro he
  have hv := congrArg Fin.val he
  have hil := i.isLt
  simp only [previous_val] at hv
  omega

theorem positive_sq_zero (i : Fin r) : positive R r i^2=0 := by
  unfold positive
  split_ifs with hi
  · have hne : (⟨i.val+1,hi⟩ : Fin r)≠i := by
      intro he
      have hv := congrArg Fin.val he
      change i.val+1=i.val at hv
      omega
    simp [pow_two,sub_mul,mul_sub,hne,hne.symm]
  · simp [pow_two,sub_mul,mul_sub]

theorem negative_sq_zero (i : Fin r) : negative R r i^2=0 := by
  rw [negative,pow_two,←Matrix.transpose_mul,←pow_two,positive_sq_zero]
  exact Matrix.transpose_zero

theorem positive_negative (i : Fin r) : ⁅positive R r i,negative R r i⁆=cartan R r i := rfl

theorem cartan_transpose (i : Fin r) : (cartan R r i).transpose=cartan R r i := by
  simp only [cartan,Ring.lie_def,negative,Matrix.transpose_sub,Matrix.transpose_mul,
    Matrix.transpose_transpose]

theorem map_positive {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (positive R r i)=positive S r i := by
  by_cases hi : i.val+1<r
  · simp only [positive,dif_pos hi]
    rw [map_sub]
    change (Matrix.single _ _ (1:R)).map f-(Matrix.single _ _ (1:R)).map f=_
    simp only [Matrix.map_single,map_one]
  · simp only [positive,dif_neg hi]
    rw [map_sub]
    change (Matrix.single _ _ (1:R)).map f-(Matrix.single _ _ (1:R)).map f=_
    simp only [Matrix.map_single,map_one]

theorem map_negative {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (negative R r i)=negative S r i := by
  change (positive R r i).transpose.map f=(positive S r i).transpose
  rw [Matrix.transpose_map]
  exact congrArg Matrix.transpose (map_positive R r f i)

theorem map_cartan {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (cartan R r i)=cartan S r i := by
  simp only [cartan,Ring.lie_def,map_sub,map_mul,map_positive,map_negative]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
