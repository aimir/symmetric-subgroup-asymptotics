import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGSymplecticCartanMatrices
import Mathlib.Tactic.Abel

/-! A unimodular change of the ACTUAL original integral Cartan family.
The tails H_i+...+H_last map to primitive diagonal coordinates D_i.
No inverse Cartan matrix or division by two is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalCartanTail
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates
variable (r : ℕ)

def Hnat (j : ℕ) : Source r :=
  if h : j<r then latticeGenerator (CartanMatrix.C r).transpose (.H ⟨j,h⟩) else 0

def diagonal (j : ℕ) : Mat ℤ r :=
  if h : j<r then Matrix.single (.inl ⟨j,h⟩) (.inl ⟨j,h⟩) 1 -
    Matrix.single (.inr ⟨j,h⟩) (.inr ⟨j,h⟩) 1 else 0

def tail (j : ℕ) : Source r := ∑ a∈Finset.range (r-j),Hnat r (j+a)

private theorem telescoping {M : Type*} [AddCommGroup M] (f : ℕ→M) (k n : ℕ) :
    (∑ a∈Finset.range n,(f (k+a)-f (k+a+1)))=f k-f (k+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.succ_eq_add_one,Nat.add_assoc]
    abel

theorem integralRepresentation_H (i : Fin r) :
    integralSymplecticRepresentation r
      (latticeGenerator (CartanMatrix.C r).transpose (.H i))=cartan ℤ r i := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (generator (CartanMatrix.C r).transpose (.H i)) =
      (Int.castRingHom ℚ).mapMatrix (cartan ℤ r i)
  rw [rationalSymplecticRepresentation_H,map_cartan]

theorem Hnat_image (j : ℕ) :
    integralSymplecticRepresentation r (Hnat r j)=diagonal r j-diagonal r (j+1) := by
  by_cases hj : j<r
  · rw [Hnat,dif_pos hj,integralRepresentation_H,cartan_eq]
    by_cases hn : j+1<r
    · simp only [Fin.val_mk,hn,dif_pos,diagonal,hj]
      abel
    · simp [hn,diagonal,hj]
  · have hn : ¬j+1<r := by omega
    simp only [Hnat,dif_neg hj,map_zero,diagonal,dif_neg hn,sub_self]

theorem tail_image (j : ℕ) :
    integralSymplecticRepresentation r (tail r j)=diagonal r j := by
  unfold tail
  rw [map_sum]
  simp_rw [Hnat_image]
  rw [telescoping]
  have he : diagonal r (j+(r-j))=0 := by
    apply dif_neg
    omega
  rw [he,sub_zero]

theorem tail_step (j : ℕ) (hj : j<r) :
    tail r j=Hnat r j+tail r (j+1) := by
  have hr : r-j=(r-(j+1))+1 := by omega
  unfold tail
  rw [hr,Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  omega

theorem generator_H_from_tails (i : Fin r) :
    latticeGenerator (CartanMatrix.C r).transpose (.H i)=tail r i.val-tail r (i.val+1) := by
  have h:=tail_step r i.val i.isLt
  rw [Hnat,dif_pos i.isLt] at h
  exact eq_sub_iff_add_eq.mpr h.symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalCartanTail
