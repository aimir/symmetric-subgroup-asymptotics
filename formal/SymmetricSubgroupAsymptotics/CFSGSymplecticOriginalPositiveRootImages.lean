import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalRootParents
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootMatrixArithmetic
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalCartanTail

/-! Whole positive-root images in the ACTUAL original integral source.
Induction uses source parent equalities, then literal sparse matrix
arithmetic. No source realization injectivity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveRootImages
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalRootParents
variable (r : ℕ)

theorem generator_E_image (i : Fin r) :
    integralSymplecticRepresentation r
      (latticeGenerator (CartanMatrix.C r).transpose (.E i))=positive ℤ r i := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (generator (CartanMatrix.C r).transpose (.E i)) =
      (Int.castRingHom ℚ).mapMatrix (positive ℤ r i)
  rw [rationalSymplecticRepresentation_E,map_positive]

private theorem long_source_parent (i : Fin r) (hi : i.val+1<r) :
    CFSGSymplecticOriginalRootCandidates.long r false i=integralOperator (CartanMatrix.C r).transpose false i 2
      (CFSGSymplecticOriginalRootCandidates.long r false ⟨i.val+1,hi⟩) := by
  let last : Fin r := ⟨r-1,by omega⟩
  have hs:=descend_split r i last (by dsimp [last];omega)
  unfold CFSGSymplecticOriginalRootCandidates.long
  change path r false last _=integralOperator _ false i 2 (path r false last _)
  rw [hs]
  simp only [steps,List.map_append,List.map_cons,List.map_nil]
  exact positive_path_snoc r last _ i 2

theorem long_image (i : Fin r) :
    integralSymplecticRepresentation r (CFSGSymplecticOriginalRootCandidates.long r false i)=CFSGSymplecticUniformRootMatrixArithmetic.long ℤ r i := by
  suffices h : ∀ n : ℕ,∀ i : Fin r,r-i.val=n→
      integralSymplecticRepresentation r (CFSGSymplecticOriginalRootCandidates.long r false i)=CFSGSymplecticUniformRootMatrixArithmetic.long ℤ r i by
    exact h _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hn
    by_cases hi : i.val+1<r
    · rw [long_source_parent r i hi,integralRepresentation_operator,
        ih (r-(i.val+1)) (by omega) ⟨i.val+1,hi⟩ rfl]
      change CFSGIntegralSquareZeroOperators.operator ℤ (positive ℤ r i) 2
        (CFSGSymplecticUniformRootMatrixArithmetic.long ℤ r ⟨i.val+1,hi⟩)=CFSGSymplecticUniformRootMatrixArithmetic.long ℤ r i
      exact CFSGSymplecticUniformRootMatrixArithmetic.long_divided_parent ℤ r i hi
    · have he : (⟨r-1,by have hlt := i.isLt;omega⟩ : Fin r)=i := by
        apply Fin.ext
        change r-1=i.val
        have hlt := i.isLt
        omega
      simp only [CFSGSymplecticOriginalRootCandidates.long,he,descend_self,steps,List.map_nil,path,
        Bool.false_eq_true,if_false,one_smul,
        CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps]
      rw [generator_E_image]
      simp only [positive,dif_neg hi,CFSGSymplecticUniformRootMatrixArithmetic.long]

theorem difference_image (ij : Pair r) :
    integralSymplecticRepresentation r (CFSGSymplecticOriginalRootCandidates.difference r false ij)=
      CFSGSymplecticUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2 := by
  suffices h : ∀ n : ℕ,∀ ij : Pair r,ij.val.2.val-ij.val.1.val=n→
      integralSymplecticRepresentation r (CFSGSymplecticOriginalRootCandidates.difference r false ij)=
        CFSGSymplecticUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2 by exact h _ ij rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ij hn
    let i:=ij.val.1
    let j:=ij.val.2
    have hij : i.val<j.val:=ij.property
    have hi : i.val+1<r:=by omega
    by_cases hadj : j.val=i.val+1
    · have hstart : (⟨j.val-1,by have hjlt := j.isLt;omega⟩ : Fin r)=i := by
        apply Fin.ext
        change j.val-1=i.val
        omega
      unfold CFSGSymplecticOriginalRootCandidates.difference
      change integralSymplecticRepresentation r (path r false _ _)=_
      rw [hstart,descend_self]
      simp only [steps,List.map_nil,path,Bool.false_eq_true,if_false,one_smul,
        CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps]
      rw [generator_E_image]
      have hj : (⟨i.val+1,hi⟩ : Fin r)=j := by apply Fin.ext;exact hadj.symm
      simp only [positive,dif_pos hi,hj,CFSGSymplecticUniformRootMatrixArithmetic.difference] <;> rfl
    · have hgap : i.val+1<j.val:=by omega
      let next : Fin r:=⟨i.val+1,hi⟩
      let parent : Pair r:=⟨(next,j),hgap⟩
      have hp:=positive_difference_parent r i j hgap
      change integralOperator _ false i 1 (CFSGSymplecticOriginalRootCandidates.difference r false parent)=CFSGSymplecticOriginalRootCandidates.difference r false ij at hp
      rw [←hp,integralRepresentation_operator,
        ih (j.val-next.val) (by dsimp [next];omega) parent rfl]
      change CFSGIntegralSquareZeroOperators.operator ℤ (positive ℤ r i) 1
        (CFSGSymplecticUniformRootMatrixArithmetic.difference ℤ r next j)=CFSGSymplecticUniformRootMatrixArithmetic.difference ℤ r i j
      rw [CFSGIntegralSquareZeroOperators.operator_one]
      exact CFSGSymplecticUniformRootMatrixArithmetic.difference_parent ℤ r i j hi hgap

theorem sum_image (ij : Pair r) :
    integralSymplecticRepresentation r (CFSGSymplecticOriginalRootCandidates.sumRoot r false ij)=
      CFSGSymplecticUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2 := by
  suffices h : ∀ n : ℕ,∀ ij : Pair r,ij.val.2.val-ij.val.1.val=n→
      integralSymplecticRepresentation r (CFSGSymplecticOriginalRootCandidates.sumRoot r false ij)=
        CFSGSymplecticUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2 by exact h _ ij rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ij hn
    let i:=ij.val.1
    let j:=ij.val.2
    have hij : i.val<j.val:=ij.property
    have hi : i.val+1<r:=by omega
    by_cases hadj : j.val=i.val+1
    · have hj : (⟨i.val+1,hi⟩ : Fin r)=j := by apply Fin.ext;exact hadj.symm
      have hpair : (⟨(i,(⟨i.val+1,hi⟩ : Fin r)),by change i.val < i.val + 1;omega⟩ : Pair r)=ij := by
        apply Subtype.ext
        exact Prod.ext rfl hj
      have hp:=adjacent_sum_parent r i hi
      dsimp only at hp
      rw [hpair,hj] at hp
      change integralOperator _ false i 1 (CFSGSymplecticOriginalRootCandidates.long r false j)=CFSGSymplecticOriginalRootCandidates.sumRoot r false ij at hp
      rw [←hp,integralRepresentation_operator,long_image]
      change CFSGIntegralSquareZeroOperators.operator ℤ (positive ℤ r i) 1
        (CFSGSymplecticUniformRootMatrixArithmetic.long ℤ r j)=CFSGSymplecticUniformRootMatrixArithmetic.sumRoot ℤ r i j
      rw [CFSGIntegralSquareZeroOperators.operator_one,←hj]
      exact CFSGSymplecticUniformRootMatrixArithmetic.adjacent_sum_parent ℤ r i hi
    · have hgap : i.val+1<j.val:=by omega
      let next : Fin r:=⟨i.val+1,hi⟩
      let parent : Pair r:=⟨(next,j),hgap⟩
      have hp:=positive_sum_parent r i j hgap
      change integralOperator _ false i 1 (CFSGSymplecticOriginalRootCandidates.sumRoot r false parent)=CFSGSymplecticOriginalRootCandidates.sumRoot r false ij at hp
      rw [←hp,integralRepresentation_operator,
        ih (j.val-next.val) (by dsimp [next];omega) parent rfl]
      change CFSGIntegralSquareZeroOperators.operator ℤ (positive ℤ r i) 1
        (CFSGSymplecticUniformRootMatrixArithmetic.sumRoot ℤ r next j)=CFSGSymplecticUniformRootMatrixArithmetic.sumRoot ℤ r i j
      rw [CFSGIntegralSquareZeroOperators.operator_one]
      exact CFSGSymplecticUniformRootMatrixArithmetic.sum_parent ℤ r i j hi hgap

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveRootImages
