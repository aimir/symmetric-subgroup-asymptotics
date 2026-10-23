import SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalPropagationPilot
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientStepEntries
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Algebra.CharP.Basic

/-! The selected diagonal-propagation edges are literal entries of the
actual positive E6 root units in characteristic two. Reification uses
norm-two proofs for a single index, never a general Roots enumeration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalStepEntries
open CFSGFFourSerreMatrices CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing
open CFSGTwistedE6GeckDiagramCovariance CFSGFFourE6NormQuotientStepEntries
open CFSGFFourE6NormQuotientCoefficientPilot CFSGFFourE6NormDiagonalPropagationPilot
open CFSGSerreQuadraticMatrix

def actualIndex : (z:RawIndex) → rawNorm z=2 → Index
  | .inl i,_=>.inl (E6Index i)
  | .inr v,h=>.inr ⟨v,h⟩

theorem erase_actualIndex (z:RawIndex) (hz:rawNorm z=2) : eraseGeck (actualIndex z hz)=z := by
  cases z with
  | inl i=>change (Sum.inl (E6Index.symm (E6Index i)):RawIndex)=Sum.inl i;rw [Equiv.symm_apply_apply]
  | inr v=>rfl

theorem rawNorm_erase (r:Index) : rawNorm (eraseGeck r)=2 := by
  cases r with
  | inl i=>rfl
  | inr r=>exact r.property

theorem actualIndex_erase (r:Index) (hz:rawNorm (eraseGeck r)=2) : actualIndex (eraseGeck r) hz=r := by
  cases r with
  | inl i=>change (Sum.inl (E6Index (E6Index.symm i)):Index)=Sum.inl i;rw [Equiv.apply_symm_apply]
  | inr r=>rfl

def rawDiag (K:Type) [Field K] (M:Matrix Index Index K) (z:RawIndex) : K :=
  if h:rawNorm z=2 then M (actualIndex z h) (actualIndex z h) else 1

theorem rawDiag_erase (K:Type) [Field K] (M:Matrix Index Index K) (r:Index) :
    rawDiag K M (eraseGeck r)=M r r := by
  rw [rawDiag,dif_pos (rawNorm_erase r),actualIndex_erase]

private theorem cast_eq_of_mod_two (K:Type) [Field K] [CharP K 2]
    (a b:ℤ) (h:a%2=b%2) : (a:K)=(b:K) := by
  calc
    (a:K)=((a%2:ℤ):K):=CharP.intCast_eq_intCast_mod K 2
    _=((b%2:ℤ):K):=congrArg (fun z:ℤ=>(z:K)) h
    _=(b:K):=(CharP.intCast_eq_intCast_mod K 2).symm

theorem unit_step_entry (K:Type) [Field K] [CharP K 2]
    (i:Fin 6) (r s:RawIndex) (hr:rawNorm r=2) (hs:rawNorm s=2) (hne:r≠s)
    (hE:stepEntry i r s%2=1) (hD:secondEntry i r s%2=0) :
    (canonicalRoot rawData K false i 1:Matrix Index Index K) (actualIndex r hr) (actualIndex s hs)=1 := by
  have hactual:actualIndex r hr≠actualIndex s hs := by
    intro h
    apply hne
    have hraw:=congrArg eraseGeck h
    simpa only [erase_actualIndex] using hraw
  have hroot (a b:Index):fieldRoot rawData K false i a b=(e6EZ i a b:K):=rfl
  have hsecond (a b:Index):fieldSecond rawData K false i a b=(e6SecondZ i a b:K):=rfl
  have hEc:(stepEntry i r s:K)=1 := by
    simpa only [Int.cast_one] using cast_eq_of_mod_two K (stepEntry i r s) 1 (by simpa using hE)
  have hDc:(secondEntry i r s:K)=0 := by
    simpa only [Int.cast_zero] using cast_eq_of_mod_two K (secondEntry i r s) 0 (by simpa using hD)
  rw [canonicalRoot_val]
  simp only [one_smul,one_pow,Matrix.add_apply,hroot,hsecond,e6EZ_entry,e6SecondZ_entry,
    erase_actualIndex,Matrix.one_apply,if_neg hactual,hEc,hDc,zero_add,add_zero]

private theorem diagonal_eq_of_commuting_entry (K:Type) [Field K]
    (M X:Matrix Index Index K) (hdiag:M.IsDiag) (hcomm:M*X=X*M)
    (r s:Index) (hentry:X r s=1) : M r r=M s s := by
  have h:=congrArg (fun N:Matrix Index Index K=>N r s) hcomm
  dsimp only at h
  rw [←hdiag.diagonal_diag,Matrix.diagonal_mul,Matrix.mul_diagonal] at h
  change M r r*X r s=X r s*M s s at h
  simpa only [hentry,mul_one,one_mul] using h

theorem rawDiag_step_eq (K:Type) [Field K] [CharP K 2]
    (M:Matrix Index Index K) (hdiag:M.IsDiag)
    (hcomm:∀i:Fin 6,M*(canonicalRoot rawData K false i 1:Matrix Index Index K)=
      (canonicalRoot rawData K false i 1:Matrix Index Index K)*M)
    (e:Step) (he:e∈steps) : rawDiag K M e.child=rawDiag K M e.parent := by
  obtain ⟨hne,hchild,hparent,hE,hD⟩:=steps_entries e he
  have hrow:rawNorm (row e)=2 := by
    cases h:e.reversed
    · simpa [row,h] using hchild
    · simpa [row,h] using hparent
  have hcol:rawNorm (col e)=2 := by
    cases h:e.reversed
    · simpa [col,h] using hparent
    · simpa [col,h] using hchild
  have hne':row e≠col e := by
    cases h:e.reversed
    · simpa [row,col,h] using hne
    · simpa [row,col,h] using Ne.symm hne
  have hentry:=unit_step_entry K e.node (row e) (col e) hrow hcol hne' hE hD
  have hvalues:=diagonal_eq_of_commuting_entry K M _ hdiag (hcomm e.node) _ _ hentry
  have hraw:rawDiag K M (row e)=rawDiag K M (col e) := by
    simpa only [rawDiag,dif_pos hrow,dif_pos hcol] using hvalues
  cases h:e.reversed
  · simpa [row,col,h] using hraw
  · simpa [row,col,h] using hraw.symm

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalStepEntries
