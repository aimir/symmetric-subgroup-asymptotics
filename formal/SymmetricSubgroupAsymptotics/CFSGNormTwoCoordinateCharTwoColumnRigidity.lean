import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCharTwoRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootOrbitTransitive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylBlocks

/-! A diagonal actual Geck matrix fixing Cartan columns and commuting
with the signed simple units is one in characteristic two. The proof
uses one coefficient-one simple column and actual Weyl transitivity;
no root census, torus recognition or ordinary-group simplicity is used.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoColumnRigidity
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateRootOrbitTransitive CFSGNormTwoCoordinateLeadingHom
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "J₀" => CFSGNormTwoCoordinateWeylBlocks.GeckIndex A hd hs hp ho
local notation "D₀" => realizationData A hs hp b₀ s₀

omit [(rootPairing A hs hp).IsReduced] in
theorem word_root_column (K:Type) [Field K] [CharP K 2]
    (w:List (Fin r)) (k:Roots A) :
    (wordUnit A hs hp b₀ s₀ K w:Matrix J₀ J₀ K)*ᵥPi.single (.inr k) 1=
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ w k)) 1 := by
  induction w with
  | nil=>exact Matrix.one_mulVec _
  | cons i w ih=>
    change ((canonicalWeyl D₀ K i:Matrix J₀ J₀ K)*
      (wordUnit A hs hp b₀ s₀ K w:Matrix J₀ J₀ K))*ᵥ_= _
    rw [←Matrix.mulVec_mulVec,ih,weyl_root_column]
    rfl

omit [(rootPairing A hs hp).IsReduced] in
theorem simple_parameter_entry (K:Type) [Field K] (i:Fin r) (t:K) :
    (canonicalRoot D₀ K false i t:Matrix J₀ J₀ K)
      (.inl (s₀ i)) (.inr (negativeIndex A hs hp (s₀ i)))=t := by
  have h:=congrArg (fun z:Multiplicative (Fin r→K)=>z.toAdd i)
    (leadingHom_positiveRoot A hd hs hp ho K i t)
  change (canonicalRoot D₀ K false i t:Matrix J₀ J₀ K)
    (.inl (s₀ i)) (.inr (negativeIndex A hs hp (s₀ i)))=(Pi.single i t:Fin r→K) i at h
  simpa only [Pi.single_eq_same] using h

theorem diagonal_eq_one (K:Type) [Field K] [CharP K 2] (i₀:Fin r)
    (d:(Matrix J₀ J₀ K)ˣ) (hdiag:(d:Matrix J₀ J₀ K).IsDiag)
    (hcartan:∀j:(b₀).support,(d:Matrix J₀ J₀ K)*ᵥPi.single (.inl j) 1=Pi.single (.inl j) 1)
    (hcomm:∀neg i t,Commute d (canonicalRoot D₀ K neg i t)) : d=1 := by
  have hrow:(d:Matrix J₀ J₀ K) (.inl (s₀ i₀)) (.inl (s₀ i₀))=1 := by
    have h:=congrFun (hcartan (s₀ i₀)) (.inl (s₀ i₀))
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.single_eq_same] using h
  let k₀:=negativeIndex A hs hp (s₀ i₀)
  have hcol:(d:Matrix J₀ J₀ K) (.inr k₀) (.inr k₀)=1 := by
    have h:=congrArg (fun u:(Matrix J₀ J₀ K)ˣ=>(u:Matrix J₀ J₀ K)
      (.inl (s₀ i₀)) (.inr k₀)) (hcomm false i₀ 1).eq
    change ((d:Matrix J₀ J₀ K)*(canonicalRoot D₀ K false i₀ 1:Matrix J₀ J₀ K)) _ _=
      ((canonicalRoot D₀ K false i₀ 1:Matrix J₀ J₀ K)*(d:Matrix J₀ J₀ K)) _ _ at h
    rw [←hdiag.diagonal_diag,Matrix.diagonal_mul,Matrix.mul_diagonal] at h
    change (d:Matrix J₀ J₀ K) (.inl (s₀ i₀)) (.inl (s₀ i₀))*
      (canonicalRoot D₀ K false i₀ 1:Matrix J₀ J₀ K) (.inl (s₀ i₀)) (.inr k₀)=
      (canonicalRoot D₀ K false i₀ 1:Matrix J₀ J₀ K) (.inl (s₀ i₀)) (.inr k₀)*
      (d:Matrix J₀ J₀ K) (.inr k₀) (.inr k₀) at h
    rw [hrow,simple_parameter_entry,one_mul,one_mul] at h
    exact h.symm
  have hseed:(d:Matrix J₀ J₀ K)*ᵥPi.single (.inr k₀) 1=Pi.single (.inr k₀) 1 := by
    rw [←hdiag.diagonal_diag,Matrix.diagonal_mulVec_single]
    change (Pi.single (.inr k₀) ((d:Matrix J₀ J₀ K) (.inr k₀) (.inr k₀)*1):J₀→K)=Pi.single (.inr k₀) 1
    rw [hcol,mul_one]
  have hW:∀w:List (Fin r),Commute d (wordUnit A hs hp b₀ s₀ K w) := by
    intro w
    induction w with
    | nil=>exact Commute.one_right _
    | cons i w ih=>
      exact (((hcomm false i 1).mul_right (hcomm true i (-1))).mul_right (hcomm false i 1)).mul_right ih
  have hroot (k:Roots A) :
      (d:Matrix J₀ J₀ K)*ᵥPi.single (.inr k) 1=Pi.single (.inr k) 1 := by
    obtain ⟨w,hw⟩:=exists_word_root_to_root A hd hs hp ho k₀ k
    have hwcol:=word_root_column A hd hs hp ho K w k₀
    rw [hw] at hwcol
    have hc:=congrArg (fun u:(Matrix J₀ J₀ K)ˣ=>(u:Matrix J₀ J₀ K)) (hW w).eq
    change (d:Matrix J₀ J₀ K)*(wordUnit A hs hp b₀ s₀ K w:Matrix J₀ J₀ K)=
      (wordUnit A hs hp b₀ s₀ K w:Matrix J₀ J₀ K)*(d:Matrix J₀ J₀ K) at hc
    calc
      _=(d:Matrix J₀ J₀ K)*ᵥ((wordUnit A hs hp b₀ s₀ K w:Matrix J₀ J₀ K)*ᵥPi.single (.inr k₀) 1) :=
        congrArg (fun v:J₀→K=>(d:Matrix J₀ J₀ K)*ᵥv) hwcol.symm
      _=(wordUnit A hs hp b₀ s₀ K w:Matrix J₀ J₀ K)*ᵥ
          ((d:Matrix J₀ J₀ K)*ᵥPi.single (.inr k₀) 1) := by
            rw [Matrix.mulVec_mulVec,hc,←Matrix.mulVec_mulVec]
      _=_ := by rw [hseed,hwcol]
  apply Units.ext
  ext i j
  have hj:(d:Matrix J₀ J₀ K)*ᵥ(Pi.single j 1:J₀→K)=Pi.single j 1 := by
    cases j with
    | inl b=>exact hcartan b
    | inr k=>exact hroot k
  have he:=congrFun hj i
  change (d:Matrix J₀ J₀ K) i j=(1:Matrix J₀ J₀ K) i j
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.single_apply,Matrix.one_apply] using he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoColumnRigidity
