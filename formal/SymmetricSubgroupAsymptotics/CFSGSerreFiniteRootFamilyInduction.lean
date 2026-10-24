import SymmetricSubgroupAsymptotics.CFSGSerreRootFamilyLoweringInduction

/-! A whole finite-family certificate for genuine original Serre source
actions. Base Cartan raises, simple lowerings, actual parent paths and
finite mixed coefficient identities determine every source action.
The proof uses height induction and positive-weight lowering uniqueness;
it assumes neither a source basis nor matrix faithfulness. The finite
integer data and parent paths must still be proved in each application. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreFiniteRootActionTable
open CFSGSerreRootFamilyLoweringInduction
variable {r:ℕ} {I:Type*} [Fintype I] [DecidableEq I]
    (A:Matrix (Fin r) (Fin r) ℤ) (x:I→RationalLie A)
local notation "lc" => Fintype.linearCombination ℚ x

private theorem combination_weight (neg:Bool) (a:Fin r) (weight:I→ℚ) (mu:ℚ)
    (q:I→ℚ) (hw:∀k,⁅coroot A neg a,x k⁆=weight k • x k)
    (hq:∀k,q k≠0→weight k=mu) :
    ⁅coroot A neg a,lc q⁆=mu • lc q := by
  change ⁅coroot A neg a,∑k,q k • x k⁆=mu • (∑k,q k • x k)
  rw [lie_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz:q k=0
  · simp only [hz,zero_smul,lie_zero,smul_zero]
  · rw [lie_smul,hw,hq k hz,smul_comm]

theorem source_tables (neg:Bool) (height:I→ℕ) (weight:Fin r→I→ℚ)
    (e f:Fin r→I→I→ℚ) (hdiag:∀a,A a a=2)
    (hweight:∀a j,⁅coroot A neg a,x j⁆=weight a j • x j)
    (hEbase:∀i j,height j=0→⁅rootVector A neg i,x j⁆=lc (e i j))
    (hFbase:∀a j,height j=1→⁅oppositeVector A neg a,x j⁆=lc (f a j))
    (hFsupport:∀a j,0<height j→∀l,f a j l≠0→height l+1=height j)
    (hEsupport:∀i j,0<height j→∀l,e i j l≠0→height l=height j+1)
    (hEweight:∀i a j,0<height j→∀l,e i j l≠0→
      weight a l=(A a i:ℚ)+weight a j)
    (hpositive:∀i j,0<height j→∃a,0<(A a i:ℚ)+weight a j)
    (hparent:∀j,1<height j→∃(i:Fin r)(p:I)(c:ℚ),c≠0 ∧ 0<height p ∧
      height p+1=height j ∧ ⁅rootVector A neg i,x p⁆=c • x j ∧
      e i p=c • Pi.single j 1)
    (hcomm:∀i a j,0<height j→
      (if a=i then (-weight a j) • Pi.single j 1 else 0)+
        (∑l,f a j l • e i l)=Fintype.linearCombination ℚ (f a) (e i j)) :
    (∀i j,⁅rootVector A neg i,x j⁆=lc (e i j)) ∧
      (∀a j,0<height j→⁅oppositeVector A neg a,x j⁆=lc (f a j)) := by
  have hmain:∀n:ℕ,∀i j,height j=n→⁅rootVector A neg i,x j⁆=lc (e i j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      intro i j hj
      by_cases hn:n=0
      · exact hEbase i j (hj.trans hn)
      · have hjpos:0<height j:=by omega
        have hsmall:∀i k,height k<n→⁅rootVector A neg i,x k⁆=lc (e i k) := by
          intro b k hk
          exact ih (height k) hk b k rfl
        have hF:=lowering_table_through_height A x neg height weight e f hweight hFbase
          hFsupport hparent hcomm n hsmall
        obtain ⟨a,hpos⟩:=hpositive i j hjpos
        have htargetWeight:⁅coroot A neg a,lc (e i j)⁆=
            ((A a i:ℚ)+weight a j) • lc (e i j) :=
          combination_weight A x neg a (weight a) _ (e i j) (hweight a)
            (hEweight i a j hjpos)
        have htargetLower:⁅oppositeVector A neg a,lc (e i j)⁆=
            lc (Fintype.linearCombination ℚ (f a) (e i j)) := by
          change ⁅rootVector A (!neg) a,lc (e i j)⁆=
            lc (∑k,e i j k • f a k)
          apply raising_combination A x (!neg) a (e i j) (f a)
          intro k hk
          have hs:=hEsupport i j hjpos k hk
          exact hF a k (by omega) (by omega)
        have hE:∀l,f a j l≠0→⁅rootVector A neg i,x l⁆=lc (e i l) := by
          intro l hl
          have hs:=hFsupport a j hjpos l hl
          exact hsmall i l (by omega)
        exact raising_eq_of_lowering_coefficients A x neg i a (hdiag a) j (weight a j)
          hpos (lc (e i j)) (hweight a j) htargetWeight (f a j) (e i)
          (Fintype.linearCombination ℚ (f a) (e i j)) (hF a j hjpos (by omega)) hE
          htargetLower (hcomm i a j hjpos)
  have hraise:∀i j,⁅rootVector A neg i,x j⁆=lc (e i j):=fun i j=>hmain (height j) i j rfl
  refine ⟨hraise,?_⟩
  intro a j hj
  exact lowering_table_through_height A x neg height weight e f hweight hFbase hFsupport
    hparent hcomm (height j) (fun i k _=>hraise i k) a j hj (Nat.le_succ _)

end SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction
