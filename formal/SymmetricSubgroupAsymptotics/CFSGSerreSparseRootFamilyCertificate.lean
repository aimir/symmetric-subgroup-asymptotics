import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction
import SymmetricSubgroupAsymptotics.CFSGIntegralRootActionEntries

/-! Integral sparse data for the whole-family original-source induction.
Each action row consists of one target and an integer coefficient. Finite
integer mixed identities, target heights and target weights supply the
rational coefficient hypotheses of the shared source theorem. Actual
base actions and nonzero parent paths remain required source identities;
no independence, spanning or representation faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreSparseRootFamilyCertificate
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGIntegralRootActionEntries CFSGSerreFiniteRootFamilyInduction
variable {r:ℕ} {I:Type*} [DecidableEq I]

private theorem coefficient_ne_zero (u:I×ℤ) (k:I)
    (hk:rationalRow u k≠0) : u.2≠0 := by
  intro hu
  exact hk (congrFun (rationalRow_eq_zero u hu) k)

private theorem rationalRow_pair (j:I) (c:ℤ) :
    rationalRow (j,c)=(c:ℚ) • Pi.single j 1 := by
  funext k
  by_cases hj:j=k <;> simp [rationalRow,Pi.single_apply,hj]

variable [Fintype I]

theorem source_tables_of_integer_entries
    (A:Matrix (Fin r) (Fin r) ℤ) (x:I→RationalLie A)
    (neg:Bool) (height:I→ℕ) (weight:Fin r→I→ℤ)
    (E F:Fin r→I→I×ℤ) (hdiag:∀a,A a a=2)
    (hweight:∀a j,⁅coroot A neg a,x j⁆=(weight a j:ℚ) • x j)
    (hEbase:∀i j,height j=0→
      ⁅rootVector A neg i,x j⁆=((E i j).2:ℚ) • x (E i j).1)
    (hFbase:∀a j,height j=1→
      ⁅oppositeVector A neg a,x j⁆=((F a j).2:ℚ) • x (F a j).1)
    (hFheight:∀a j,0<height j→(F a j).2≠0→height (F a j).1+1=height j)
    (hEheight:∀i j,0<height j→(E i j).2≠0→height (E i j).1=height j+1)
    (hEweight:∀i a j,0<height j→(E i j).2≠0→
      weight a (E i j).1=A a i+weight a j)
    (hpositive:∀i j,0<height j→∃a,0<(A a i:ℚ)+(weight a j:ℚ))
    (hparent:∀j,1<height j→∃(i:Fin r)(p:I)(c:ℤ),c≠0 ∧ 0<height p ∧
      height p+1=height j ∧ ⁅rootVector A neg i,x p⁆=(c:ℚ) • x j ∧ E i p=(j,c))
    (hcomm:∀i a j,0<height j→
      (if a=i then (-weight a j) • Pi.single j 1 else 0)+
        (F a j).2 • integerRow (E i (F a j).1)=
        (E i j).2 • integerRow (F a (E i j).1)) :
    (∀i j,⁅rootVector A neg i,x j⁆=((E i j).2:ℚ) • x (E i j).1) ∧
      (∀a j,0<height j→
        ⁅oppositeVector A neg a,x j⁆=((F a j).2:ℚ) • x (F a j).1) := by
  have hall := source_tables A x neg height (fun a j=>(weight a j:ℚ))
    (fun i j=>rationalRow (E i j)) (fun a j=>rationalRow (F a j)) hdiag hweight
    (fun i j hj=>by simpa only [combination_rationalRow] using hEbase i j hj)
    (fun a j hj=>by simpa only [combination_rationalRow] using hFbase a j hj)
    (fun a j hj k hk=>by
      have he:=rationalRow_support (F a j) k hk
      subst k
      exact hFheight a j hj (coefficient_ne_zero (F a j) _ hk))
    (fun i j hj k hk=>by
      have he:=rationalRow_support (E i j) k hk
      subst k
      exact hEheight i j hj (coefficient_ne_zero (E i j) _ hk))
    (fun i a j hj k hk=>by
      have he:=rationalRow_support (E i j) k hk
      subst k
      have hw:=hEweight i a j hj (coefficient_ne_zero (E i j) _ hk)
      change (weight a (E i j).1:ℚ)=(A a i:ℚ)+(weight a j:ℚ)
      exact_mod_cast hw)
    hpositive
    (fun j hj=>by
      obtain ⟨i,p,c,hc,hp,hpj,hpath,he⟩:=hparent j hj
      refine ⟨i,p,(c:ℚ),?_,hp,hpj,hpath,?_⟩
      · exact_mod_cast hc
      · change rationalRow (E i p)=(c:ℚ) • Pi.single j 1
        rw [he]
        exact rationalRow_pair j c)
    (fun i a j hj=>by
      change (if a=i then (-(weight a j:ℚ)) • Pi.single j 1 else 0)+
          Fintype.linearCombination ℚ (fun k=>rationalRow (E i k)) (rationalRow (F a j))=
          Fintype.linearCombination ℚ (fun k=>rationalRow (F a k)) (rationalRow (E i j))
      rw [combination_rationalRow,combination_rationalRow]
      exact mixed_identity_cast a i j (weight a j) (F a j) (E i j)
        (E i) (F a) (hcomm i a j hj))
  simpa only [combination_rationalRow] using hall

end SymmetricSubgroupAsymptotics.CFSGSerreSparseRootFamilyCertificate
