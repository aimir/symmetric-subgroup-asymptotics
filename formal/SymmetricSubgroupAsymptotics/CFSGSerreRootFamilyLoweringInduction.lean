import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootActionTable

/-! The lowering half of a whole finite-family source certificate.
If raises are known below height N, actual nonzero-scalar parent paths
and finite mixed coefficient identities determine all lowerings through
height N+1. Height-zero slots may represent Cartan vectors; their raises
are included in the smaller-height input. No basis is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreRootFamilyLoweringInduction
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreFiniteRootActionTable
variable {r:ℕ} {I:Type*} [Fintype I] [DecidableEq I]
    (A:Matrix (Fin r) (Fin r) ℤ) (x:I→RationalLie A)
local notation "L" => RationalLie A
local notation "lc" => Fintype.linearCombination ℚ x

theorem lowering_table_through_height (neg:Bool) (height:I→ℕ)
    (weight:Fin r→I→ℚ) (e f:Fin r→I→I→ℚ)
    (hweight:∀a j,⁅coroot A neg a,x j⁆=weight a j • x j)
    (hbase:∀a j,height j=1→⁅oppositeVector A neg a,x j⁆=lc (f a j))
    (hsupport:∀a j,0<height j→∀l,f a j l≠0→height l+1=height j)
    (hparent:∀j,1<height j→∃(i:Fin r)(p:I)(c:ℚ),c≠0 ∧ 0<height p ∧
      height p+1=height j ∧ ⁅rootVector A neg i,x p⁆=c • x j ∧
      e i p=c • Pi.single j 1)
    (hcomm:∀i a j,0<height j→
      (if a=i then (-weight a j) • Pi.single j 1 else 0)+
        (∑l,f a j l • e i l)=Fintype.linearCombination ℚ (f a) (e i j))
    (N:ℕ) (hsmall:∀i j,height j<N→⁅rootVector A neg i,x j⁆=lc (e i j)) :
    ∀a j,0<height j→height j≤N+1→⁅oppositeVector A neg a,x j⁆=lc (f a j) := by
  have hmain:∀m:ℕ,∀a j,height j=m→0<m→m≤N+1→
      ⁅oppositeVector A neg a,x j⁆=lc (f a j) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih=>
      intro a j hj hm hbound
      by_cases hone:m=1
      · exact hbase a j (hj.trans hone)
      · have hgt:1<height j:=by omega
        obtain ⟨i,p,c,hc,hp,hpj,hpath,hepath⟩:=hparent j hgt
        have hFp:⁅oppositeVector A neg a,x p⁆=lc (f a p) :=
          ih (height p) (by omega) a p rfl hp (by omega)
        have hE:∀l,f a p l≠0→⁅rootVector A neg i,x l⁆=lc (e i l) := by
          intro l hl
          have hs:=hsupport a p hp l hl
          exact hsmall i l (by omega)
        have hcoeff:=hcomm i a p hp
        rw [hepath,map_smul,Fintype.linearCombination_apply_single,one_smul] at hcoeff
        exact lowering_of_raising_path A x neg i a p (weight a p) (hweight a p)
          (x j) c hc hpath (f a p) (e i) (f a j) hFp hE hcoeff
  intro a j hj hbound
  exact hmain (height j) a j rfl hj hbound

end SymmetricSubgroupAsymptotics.CFSGSerreRootFamilyLoweringInduction
