import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.Tactic.Linarith

/-! The actual norm-two lattice root pairing is reduced: a scalar relating
two roots has square one, hence is a sign. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
open CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

 instance rootPairing_isReduced : (rootPairing A hs hp).IsReduced where
  eq_or_eq_neg i j hij := by
    let P := rootPairing A hs hp
    have hex : ∃c : ℚ,c • P.root i=P.root j := by
      change ¬LinearIndependent ℚ ![P.root i,P.root j] at hij
      rw [LinearIndependent.pair_iff' (P.ne_zero i)] at hij
      exact not_forall_not.mp hij
    obtain ⟨c,hc⟩ := hex
    have hi : rationalPairing A (P.root i) (P.root i)=2 := P.root_coroot_two i
    have hj : rationalPairing A (P.root j) (P.root j)=2 := P.root_coroot_two j
    have hn := congrArg (fun x=>rationalPairing A x x) hc
    simp only [(rationalPairing A).smul_left,(rationalPairing A).smul_right,hi,hj] at hn
    have hprod : (c-1)*(c+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hc1|hcm1
    · have h1 : c=1 := sub_eq_zero.mp hc1
      left
      simpa only [h1,one_smul] using hc
    · have hm1 : c= -1 := by linarith
      right
      have he : -(P.root i)=P.root j := by simpa only [hm1,neg_one_smul] using hc
      exact (neg_eq_iff_eq_neg.mp he)

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
