import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalPositiveSources
import SymmetricSubgroupAsymptotics.CFSGSerreChevalleyInvolution
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Both signed source families use the SAME genuine parent. The checked
original Serre generator exchange therefore transports the entire source
recursion and every first-action identity from one sign to the other.
This avoids a second negative-root source-action certificate. No target
representation, source spanning, or faithfulness is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceInvolution
open CFSG.Models.Chevalley CFSGNormTwoOriginalPositiveSources
open CFSGIntegerMatrixPairing CFSGSerreSignedRootWeights
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)

theorem source_involution (neg : Bool) (k : Positive A) :
    CFSGSerreChevalleyInvolution.rationalMap A (source A hd hs hp neg k).val=
      (source A hd hs hp (!neg) k).val := by
  have hall : ∀n : ℕ,∀k : Positive A,rootHeight A k=n→∀neg,
      CFSGSerreChevalleyInvolution.rationalMap A (source A hd hs hp neg k).val=
        (source A hd hs hp (!neg) k).val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk neg
      classical
      by_cases h : IsSimple A hd k
      · obtain ⟨i,hi⟩ := h
        have he : k=simpleRoot A hd i := Subtype.ext hi
        subst k
        rw [source_simple,source_simple]
        cases neg
        · exact CFSGSerreChevalleyInvolution.rationalMap_E A i
        · exact CFSGSerreChevalleyInvolution.rationalMap_F A i
      · obtain ⟨i,p,hheight,_,_,hpath⟩ := source_parent_all_signs A hd hs hp k h
        rw [←hpath neg,LieHom.map_lie,CFSGSerreChevalleyInvolution.rationalMap_root,
          ih (rootHeight A p) (by omega) p rfl neg]
        exact hpath (!neg)
  exact hall (rootHeight A k) k rfl neg

theorem integralMap_source (neg : Bool) (k : Positive A) :
    CFSGSerreChevalleyInvolution.integralMap A (source A hd hs hp neg k)=
      source A hd hs hp (!neg) k := by
  apply Subtype.ext
  exact source_involution A hd hs hp neg k

abbrev HalfIndex := Fin r ⊕ Positive A

def half (neg : Bool) : HalfIndex A→RationalLie A
  | .inl i=>coroot A neg i
  | .inr k=>(source A hd hs hp neg k).val

theorem half_involution (neg : Bool) (j : HalfIndex A) :
    CFSGSerreChevalleyInvolution.rationalMap A (half A hd hs hp neg j)=
      half A hd hs hp (!neg) j := by
  cases j with
  | inl i =>
    cases neg <;> simp only [half,coroot,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      map_neg,CFSGSerreChevalleyInvolution.rationalMap_H,neg_neg]
  | inr k => exact source_involution A hd hs hp neg k

variable [Fintype (Positive A)] [DecidableEq (Positive A)]

/-- A genuine first-action identity, for raising OR lowering, transports
with exactly the same coefficients to the other signed source half. -/
theorem action_identity_transport (acting family : Bool) (i : Fin r)
    (j : HalfIndex A) (q : HalfIndex A→ℚ)
    (he : ⁅rootVector A acting i,half A hd hs hp family j⁆=
      Fintype.linearCombination ℚ (half A hd hs hp family) q) :
    ⁅rootVector A (!acting) i,half A hd hs hp (!family) j⁆=
      Fintype.linearCombination ℚ (half A hd hs hp (!family)) q := by
  have h := congrArg (CFSGSerreChevalleyInvolution.rationalMap A) he
  simpa only [LieHom.map_lie,CFSGSerreChevalleyInvolution.rationalMap_root,
    half_involution,Fintype.linearCombination_apply,map_sum,map_smul] using h

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceInvolution
