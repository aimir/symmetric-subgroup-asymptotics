import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan

/-! If the reflected simple root has height zero, the original Weyl
unit preserves EVERY block of that integral grading. The proof uses its
actual signed root columns and its actual Cartan columns. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylHeightBlocks
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckSignedRootColumns CFSGNormTwoGeckFieldWeylCartan
open CFSGSerreQuadraticMatrix CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_preserves (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type*) [CommRing K] (i : Fin r) (hi : height (s i:Roots A).val=0) :
    Supported (weight A hs hp b height) id
      (canonicalWeyl (realizationData A hs hp b s) K i :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  intro j k hjk
  cases k with
  | inl k=>
    have hc := weyl_cartan_general A hs hp b s K i k
    rw [Matrix.mulVec_single_one] at hc
    have he := congrFun hc j
    cases j with
    | inl j=>exact False.elim (hjk rfl)
    | inr j=>simpa [Pi.single_apply] using he
  | inr k=>
    obtain ⟨c,_,hc⟩ := signed_root_column A hs hp b s K i k
    rw [Matrix.mulVec_single_one] at hc
    have he := congrFun hc j
    have hwt : weight A hs hp b height
        (.inr ((rootPairing A hs hp).reflectionPerm (s i) k))=
        weight A hs hp b height (.inr k) := by
      change height (((rootPairing A hs hp).reflectionPerm (s i) k).val)=height k.val
      rw [reflection_val,map_sub,map_smul,hi,smul_zero,sub_zero]
    have hne : j≠.inr ((rootPairing A hs hp).reflectionPerm (s i) k) := by
      intro h
      subst j
      exact hjk hwt
    simpa [Pi.single_apply,hne,Ne.symm hne] using he

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylHeightBlocks
