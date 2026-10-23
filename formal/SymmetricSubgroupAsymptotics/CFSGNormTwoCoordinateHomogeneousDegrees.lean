import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeightDiameter
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAnyNonrootDegreeZero
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLieForm
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGramEntries

/-! A nonzero homogeneous element of the SAME coordinate Geck Lie
algebra has zero or norm-two degree. Norm four/six use actual generated
Lie recognition; norm eight uses its proved invariant Gram form. Thus
ambient matrix grading is not being mistaken for a root-space theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHomogeneousDegrees
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckColumns CFSGGradedMatrixSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

theorem weight_difference_norm_cases (x y : (b₀).support⊕Roots A) :
    let q := integerPairing A (ell x-ell y) (ell x-ell y)
    q=0 ∨ q=2 ∨ q=4 ∨ q=6 ∨ q=8 := by
  dsimp only
  cases x with
  | inl i=>
    cases y with
    | inl j=>
      change integerPairing A (0-0) (0-0)=0 ∨ _
      left
      simp
    | inr k=>
      right
      left
      change integerPairing A (0-k.val) (0-k.val)=2
      simp only [zero_sub,map_neg,LinearMap.neg_apply,neg_neg,k.property]
  | inr k=>
    cases y with
    | inl j=>
      right
      left
      change integerPairing A (k.val-0) (k.val-0)=2
      simpa only [sub_zero] using k.property
    | inr l=>
      change integerPairing A (k.val-l.val) (k.val-l.val)=0 ∨ _
      simp only [latticeWeight,norm_sub A hs,k.property,l.property]
      have hb := root_pairing_bounds A hs hp k l
      omega

omit [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
theorem norm_eight_degree_zero (M : Mat) (d : Fin r→ℤ)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+d) M)
    (hnorm : integerPairing A d d=8) : M=0 := by
  apply Matrix.ext
  intro x y
  change M x y=0
  by_cases he : ell x=ell y+d
  · have hdiff : ell x-ell y=d := by
      rw [he]
      exact add_sub_cancel_left _ _
    have hn : integerPairing A (ell x-ell y) (ell x-ell y)=8 := by
      rw [hdiff,hnorm]
    cases x with
    | inl i=>
      cases y with
      | inl j=>
        change integerPairing A (0-0) (0-0)=8 at hn
        norm_num at hn
      | inr k=>
        change integerPairing A (0-k.val) (0-k.val)=8 at hn
        simp only [zero_sub,map_neg,LinearMap.neg_apply,neg_neg,k.property] at hn
        norm_num at hn
    | inr k=>
      cases y with
      | inl j=>
        change integerPairing A (k.val-0) (k.val-0)=8 at hn
        simp only [sub_zero,k.property] at hn
        norm_num at hn
      | inr l=>
        change integerPairing A (k.val-l.val) (k.val-l.val)=8 at hn
        rw [norm_sub A hs,k.property,l.property] at hn
        have hpair : integerPairing A k.val l.val= -2 := by omega
        have hk : k=negativeIndex A hs hp l := by
          apply Subtype.ext
          exact ((root_pairing_eq_neg_two_iff A hs hp k l).mp hpair).trans
            (negative_val A hs hp l).symm
        have hz := CFSGNormTwoGeckGramEntries.opposite_entry_zero A hs hp b₀ M
          (CFSGNormTwoGeckLieForm.mem_form A hs hp hd ho hM) l
        simpa only [hk] using hz
  · exact hdeg x y he

theorem nonzero_homogeneous_norm_zero_or_two (M : Mat) (d : Fin r→ℤ)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+d) M) (hne : M≠0) :
    integerPairing A d d=0 ∨ integerPairing A d d=2 := by
  obtain ⟨x,y,hxy⟩ : ∃x y,M x y≠0 := by
    by_contra h
    apply hne
    apply Matrix.ext
    intro x y
    change M x y=0
    exact not_not.mp (fun hxy=>h ⟨x,y,hxy⟩)
  have he : ell x=ell y+d := by
    by_contra he
    exact hxy (hdeg x y he)
  have hdiff : ell x-ell y=d := by
    rw [he]
    exact add_sub_cancel_left _ _
  have hc := weight_difference_norm_cases A hd hs hp ho x y
  dsimp only at hc
  rw [hdiff] at hc
  rcases hc with h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hne (CFSGNormTwoCoordinateAnyNonrootDegreeZero.norm_four_or_six_degree_zero
      A hd hs hp ho M d hM hdeg (Or.inl h)))
  · exact False.elim (hne (CFSGNormTwoCoordinateAnyNonrootDegreeZero.norm_four_or_six_degree_zero
      A hd hs hp ho M d hM hdeg (Or.inr h)))
  · exact False.elim (hne (norm_eight_degree_zero A hd hs hp ho M d hM hdeg h))

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHomogeneousDegrees
