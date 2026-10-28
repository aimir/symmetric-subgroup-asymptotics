import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRationalFirstActionSpan
import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceFamily
import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceBaseActions

/-! Whole ORIGINAL rational source spanning from the two genuine signed
half-action identities. The Cartan sign is retained exactly. This is the
final assembly of source first-action stability, not a statement about
spanning only a native image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoSignedSourceSpan
open CFSG.Models.Chevalley CFSGNormTwoOriginalPositiveSources
open CFSGNormTwoOriginalSourceInvolution CFSGNormTwoOriginalSourceBaseActions
open CFSGNormTwoOriginalSourceFamily CFSGSerreSignedRootWeights
open CFSGIntegerMatrixPairing
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Positive A)] [DecidableEq (Positive A)]

def rationalFamily (j : BasisIndex A) : RationalLie A := (vector A hd hs hp j).val

private theorem half_mem_span (neg : Bool) (j : HalfIndex A) :
    half A hd hs hp neg j∈Submodule.span ℚ (Set.range (rationalFamily A hd hs hp)) := by
  cases j with
  | inl a =>
    have h : generator A (.H a)∈Submodule.span ℚ (Set.range (rationalFamily A hd hs hp)) :=
      Submodule.subset_span ⟨.inl a,rfl⟩
    cases neg
    · exact h
    · exact Submodule.neg_mem _ h
  | inr k => exact Submodule.subset_span ⟨.inr (neg,k),rfl⟩

private theorem combination_mem_span (neg : Bool) (q : HalfIndex A→ℚ) :
    Fintype.linearCombination ℚ (half A hd hs hp neg) q∈
      Submodule.span ℚ (Set.range (rationalFamily A hd hs hp)) := by
  rw [Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ (fun j _=>Submodule.smul_mem _ _ (half_mem_span A hd hs hp neg j))

/-- Whole original rational quotient spanning; the original generators,
all actual positive paths and all actual negative paths are retained. -/
theorem span_eq_top (e f : Fin r→HalfIndex A→HalfIndex A→ℚ)
    (htables : ∀neg,
      (∀i j,⁅rootVector A neg i,half A hd hs hp neg j⁆=
        Fintype.linearCombination ℚ (half A hd hs hp neg) (e i j)) ∧
      (∀i j,0<halfHeight A j→⁅oppositeVector A neg i,half A hd hs hp neg j⁆=
        Fintype.linearCombination ℚ (half A hd hs hp neg) (f i j))) :
    Submodule.span ℚ (Set.range (rationalFamily A hd hs hp))=⊤ := by
  apply CFSGSerreFiniteRationalFirstActionSpan.span_eq_top
  · intro g
    cases g with
    | H a => exact Submodule.subset_span ⟨.inl a,rfl⟩
    | E a =>
      apply Submodule.subset_span
      refine ⟨.inr (false,simpleRoot A hd a),?_⟩
      exact congrArg Subtype.val (source_simple A hd hs hp false a)
    | F a =>
      apply Submodule.subset_span
      refine ⟨.inr (true,simpleRoot A hd a),?_⟩
      exact congrArg Subtype.val (source_simple A hd hs hp true a)
  · intro neg i j
    cases j with
    | inl a =>
      have hrow := (htables neg).1 i (.inl a)
      have hmem : ⁅rootVector A neg i,half A hd hs hp neg (.inl a)⁆∈
          Submodule.span ℚ (Set.range (rationalFamily A hd hs hp)) := by
        rw [hrow]
        exact combination_mem_span A hd hs hp neg _
      cases neg
      · exact hmem
      · have hn:=Submodule.neg_mem _ hmem
        simpa only [half,coroot,if_true,lie_neg,neg_neg] using hn
    | inr p =>
      obtain ⟨family,k⟩:=p
      have hp':0<halfHeight A (.inr k) := rootHeight_pos A k
      cases neg <;> cases family
      · change ⁅rootVector A false i,half A hd hs hp false (.inr k)⁆∈_
        rw [(htables false).1 i (.inr k)]
        exact combination_mem_span A hd hs hp false _
      · change ⁅oppositeVector A true i,half A hd hs hp true (.inr k)⁆∈_
        rw [(htables true).2 i (.inr k) hp']
        exact combination_mem_span A hd hs hp true _
      · change ⁅oppositeVector A false i,half A hd hs hp false (.inr k)⁆∈_
        rw [(htables false).2 i (.inr k) hp']
        exact combination_mem_span A hd hs hp false _
      · change ⁅rootVector A true i,half A hd hs hp true (.inr k)⁆∈_
        rw [(htables true).1 i (.inr k)]
        exact combination_mem_span A hd hs hp true _

end SymmetricSubgroupAsymptotics.CFSGNormTwoSignedSourceSpan
