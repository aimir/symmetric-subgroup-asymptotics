import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceInvolution

/-! Actual source-side base actions for the uniform norm-two family.
The Cartan raises and simple-root lowerings are ORIGINAL Serre relations;
height-one roots are proved simple by the genuine positive-parent descent.
These are unconditional source inputs to the shared lowering induction,
not target tables transported through an assumed faithful realization. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceBaseActions
open CFSG.Models.Chevalley CFSGNormTwoOriginalPositiveSources
open CFSGNormTwoOriginalSourceInvolution CFSGSerreSignedRootWeights
open CFSGIntegerMatrixPairing CFSGNormTwoPositiveRootParents
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)

theorem rootHeight_pos (k : Positive A) : 0 < rootHeight A k := by
  have h := height_pos A k.val k.property
  dsimp only [rootHeight]
  omega

include hs hp in
/-- A positive root of height one is genuinely one coordinate simple root. -/
theorem isSimple_of_height_one (k : Positive A) (hk : rootHeight A k=1) :
    IsSimple A hd k := by
  classical
  by_contra hn
  obtain ⟨i,p,hheight,_,_,_⟩ := source_parent A hd hs hp false k hn
  have hpos := rootHeight_pos A p
  omega

def halfHeight : HalfIndex A→ℕ
  | .inl _=>0
  | .inr k=>rootHeight A k

def halfWeight (a : Fin r) : HalfIndex A→ℚ
  | .inl _=>0
  | .inr k=>weight A a k

theorem half_weight (neg : Bool) (a : Fin r) (j : HalfIndex A) :
    ⁅coroot A neg a,half A hd hs hp neg j⁆=
      halfWeight A a j • half A hd hs hp neg j := by
  cases j with
  | inl b =>
    simpa only [half,halfWeight,zero_smul] using coroots_commute A neg a b
  | inr k => exact source_weight A hd hs hp neg k a

private theorem simple_value (neg : Bool) (i : Fin r) :
    (source A hd hs hp neg (simpleRoot A hd i)).val=rootVector A neg i := by
  rw [source_simple]
  cases neg <;> rfl

/-- Height-zero Cartan raise, with the exact acting/Cartan index order. -/
theorem raising_cartan (neg : Bool) (i b : Fin r) :
    ⁅rootVector A neg i,half A hd hs hp neg (.inl b)⁆=
      (-(A b i:ℚ)) • half A hd hs hp neg (.inr (simpleRoot A hd i)) := by
  change ⁅rootVector A neg i,coroot A neg b⁆=
    (-(A b i:ℚ)) • (source A hd hs hp neg (simpleRoot A hd i)).val
  rw [simple_value,←lie_skew,coroot_root,neg_smul]

/-- Every simple lowering has precisely the original mixed Serre row. -/
theorem lowering_simple (neg : Bool) (a i : Fin r) :
    ⁅oppositeVector A neg a,half A hd hs hp neg (.inr (simpleRoot A hd i))⁆=
      if a=i then -half A hd hs hp neg (.inl a) else 0 := by
  change ⁅oppositeVector A neg a,(source A hd hs hp neg (simpleRoot A hd i)).val⁆=
    if a=i then -coroot A neg a else 0
  rw [simple_value]
  by_cases h : a=i
  · subst i
    rw [if_pos rfl]
    exact opposite_same A neg a
  · rw [if_neg h]
    exact opposite_distinct A neg a i h

/-- The genuine arbitrary height-one source base, with the simple node
identified internally rather than supplied by a source certificate. -/
theorem lowering_height_one (neg : Bool) (a : Fin r) (k : Positive A)
    (hk : rootHeight A k=1) :
    ∃i,k=simpleRoot A hd i ∧
      ⁅oppositeVector A neg a,(source A hd hs hp neg k).val⁆=
        if a=i then -coroot A neg a else 0 := by
  obtain ⟨i,hi⟩ := isSimple_of_height_one A hd hs hp k hk
  have he : k=simpleRoot A hd i := Subtype.ext hi
  refine ⟨i,he,?_⟩
  subst k
  exact lowering_simple A hd hs hp neg a i

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceBaseActions
