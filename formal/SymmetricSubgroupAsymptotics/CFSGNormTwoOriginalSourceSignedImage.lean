import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalPositiveSources

/-! A genuine target Chevalley involution transports the original source
paths with their EXACT height sign. This is different from the checked
old source E/F exchange, which has no minus on the two simple roots.
The theorem needs only the actual target involution formulas on the
images of the original generators, never source faithfulness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceSignedImage
open CFSG.Models.Chevalley CFSGNormTwoOriginalPositiveSources
open CFSGIntegerMatrixPairing
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : RationalLie A→ₗ⁅ℚ⁆L) (omega : L≃ₗ⁅ℚ⁆L)

theorem image_chevalley (hroot : ∀neg i,
    omega (f (rootVector A neg i))= -f (rootVector A (!neg) i))
    (neg : Bool) (k : Positive A) :
    omega (f (source A hd hs hp neg k).val)=
      ((-1:ℤ)^rootHeight A k) • f (source A hd hs hp (!neg) k).val := by
  have hall : ∀n : ℕ,∀k : Positive A,rootHeight A k=n→∀neg,
      omega (f (source A hd hs hp neg k).val)=
        ((-1:ℤ)^rootHeight A k) • f (source A hd hs hp (!neg) k).val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk neg
      classical
      by_cases h : IsSimple A hd k
      · obtain ⟨i,hi⟩ := h
        have he : k=simpleRoot A hd i := Subtype.ext hi
        subst k
        have hh : rootHeight A (simpleRoot A hd i)=1 := by
          change (CFSGIntegerHeightSign.height (Pi.single i (1:ℤ))).toNat=1
          rw [CFSGNormTwoPositiveRootParents.height_coordinate]
          rfl
        rw [source_simple,source_simple,hh,pow_one,neg_one_zsmul]
        cases neg <;> exact hroot _ i
      · obtain ⟨i,p,hheight,_,_,hpath⟩ := source_parent_all_signs A hd hs hp k h
        have hfparent (delta : Bool) :
            f (source A hd hs hp delta k).val=
              ⁅f (rootVector A delta i),f (source A hd hs hp delta p).val⁆ := by
          rw [←hpath delta,LieHom.map_lie]
        rw [hfparent neg,LieEquiv.map_lie,hroot,
          ih (rootHeight A p) (by omega) p rfl neg,
          neg_lie,lie_zsmul,←hfparent (!neg),←hheight,pow_succ]
        simp only [mul_neg_one,neg_smul]
  exact hall (rootHeight A k) k rfl neg

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceSignedImage
