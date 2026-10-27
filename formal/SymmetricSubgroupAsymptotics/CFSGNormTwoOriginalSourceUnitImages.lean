import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalPositiveSources

/-! Source-side primitive-image induction. This is an INTERNAL bridge:
the target simple-root and root-sum unit identities must be actual proved
identities. The native Chevalley normalization supplies them for the
concrete exceptional target; they are not a new recognition/stability
premise of a classification endpoint. No source independence is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceUnitImages
open CFSG.Models.Chevalley CFSGNormTwoOriginalPositiveSources
open CFSGIntegerMatrixPairing
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : RationalLie A→ₗ⁅ℚ⁆L)

/-- The recursively defined ORIGINAL source has primitive unit image as
soon as its genuine target simple and root-parent brackets do. This uses
the source parent's actual defining bracket, not a matrix lift. -/
theorem image_is_unit_root (neg : Bool) (v : Positive A→L)
    (hsimple : ∀i,∃epsilon : ℤ,(epsilon=1 ∨ epsilon= -1) ∧
      f (rootVector A neg i)=epsilon • v (simpleRoot A hd i))
    (hparent : ∀(i : Fin r)(p k : Positive A),
      k.val.val=p.val.val+Pi.single i 1→
      ∃epsilon : ℤ,(epsilon=1 ∨ epsilon= -1) ∧
        ⁅f (rootVector A neg i),v p⁆=epsilon • v k)
    (k : Positive A) :
    ∃epsilon : ℤ,(epsilon=1 ∨ epsilon= -1) ∧
      f (source A hd hs hp neg k).val=epsilon • v k := by
  have hall : ∀n : ℕ,∀k : Positive A,rootHeight A k=n→
      ∃epsilon : ℤ,(epsilon=1 ∨ epsilon= -1) ∧
        f (source A hd hs hp neg k).val=epsilon • v k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk
      classical
      by_cases h : IsSimple A hd k
      · obtain ⟨i,hi⟩ := h
        have he : k=simpleRoot A hd i := Subtype.ext hi
        subst k
        rw [source_simple]
        cases neg <;> exact hsimple i
      · obtain ⟨i,p,hheight,hcoords,_,hpath⟩ := source_parent A hd hs hp neg k h
        obtain ⟨epsilon,hepsilon,himage⟩ := ih (rootHeight A p) (by omega) p rfl
        obtain ⟨eta,heta,hbracket⟩ := hparent i p k hcoords
        refine ⟨epsilon*eta,?_,?_⟩
        · rcases hepsilon with rfl|rfl <;> rcases heta with rfl|rfl <;> norm_num
        · rw [←hpath,LieHom.map_lie,himage,lie_zsmul,hbracket,smul_smul]
  exact hall (rootHeight A k) k rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceUnitImages
