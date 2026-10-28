import SymmetricSubgroupAsymptotics.CFSGNormTwoSignedRootIndex
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns

/-! Exact completeness of literal signed positive-root coordinates, from
the actual norm-two one-sign theorem. No exceptional root census, source
basis or group-recognition theorem is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoSignedRootIndexCover
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoOriginalPositiveSources
open CFSGNormTwoSignedRootIndex
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)

include hd hs hp ho in
theorem signedRoot_surjective : Function.Surjective (signedRoot A) := by
  intro q
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
    (fun a=>by rw [hd a];exact even_two) ho q.val q.property with hpos|hneg
  · exact ⟨(false,⟨q,hpos⟩),rfl⟩
  · have hop : ∀a,0≤(opposite A q).val a := fun a=>neg_nonneg.mpr (hneg a)
    refine ⟨(true,⟨opposite A q,hop⟩),?_⟩
    exact opposite_involutive A q

include hd hs hp ho in
theorem familyIndex_surjective : Function.Surjective (familyIndex A) := by
  intro j
  cases j with
  | inl q =>
    obtain ⟨p,hp'⟩:=signedRoot_surjective A hd hs hp ho q
    exact ⟨.inr p,congrArg Sum.inl hp'⟩
  | inr a => exact ⟨.inl a,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoSignedRootIndexCover
