import SymmetricSubgroupAsymptotics.CFSGSerreModelLieAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticLieRealization
import SymmetricSubgroupAsymptotics.PerfectLieCentralDeviation

/-! A central Lie-realization kernel is enough to make the actual
ORIGINAL group action on its image faithful, provided the genuine source
Lie algebra is perfect. All hypotheses here are internal algebraic data;
the concrete E6 consumer constructs them without a final callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticImageFaithfulness
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix

/-- Perfectness kills central deviations of every actual model element.
Full ambient Lie-injectivity is deliberately not a hypothesis. -/
theorem imageRepresentation_injective
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : Data A I) (K : Type) [Field K]
    (hge : ∀ neg i k, 4 ≤ k → integralOperator A neg i k = 0)
    (hperfect : Submodule.span K
      (Set.range (fun xy : Space A K × Space A K => ⁅xy.1, xy.2⁆)) = ⊤)
    (hker : ∀ z : Space A K, baseChange D K z = 0 → ∀ y : Space A K, ⁅z, y⁆ = 0) :
    Function.Injective (imageRepresentation D K) := by
  apply (imageRepresentation D K).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hrep : imageRepresentation D K g = 1 := hg
  have himage (x : Space A K) : baseChange D K (g.val x) = baseChange D K x := by
    have h := imageRepresentation_intertwines D K g x
    rw [hrep] at h
    exact h.symm
  have heq := PerfectLieCentralDeviation.eq_id_of_central_kernel
    (CFSGSerreQuadraticLieRealization.baseChangeLieHom D K)
    (CFSGSerreModelLieAutomorphisms.modelLieHom A K hge g)
    hperfect hker himage
  change g = 1
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f : Space A K →ₗ⁅K⁆ Space A K => f x) heq

/-- The equivalence is onto the actual same-image action range; no
independently named target group or source simplicity is used. -/
def originalImageEquiv
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : Data A I) (K : Type) [Field K]
    (hge : ∀ neg i k, 4 ≤ k → integralOperator A neg i k = 0)
    (hperfect : Submodule.span K
      (Set.range (fun xy : Space A K × Space A K => ⁅xy.1, xy.2⁆)) = ⊤)
    (hker : ∀ z : Space A K, baseChange D K z = 0 → ∀ y : Space A K, ⁅z, y⁆ = 0) :
    Model A K ≃* (imageRepresentation D K).range :=
  MulEquiv.ofBijective (imageRepresentation D K).rangeRestrict
    ⟨fun x y h => imageRepresentation_injective D K hge hperfect hker
      (congrArg Subtype.val h), (imageRepresentation D K).rangeRestrict_surjective⟩

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticImageFaithfulness
