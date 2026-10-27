import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalAmbientKernelCentral
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootNilpotence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPerfect
import SymmetricSubgroupAsymptotics.CFSGSerreModelLieAutomorphisms
import SymmetricSubgroupAsymptotics.PerfectLieCentralDeviation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv

/-! Characteristic-UNIFORM original D projective recognition. The original
source Lie algebra is perfect and its actual natural realization has central
kernel. Genuine model Lie automorphisms are therefore detected by their
natural image action. Original/natural range equality supplies surjectivity.
No source/matrix faithfulness, old simplicity or recognition premise occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalProjectiveEquivalenceAllFields
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K] (r : ℕ) (hr : 4 ≤ r)

include hr in
theorem dividedPower_cutoff (neg : Bool) (i : Fin r) (k : ℕ) (hk : 4 ≤ k) :
    integralOperator (CartanMatrix.D r) neg i k=0 :=
  CFSGOrthogonalDOriginalRootNilpotence.integralOperator_large r hr neg i k (by omega)

theorem eq_one_of_image (g : Model (CartanMatrix.D r) K)
    (hg : orthogonalImageRepresentation K r hr g=1) : g=1 := by
  let f : Space (CartanMatrix.D r) K→ₗ⁅K⁆Space (CartanMatrix.D r) K:=
    CFSGSerreModelLieAutomorphisms.modelLieHom (CartanMatrix.D r) K (dividedPower_cutoff r hr) g
  let beta:=CFSGSerreSquareZeroLieRealization.baseChangeLieHom (realizationData r hr) K
  have himage (x : Space (CartanMatrix.D r) K) : beta (f x)=beta x := by
    have h:=CFSGSerreSquareZeroMatrix.imageRepresentation_intertwines (realizationData r hr) K g x
    rw [hg] at h
    change orthogonalBaseChange K r hr x=orthogonalBaseChange K r hr (g.val x) at h
    exact h.symm
  have hf : f=LieHom.id :=
    PerfectLieCentralDeviation.eq_id_of_central_kernel beta f
      (CFSGOrthogonalDOriginalPerfect.bracketSpan_eq_top r hr K)
      (CFSGOrthogonalDOriginalAmbientKernelCentral.kernel_central r hr K) himage
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h:=congrArg (fun F : Space (CartanMatrix.D r) K→ₗ⁅K⁆Space (CartanMatrix.D r) K=>F x) hf
  exact h

theorem imageRepresentation_injective : Function.Injective (orthogonalImageRepresentation K r hr) := by
  apply (orthogonalImageRepresentation K r hr).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  exact Subgroup.mem_bot.mpr (eq_one_of_image K r hr g (MonoidHom.mem_ker.mp hg))

theorem sourceActionIntoElementaryRange_injective :
    Function.Injective (sourceActionIntoElementaryRange K r hr) := by
  intro g h he
  exact imageRepresentation_injective K r hr (congrArg Subtype.val he)

theorem sourceToElementaryProjective_injective (s : ℕ) :
    Function.Injective (sourceToElementaryProjective K s) := by
  intro g h he
  apply sourceActionIntoElementaryRange_injective K (s+4) (by omega)
  exact (elementaryProjectiveActionEquiv K s).symm.injective he

def sourceEquivElementaryProjective (s : ℕ) :
    Model (CartanMatrix.D (s+4)) K≃*elementaryProjective K (s+4) :=
  MulEquiv.ofBijective (sourceToElementaryProjective K s)
    ⟨sourceToElementaryProjective_injective K s,
      sourceToElementaryProjective_surjective K s⟩

def projectiveEquivElementaryProjective (s : ℕ) :
    Projective (CartanMatrix.D (s+4)) K≃*elementaryProjective K (s+4) :=
  (CFSGCenterQuotientEquiv.equiv (sourceEquivElementaryProjective K s)).trans
    ((QuotientGroup.quotientMulEquivOfEq (elementaryProjective_center_eq_bot K s)).trans
      QuotientGroup.quotientBot)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalProjectiveEquivalenceAllFields
