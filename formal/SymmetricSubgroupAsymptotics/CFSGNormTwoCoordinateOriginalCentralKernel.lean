import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageCentralKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGPerfectCentralKernel

/-! The actual original projective projection has exactly the centre as
kernel, proved from perfectness and integral generator identities. This
does not assume original Lie base-change faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCentralKernel
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckHeightData
open CFSGNormTwoGeckImageWeylWitness CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePerfect
open CFSGNormTwoCoordinateImageCentralKernel CFSGPerfectCentralKernel
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem originalProjection_kernel_eq_center
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (originalProjection A hd hs hp ho K i).ker =
      Subgroup.center (ElementaryGroup A hd hs hp ho K) := by
  let f := (imageAction A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K).rangeRestrict
  have hkf : f.ker =
      (imageAction A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K).ker :=
    MonoidHom.ker_rangeRestrict _
  have hker : f.ker ≤ Subgroup.center (ElementaryGroup A hd hs hp ho K) :=
    hkf.le.trans (imageAction_kernel_le_center A hd hs hp ho K)
  have he := projective_kernel_eq_center f
    (imageAction A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K).rangeRestrict_surjective
    (commutator_eq_top A hd hs hp ho K) hker
  let e := originalImageProjectiveEquiv A hd hs hp ho K i
  let q := QuotientGroup.mk' (Subgroup.center
    (imageGroup A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K))
  exact (MonoidHom.ker_mulEquiv_comp (q.comp f) e.symm).trans he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCentralKernel
