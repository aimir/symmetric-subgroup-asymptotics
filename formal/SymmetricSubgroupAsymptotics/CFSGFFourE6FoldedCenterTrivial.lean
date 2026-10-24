import SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedCenterScalars
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoColumnRigidity
import SymmetricSubgroupAsymptotics.CFSGFFourE6ActionCentralKernel

/-! The actual folded matrix group has trivial centre in characteristic
two. Its central elements fix Cartan columns and commute with every
ambient signed simple unit; actual Weyl root-column transport kills the
entire diagonal residual. Consequently the SAME original image action
is faithful, without an ordinary F4 simplicity assumption.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedCenterTrivial
open CFSGFFourSerreMatrices CFSGFFourE6FoldedCenterScalars
open CFSGFFourE6SignedFixedInclusion CFSGFFourE6ActionCentralKernel
open CFSGE6GeckFixedPairNormalizer CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormalizerWordIdentity
open CFSGSignedCartanReflections CFSGSerreQuadraticMatrix
variable (K:Type) [Field K] [Finite K]
local notation "F" => canonicalElementaryGroup realizationData K

theorem center_commutes_ambient_signed (g:F) (hg:g∈Subgroup.center F)
    (neg:Bool) (i:Fin 6) (t:K) : Commute g.val (canonicalRoot rawData K neg i t) := by
  let C:=Subgroup.centralizer ({g.val}:Set (Matrix GeckIndex GeckIndex K)ˣ)
  have hpos:Positive K≤C := by
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨⟨j,s⟩,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (center_commutes_ambient_positive K g hg j s).eq.symm
  have hW:relativeOpposition K∈C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    let w:F:=⟨relativeOpposition K,relativeOpposition_mem_folded K⟩
    exact congrArg (fun z:F=>z.val) (Subgroup.mem_center_iff.mp hg w)
  have hneg:Negative K≤C := by
    have hsign:(Positive K).map (MulAut.conj (relativeOpposition K)).toMonoidHom=Negative K:=
      positive_image_eq_negative K
    rw [←hsign]
    rintro u ⟨v,hv,rfl⟩
    exact C.mul_mem (C.mul_mem hW (hpos hv)) (C.inv_mem hW)
  cases neg with
  | false=>exact center_commutes_ambient_positive K g hg i t
  | true=>
    have h:canonicalRoot rawData K true i t∈C:=hneg (Subgroup.subset_closure ⟨(i,t),rfl⟩)
    exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

theorem center_element_eq_one [CharP K 2] (g:F) (hg:g∈Subgroup.center F) : g=1 := by
  have hpair:=center_mem_pairNormalizer K g hg
  have hD:=pairNormalizer_le_diagonalNormalizer K (RingEquiv.refl K) hpair
  have hdiag:(g.val:Matrix Index Index K).IsDiag:=pairNormalizer_isDiag K (RingEquiv.refl K) g.val hpair
  have hcartan:∀j:E6Base.support,(g.val:Matrix Index Index K)*ᵥPi.single (.inl j) 1=Pi.single (.inl j) 1 :=
    CFSGNormTwoCoordinateDiagonalCartan.diagonalNormalizer_le_cartanFixer
      CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos K E6Signs E6_signs_square E6_signs_cartan
      (E6_normalizer_word_identity K) (by decide) hD
  have hunit:g.val=1:=CFSGNormTwoCoordinateCharTwoColumnRigidity.diagonal_eq_one
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K 0 g.val hdiag hcartan
    (center_commutes_ambient_signed K g hg)
  exact Subtype.ext hunit

theorem center_eq_bot [CharP K 2] : Subgroup.center F=⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  exact Subgroup.mem_bot.mpr (center_element_eq_one K g hg)

theorem fullNaturalImageAction_injective [CharP K 2] : Function.Injective (fullNaturalImageAction K) := by
  intro g h he
  have hk:g⁻¹*h∈(fullNaturalImageAction K).ker := by
    change fullNaturalImageAction K (g⁻¹*h)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hz:=fullNaturalImageAction_kernel_le_center K hk
  exact inv_mul_eq_one.mp (center_element_eq_one K (g⁻¹*h) hz)

end SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedCenterTrivial
