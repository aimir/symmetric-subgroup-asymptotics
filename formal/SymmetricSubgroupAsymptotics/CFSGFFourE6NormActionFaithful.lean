import SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalResidual
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormKernelPositiveScalars

/-! Faithfulness of the actual norm26 action of the literal folded F4
matrix group in characteristic two. The kernel is first proved diagonal;
fixed norm coordinates and six actual commuting simple units kill the
remaining diagonal entries by the checked 26-edge forest. No ordinary
F4 simplicity or original-source correspondence is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionFaithful
open CFSGFFourSerreMatrices CFSGTwistedE6GeckDiagramCovariance
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormActionKernelUpper
open CFSGFFourE6NormKernelPositiveScalars CFSGFFourE6NormDiagonalResidual
open CFSGFFourE6FixedGeneratedGroup CFSGTwistedE6GeckRelativeRootGenerated
open CFSGSerreQuadraticMatrix
variable (K:Type) [Field K] [Finite K] [CharP K 2]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

theorem generated_norm_kernel_eq_one (g:J) (hg:g∈(generatedNormAction K).ker) : g=1 := by
  have hdiag:(g.val:Matrix Index Index K).IsDiag:=kernel_isDiag K g hg
  have hnorm (k:PairIndex) :
      (g.val:Matrix Index Index K)*ᵥ(normBasis K k).val=(normBasis K k).val := by
    have hk:normAction K (generatedToFolded K g)=1:=hg
    have h:=congrArg (fun f:characteristicNormImage K≃ₗ[K]characteristicNormImage K=>f (normBasis K k)) hk
    have hv:=congrArg (fun x:characteristicNormImage K=>x.val) h
    change (g.val:Matrix Index Index K)*ᵥ(normBasis K k).val=(normBasis K k).val at hv
    exact hv
  have hcomm (i:Fin 6) :
      (g.val:Matrix Index Index K)*(canonicalRoot rawData K false i 1:Matrix Index Index K)=
        (canonicalRoot rawData K false i 1:Matrix Index Index K)*(g.val:Matrix Index Index K) := by
    have he:g.val*canonicalRoot rawData K false i 1=canonicalRoot rawData K false i 1*g.val :=
      kernel_commutes_ambient_positive K g hg i 1
    exact congrArg (fun u:(Matrix Index Index K)ˣ=>(u:Matrix Index Index K)) he
  have hM:(g.val:Matrix Index Index K)=1:=diagonal_eq_one K _ hdiag hnorm hcomm
  apply Subtype.ext
  apply Units.ext
  exact hM

theorem generatedNormAction_injective : Function.Injective (generatedNormAction K) := by
  intro g h he
  have hk:generatedNormAction K (g⁻¹*h)=1 := by
    rw [map_mul,map_inv,he,inv_mul_cancel]
  exact inv_mul_eq_one.mp (generated_norm_kernel_eq_one K (g⁻¹*h) hk)

theorem normAction_injective : Function.Injective (normAction K) := by
  intro g h he
  have hle:canonicalElementaryGroup realizationData K≤J:=(fixedRootGenerated_eq_folded K).symm.le
  let gJ:J:=⟨g.val,hle g.property⟩
  let hJ:J:=⟨h.val,hle h.property⟩
  have heJ:generatedNormAction K gJ=generatedNormAction K hJ:=he
  have hgh:=generatedNormAction_injective K heJ
  have hv:=congrArg (fun u:J=>u.val) hgh
  exact Subtype.ext hv

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionFaithful
