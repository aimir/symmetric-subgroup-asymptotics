import SymmetricSubgroupAsymptotics.Selected1542FirstMonolith
import SymmetricSubgroupAsymptotics.QuotientRetainedHom
import SymmetricSubgroupAsymptotics.CentralPrimeExponentSocle

/-! The first quotient retains the literal involution and the original N8
as its second axis. Its binary kernel is the actual image of the original K. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

theorem originalCentralInvolution_central :
    originalCentralInvolution∈Subgroup.center Original := by
  have hc : Subgroup.closure (Set.range source)≤
      Subgroup.centralizer ({originalCentralInvolution} : Set Original) := by
    apply (Subgroup.closure_le (Subgroup.centralizer ({originalCentralInvolution} : Set Original))).mpr
    rintro _ ⟨j,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have he : z=originalCentralInvolution := Set.mem_singleton_iff.mp hz
    rw [he]
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact firstCenter_z_central j x
  rw [source_generates] at hc
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hg := hc (show g∈(⊤ : Subgroup Original) from trivial)
  exact (Subgroup.mem_centralizer_iff.mp hg originalCentralInvolution (by simp)).symm

def originalFirstAxis : Subgroup Original := Subgroup.zpowers originalCentralInvolution

instance originalFirstAxis_normal : originalFirstAxis.Normal :=
  CentralPrimeExponentSocle.normal_of_le_center originalFirstAxis (Subgroup.zpowers_le.mpr originalCentralInvolution_central)

theorem originalFirstAxis_mem_iff (g : Original) :
    g∈originalFirstAxis ↔ g=1 ∨ g=originalCentralInvolution := by
  constructor
  · intro hg
    have hc : originalFirstAxis≤Subgroup.centralizer (originalBinaryKernel : Set Original) := by
      apply Subgroup.zpowers_le.mpr
      apply Subgroup.mem_centralizer_iff.mpr
      intro k _
      exact Subgroup.mem_center_iff.mp originalCentralInvolution_central k
    exact originalBinaryKernel_centralizer g (hc hg)
  · rintro (rfl | rfl)
    · exact originalFirstAxis.one_mem
    · exact Subgroup.mem_zpowers originalCentralInvolution

theorem originalFirstAxis_le_originalNormal : originalFirstAxis≤originalNormal := by
  apply Subgroup.zpowers_le.mpr
  have he : originalCentralInvolution=normalOriginal 3 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change preimageElements 26 x=normalElements 3 x
    revert x
    decide +kernel
  rw [he]
  exact (normalTable.chart 3).property

def FirstQuotient := Original ⧸ originalFirstAxis

instance : Group FirstQuotient := inferInstanceAs (Group (Original ⧸ originalFirstAxis))
instance : Finite FirstQuotient := inferInstanceAs (Finite (Original ⧸ originalFirstAxis))

theorem originalFirstAxis_le_binaryKernel : originalFirstAxis≤originalBinaryKernel :=
  Subgroup.zpowers_le.mpr originalCentralInvolution_mem

def firstQuotientCubic : FirstQuotient →* CyclicThree :=
  QuotientRetainedHom.descend originalCubic originalFirstAxis originalFirstAxis_le_binaryKernel

theorem firstQuotientCubic_apply (g : Original) :
    firstQuotientCubic (QuotientGroup.mk' originalFirstAxis g)=originalCubic g := rfl

def firstQuotientBinaryKernel : Subgroup FirstQuotient := firstQuotientCubic.ker

theorem firstQuotientBinaryKernel_image : firstQuotientBinaryKernel=
    originalBinaryKernel.map (QuotientGroup.mk' originalFirstAxis) :=
  QuotientRetainedHom.descend_kernel originalCubic originalFirstAxis originalFirstAxis_le_binaryKernel

theorem firstQuotientBinaryKernel_isPGroup : IsPGroup 2 firstQuotientBinaryKernel := by
  rw [firstQuotientBinaryKernel_image]
  exact originalBinaryKernel_isPGroup.map (QuotientGroup.mk' originalFirstAxis)

def secondAxis : Subgroup FirstQuotient :=
  originalNormal.map (QuotientGroup.mk' originalFirstAxis)

instance secondAxis_normal : secondAxis.Normal :=
  inferInstanceAs ((originalNormal.map (QuotientGroup.mk' originalFirstAxis)).Normal)

theorem mkFirst_eq_one_iff (g : Original) :
    QuotientGroup.mk' originalFirstAxis g=1 ↔ g=1 ∨ g=originalCentralInvolution := by
  change (g : Original ⧸ originalFirstAxis)=1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact originalFirstAxis_mem_iff g

theorem mkFirst_involution : QuotientGroup.mk' originalFirstAxis originalCentralInvolution=1 :=
  (mkFirst_eq_one_iff _).mpr (Or.inr rfl)

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
