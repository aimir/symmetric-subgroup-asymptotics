import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPositiveContainment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPGroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection

/-! Intrinsic containment of an original projected root subgroup in the
literal original positive Sylow detects exactly positive lattice roots.
This uses the proved separation of ALL p-elements under the SAME central
projection, rather than lifting an arbitrary automorphism to matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootContainment
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootPositiveContainment CFSGNormTwoCoordinateRootPGroup
open CFSGNormTwoCoordinateOriginalCentralKernel CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinatePositiveSylow CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositivePGroup CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem originalFullRootLine_le_positive_iff
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→
        wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A) :
    originalFullRootLine A hd hs hp ho K i k≤originalPositive A hd hs hp ho K i↔
      ∀j,0≤k.val j := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := PositiveGroup A hd hs hp ho K
  let UH := U.subgroupOf H
  let R := (rootSubgroup A hd hs hp ho K k).subgroupOf H
  let f := originalProjection A hd hs hp ho K i
  let P := canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p
  have hP : Function.Injective (f.comp (P : Subgroup H).subtype) := by
    intro x y he
    have hh := originalProjection_positive_injective A hd hs hp ho K p i
      (a₁:=⟨x.val.val,x.property⟩) (a₂:=⟨y.val.val,y.property⟩) he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : U=>z.val) hh))
  have hker : f.ker≤Subgroup.center H := (originalProjection_kernel_eq_center A hd hs hp ho K i).le
  have hjoin : U⊔rootGroup A hs hp b₀ s₀ K true=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hUp : IsPGroup p UH := (rootGroup_isPGroup A hd hs hp ho s₀ K p false).of_injective
    (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hUH).injective
  have hRp : IsPGroup p R := rootSubgroupInElementary_isPGroup A hd hs hp ho K p k
  have hUmap : UH.map f=originalPositive A hd hs hp ho K i := by
    rw [originalPositive,MonoidHom.range_comp,positiveInclusion,Subgroup.inclusion_range]
  have he := CFSGCentralKernelPSubgroupReflection.map_le_map_iff f P hP hker R UH hRp hUp
  change R.map f≤originalPositive A hd hs hp ho K i↔_
  rw [←hUmap,he]
  constructor
  · intro h
    apply (rootSubgroup_le_positive_iff A hd hs hp ho K k).mp
    intro x hx
    exact h (show (⟨x,rootSubgroup_le_elementary A hd hs hp ho K k hx⟩ : H)∈R from hx)
  · intro hk x hx
    exact positive_root_subgroup_le A hd hs hp ho K k hk hx

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootContainment
