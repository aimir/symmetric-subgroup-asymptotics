import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalRootGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCenter
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup
import SymmetricSubgroupAsymptotics.CFSGPGroupNormalCenterIntersection

/-! Actual U-injectivity for EVERY nontrivial surjective quotient of the
canonical matrix group, in rank at least two over a finite field. A
nontrivial p-kernel would meet the proved dominant-root centre, then the
actual torus saturation and normal-root generation force the whole group
into the kernel. No representation faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateNormalRootGeneration
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveCenter
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePGroup CFSGPGroupNormalCenterIntersection
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def positiveInclusion (K : Type) [Field K] :
    PositiveGroup A hd hs hp ho K→*ElementaryGroup A hd hs hp ho K :=
  Subgroup.inclusion (by
    change rootGroup A hs hp b₀ s₀ K false≤
      CFSGSerreQuadraticMatrix.canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K
    rw [←positive_sup_negative A hs hp b₀ s₀ K]
    exact le_sup_left)

theorem positive_quotient_injective (K : Type) [Field K] [Finite K]
    [Nontrivial (Fin r)] (p : ℕ) [Fact p.Prime] [CharP K p]
    {Q : Type*} [Group Q] [Nontrivial Q]
    (f : ElementaryGroup A hd hs hp ho K→*Q) (hf : Function.Surjective f) :
    Function.Injective (f.comp (positiveInclusion A hd hs hp ho K)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let q := f.comp (positiveInclusion A hd hs hp ho K)
  letI : q.ker.Normal := q.normal_ker
  letI : f.ker.Normal := f.normal_ker
  have hU : IsPGroup p (PositiveGroup A hd hs hp ho K) :=
    rootGroup_isPGroup A hd hs hp ho s₀ K p false
  have hbot : q.ker=⊥ := by
    apply normal_eq_bot_of_center_intersection hU q.ker
    intro z hz hzc
    by_contra hzne
    obtain ⟨θ,hθ,hdom,hcenter⟩ := exists_root_subgroup_center A hd hs hp ho K
    have hzroot : z.val∈CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K θ := by
      have hh := hzc
      rw [hcenter] at hh
      exact hh
    obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K θ z.val).mp hzroot
    have ha0 : a≠0 := by
      intro he
      rw [he,selectedRootElement_zero] at ha
      apply hzne
      apply Subtype.ext
      exact ha.symm
    have he : elementarySelectedRootHom A hd hs hp ho K θ (Multiplicative.ofAdd a)=
        positiveInclusion A hd hs hp ho K z := by
      apply Subtype.ext
      exact ha
    have hrootN : elementarySelectedRootHom A hd hs hp ho K θ (Multiplicative.ofAdd a)∈f.ker := by
      rw [he]
      exact hz
    have htop := normal_eq_top_of_nonzero_dominant_root A hd hs hp ho K f.ker θ hθ hdom a ha0 hrootN
    obtain ⟨y,hy⟩ := exists_ne (1 : Q)
    obtain ⟨x,hx⟩ := hf y
    have hxker : x∈f.ker := by rw [htop];exact Subgroup.mem_top x
    have hfx : f x=1 := hxker
    exact hy (hx.symm.trans hfx)
  exact q.ker_eq_bot_iff.mp hbot

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveQuotientInjectivity
