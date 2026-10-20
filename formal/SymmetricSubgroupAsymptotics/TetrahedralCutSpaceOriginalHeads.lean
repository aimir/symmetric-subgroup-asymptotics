import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceRepresentation
import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalSocleCoinvariance
import SymmetricSubgroupAsymptotics.OriginalKernelSectionUniform
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalHeads
open OriginalKernelModuleChart
open AlternatingEdgeOriginalProjectorHeads (Top a t)
open TetrahedralCutSpaceCoinvariantHead (A B D0 D1)
open TetrahedralCutSpaceRepresentation (beta beta_a beta_t1 beta_t2)
abbrev R : Rep (ZMod 2) Top := Rep.of beta

private theorem t_mem : ∀ d,t d∈alternatingGroup.kleinFour (Fin 4) := by
  intro d
  rw [← NaturalA4ScalarFourHead.top_ker]
  change NaturalA4ScalarFourHead.top (t d)=1
  revert d
  decide +kernel

theorem outside_heads {G : Type} [Group G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (E : OriginalKernelModuleChart pi R) (N : Subgroup G) [N.Normal] :
    let tau := (E.sectionRepresentation pi R N).ρ.comp (sectionTop pi N hpi)
    finiteGroupSocle (G ⧸ N)≤(base pi N).ker ∨
      (Module.finrank (ZMod 2) (LinearMap.range (1+tau a+(tau a)^2))≤1 ∧
       Module.finrank (ZMod 2) (LinearMap.range (tau a+(tau a)^2))≤0) := by
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi R N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi R N)
    infer_instance
  let tau := (E.sectionRepresentation pi R N).ρ.comp (sectionTop pi N hpi)
  let q := E.sectionProjectionOnBase pi R N hpi
  have hq := E.sectionProjectionOnBase_surjective pi R N hpi
  rcases AlternatingEdgeOriginalSocleCoinvariance.dichotomy pi hpi R E N with hi | hc
  · exact Or.inl hi
  right
  have hqt : ∀ d,tau (t d)=1 := by
    intro d
    exact congrArg Units.val (hc (t_mem d))
  have hk (d : Fin 3) (v : TetrahedralCutSpaceCoinvariantHead.Vector) :
      q ((1+beta (t d)) v)=0 := by
    change q (v+beta (t d) v)=0
    rw [map_add]
    have h := Representation.IntertwiningMap.isIntertwining _ _ q (t d) v
    change q (beta (t d) v)=tau (t d) (q v) at h
    rw [h,hqt]
    change q v+q v=0
    rw [← two_smul (ZMod 2),show (2 : ZMod 2)=0 by decide,zero_smul]
  have hD0 : ∀ v,q (D0 v)=0 := by
    intro v
    change q (v+B v)=0
    rw [← beta_t1]
    exact hk 1 v
  have hD1 : ∀ v,q (D1 v)=0 := by
    intro v
    rw [← beta_t2]
    exact hk 2 v
  apply TetrahedralCutSpaceCoinvariantHead.projector_heads q.toLinearMap hq hD0 hD1 (tau a)
  intro v
  rw [← beta_a]
  exact Representation.IntertwiningMap.isIntertwining _ _ q a v
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalHeads
