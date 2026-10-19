import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceRangeRecognition
import SymmetricSubgroupAsymptotics.OriginalKernelSchreierCoordinateContainment
import SymmetricSubgroupAsymptotics.OriginalKernelModuleEquivTransport
import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalHeads

/-! Exact original cutspace coordinates from finite quotient-section
relations and three actual kernel vectors. This does not identify the
whole original group with a model or assume a split complement. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceSchreierKernelChart
open OriginalKernelModuleChart
open AlternatingEdgeOriginalProjectorHeads (Top)
open TetrahedralCutSpaceEdgeEmbedding (embedding)
variable {G ι : Type} [Group G] {pi : G →* Top}
    {A : Rep.{0} (ZMod 2) Top} (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ AlternatingEdgeOriginalProjectorHeads.beta)
    (hj : Function.Injective j)
    (g : ι → G) (hg : Subgroup.closure (Set.range g)=⊤)
    (r : Top → G) (hr : ∀ q,pi (r q)=q) (hr1 : r 1=1)
    (hwords : ∀ z : Top × ι,
      j (E.equiv.symm (schreierKernelGenerators g pi r hr z)).toAdd∈embedding.range)
    (hbasis : ∀ i : Fin 3,∃ x : pi.ker,
      j (E.equiv.symm x).toAdd=embedding (Pi.single i 1))

include hj hg hr1 hwords hbasis in
theorem range_eq : j.range=embedding.range := by
  apply TetrahedralCutSpaceEdgeEmbedding.range_eq_of_upper_and_basis
  · rintro _ ⟨v,rfl⟩
    have h := E.coordinates_mem_of_schreier j.toLinearMap embedding.range.toSubmodule
      g hg r hr hr1 hwords (E.equiv (Multiplicative.ofAdd v))
    simpa only [MulEquiv.symm_apply_apply] using h
  · intro i
    obtain ⟨x,hx⟩ := hbasis i
    exact ⟨(E.equiv.symm x).toAdd,hx⟩

 def chart : OriginalKernelModuleChart pi TetrahedralCutSpaceOriginalHeads.R :=
  E.ofModuleEquiv (TetrahedralCutSpaceEdgeEmbedding.moduleEquiv j hj
    (range_eq E j hj g hg r hr hr1 hwords hbasis))
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceSchreierKernelChart
