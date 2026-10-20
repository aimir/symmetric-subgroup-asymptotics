import SymmetricSubgroupAsymptotics.BinaryPairUniformQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import Mathlib.GroupTheory.Perm.Closure

/-! Original twelve-point pair extensions with cyclic or full symmetric
six-point image. The same actual elementary kernel chart gives quotient
socle bound two. Its correlations and affine offsets are unrestricted. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![0,1,3,5,7,9] p.1 else ![11,2,4,6,8,10] p.1
  invFun x := (![0,1,1,2,2,3,3,4,4,5,5,0] x,
    ![0,0,1,0,1,0,1,0,1,0,1,1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def cycle : Equiv.Perm (Fin 6) := finRotate 6
def swap : Equiv.Perm (Fin 6) := Equiv.swap 0 1

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

theorem uniform (g : U) (hg : F.top g = cycle) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    (F.top.rangeRestrict g) (fun _ : Fin 1 => (0 : Fin 6))
  intro i
  refine ⟨0,i.val,?_⟩
  change (F.top g ^ i.val) 0 = i
  rw [hg]
  revert i
  decide +kernel

theorem symmetric_range (g s : U) (hg : F.top g = cycle) (hs : F.top s = swap) :
    F.top.range = ⊤ := by
  have hgen : Subgroup.closure ({cycle,swap} : Set (Equiv.Perm (Fin 6))) = ⊤ := by
    simpa only [cycle,swap,show finRotate 6 (0 : Fin 6) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 6))
        (support_finRotate_of_le (by decide : 2 ≤ 6)) (0 : Fin 6)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro r hr
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · exact ⟨g,hg⟩
  · exact ⟨s,hs⟩

theorem cyclic_quotientSocle (g : U) (hg : F.top g = cycle)
    (himage : F.top.range ≤ Subgroup.zpowers cycle)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  letI : IsCyclic F.top.range := isCyclic_of_injective
    (Subgroup.inclusion himage) (Subgroup.inclusion_injective himage)
  apply F.quotientSocle_of_uniform_pair_action 1 1 (uniform F g hg) ?_ N
  intro L hL
  letI := hL
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic L

theorem symmetric_quotientSocle (g s : U) (hg : F.top g = cycle) (hs : F.top s = swap)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  apply F.quotientSocle_of_uniform_pair_action 1 1 (uniform F g hg) ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* Equiv.Perm (Fin 6) :=
    (MulEquiv.subgroupCongr (symmetric_range F g s hg hs)).trans Subgroup.topEquiv
  apply CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 1 ?_ L
  intro M hM
  letI := hM
  obtain ⟨x,hx⟩ := normal_generating_singletons_of_finite_normal_total
    (AlternatingSymmetricNormalChain.symmetric_normal_total (by norm_num : 5 ≤ Nat.card (Fin 6))) M hM
  exact normalGen_le_of_fin_tuple x hx

end SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles

end
