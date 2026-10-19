import SymmetricSubgroupAsymptotics.ProductQuartetAffineLinearProjection
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop
import SymmetricSubgroupAsymptotics.OddCubicSubgroupLift
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelConsequences

/-! The whole actual nonzero odd linear kernel lifts to an original cubic
subgroup fixing the four quartet labels and moving every local fibre.
Correlations between local odd images are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

include C in
 theorem exists_quartet_odd_subgroup [MulAction.IsPretransitive T X]
    (hO : oddKernel C.quartetLinearImage≠⊥) :
    ∃ (P : Subgroup T) (hfix : P≤C.top.ker),IsPGroup 3 P ∧
      (∀ p : P,p^3=1) ∧ ∀ i : Fin 4,∃ p : P,
        C.kernelCoordinate i ⟨p.val,hfix p.property⟩≠1 := by
  let D := C.quartetLinearImage
  let pi := C.quartetLinearMap
  let O := oddKernel D
  have htrans : ∀ i k : Fin 4,∃ d : D,(d : Frame).right • i=k := by
    intro i k
    obtain ⟨g,hg⟩ := C.top_range_transitive
      (fun x y => MulAction.exists_smul_eq T x y) i k
    obtain ⟨u,hu⟩ := g.property
    refine ⟨pi u,?_⟩
    change C.top u i=k
    rw [hu]
    exact hg
  obtain ⟨P,hP,hPO,hmap,hcubic⟩ := OddCubicSubgroupLift.exists_lift pi
    C.quartetLinearMap_surjective C.quartetLinearMap_kernel_binary O
    (isPGroup_three D) (cube_eq_one D)
  have hfix : P≤C.top.ker := by
    intro p hp
    have ht := top_one D (⟨pi p,hPO hp⟩ : O)
    change C.top p=1
    exact ht
  refine ⟨P,hfix,hP,hcubic,?_⟩
  intro i
  obtain ⟨o,ho⟩ := all_local_nontrivial D hO htrans i
  have hm : o.val∈P.map pi := hmap.symm ▸ o.property
  obtain ⟨p,hp,hpo⟩ := hm
  refine ⟨⟨p,hp⟩,?_⟩
  intro hcoord
  apply ho
  change (o.val : Frame).left i=1
  rw [←hpo]
  have h := C.quartetLinearMap_local p (hfix hp) i
  rw [hcoord,map_one] at h
  exact h

end SymmetricSubgroupAsymptotics.ProductBlockFrame
