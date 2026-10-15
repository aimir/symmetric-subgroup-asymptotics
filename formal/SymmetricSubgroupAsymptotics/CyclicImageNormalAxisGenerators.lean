import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles

/-! One normal generator from a cyclic image and one cyclic exceptional
axis. Every normal outside that axis contains the actual kernel. Adjust
a lift by a kernel element when necessary to force its normal closure
outside the axis. This keeps the original projection and kernel literal. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_singletons_of_cyclic_image_axis
    {G Q : Type} [Group G] [Finite G] [Group Q] [IsCyclic Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (C : Subgroup G) [IsCyclic C]
    (hkerC : ¬ pi.ker ≤ C)
    (haxes : ∀ N : Subgroup G, N.Normal → pi.ker ≤ N ∨ N ≤ C) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 1 → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  by_cases hNC : N ≤ C
  · letI : IsCyclic N := isCyclic_of_injective (Subgroup.inclusion hNC)
      (Subgroup.inclusion_injective hNC)
    exact exists_normal_generating_tuple_of_normalGen_le N
      (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic N)
  have hkerN : pi.ker ≤ N := (haxes N hN).resolve_right hNC
  letI : Finite Q := Finite.of_surjective pi hpi
  obtain ⟨y,hy⟩ := normal_generating_singletons_of_isCyclic
    (N.map pi) (hN.map pi hpi)
  have hy0 : y 0 ∈ N.map pi := by
    rw [← hy]
    exact Subgroup.subset_normalClosure (Set.mem_range_self 0)
  obtain ⟨z,hz,hzimage⟩ := hy0
  obtain ⟨v,hvker,hvC⟩ := Set.not_subset.mp hkerC
  have hlift : ∃ w : G, w ∈ N ∧ pi w = y 0 ∧ w ∉ C := by
    by_cases hzC : z ∈ C
    · refine ⟨z*v,N.mul_mem hz (hkerN hvker),?_,?_⟩
      · rw [map_mul,MonoidHom.mem_ker.mp hvker,mul_one,hzimage]
      · intro h
        apply hvC
        simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem hzC) h
    · exact ⟨z,hz,hzimage,hzC⟩
  obtain ⟨w,_hwN,hwimage,hwC⟩ := hlift
  let x : Fin 1 → G := fun _ => w
  let L := Subgroup.normalClosure (Set.range x)
  letI : L.Normal := by dsimp [L]; infer_instance
  have hwL : w ∈ L := Subgroup.subset_normalClosure (Set.mem_range_self (f := x) 0)
  have hkerL : pi.ker ≤ L := (haxes L inferInstance).resolve_right
    (fun h => hwC (h hwL))
  have himage : pi '' Set.range x = Set.range y := by
    ext q
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨0,hwimage.symm⟩
    · rintro ⟨i,rfl⟩
      refine ⟨w,Set.mem_range_self (f := x) 0,?_⟩
      exact hwimage.trans (congrArg y (Subsingleton.elim 0 i))
  have hmap : L.map pi = N.map pi := by
    dsimp [L]
    rw [Subgroup.map_normalClosure _ _ hpi,himage,hy]
  refine ⟨x,?_⟩
  change L = N
  calc
    L = (L.map pi).comap pi := (Subgroup.comap_map_eq_self hkerL).symm
    _ = (N.map pi).comap pi := by rw [hmap]
    _ = N := Subgroup.comap_map_eq_self hkerN

theorem quotientSocle_one_of_cyclic_image_axis
    {G Q : Type} [Group G] [Finite G] [Group Q] [IsCyclic Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (C : Subgroup G) [IsCyclic C]
    (hkerC : ¬ pi.ker ≤ C)
    (haxes : ∀ N : Subgroup G, N.Normal → pi.ker ≤ N ∨ N ≤ C)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_singletons_of_cyclic_image_axis pi hpi C hkerC haxes) N

end SymmetricSubgroupAsymptotics

end
