import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Two actual physical pair actions. The inner three-pair kernel is an
arbitrary correlated binary submodule. A cyclic three-point action makes
that module uniformly cyclic; its actual cyclic or symmetric image has
all-normal bound one. Thus the actual six-point group has all-normal
bound two, and an outer six-cycle gives quotient-socle bound three.
No normal-generator bound is inherited from an ambient subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NestedBinaryPairSocles

abbrev rotation : Equiv.Perm (Fin 3) := finRotate 3
abbrev reflection : Equiv.Perm (Fin 3) := Equiv.swap 0 1

variable {P : Subgroup (Equiv.Perm (Fin 6))} (E : BinaryPairFrame P (Fin 3))

theorem inner_uniform (r : P) (hr : E.top r = rotation) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 3)) 1 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    (E.top.rangeRestrict r) (fun _ : Fin 1 => (0 : Fin 3))
  intro i
  refine ⟨0,i.val,?_⟩
  change (E.top r ^ i.val) 0 = i
  rw [hr]
  revert i
  decide +kernel

theorem inner_symmetric_range (r s : P)
    (hr : E.top r = rotation) (hs : E.top s = reflection) : E.top.range = ⊤ := by
  have hgen : Subgroup.closure
      ({rotation,reflection} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
    simpa only [rotation,reflection,show finRotate 3 (0 : Fin 3) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 3))
        (support_finRotate_of_le (by decide : 2 ≤ 3)) (0 : Fin 3)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ⟨r,hr⟩
  · exact ⟨s,hs⟩

theorem inner_normalGen_symmetric (r s : P)
    (hr : E.top r = rotation) (hs : E.top s = reflection)
    (L : Subgroup P) [L.Normal] : MarkedC4.normalGen L ≤ 2 := by
  apply E.normalGen_le_of_uniform_pair_action 1 1 (inner_uniform E r hr) ?_ L
  intro M hM
  letI := hM
  let e : E.top.range ≃* Equiv.Perm (Fin 3) :=
    (MulEquiv.subgroupCongr (inner_symmetric_range E r s hr hs)).trans Subgroup.topEquiv
  apply CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 1 ?_ M
  intro J hJ
  letI := hJ
  obtain ⟨x,hx⟩ := normal_generating_singletons_of_finite_normal_total
    NaturalFourNormalChains.symmetric_three_normal_total J hJ
  exact normalGen_le_of_fin_tuple x hx

theorem inner_normalGen_cyclic (r : P) (hr : E.top r = rotation)
    (himage : E.top.range ≤ Subgroup.zpowers rotation)
    (L : Subgroup P) [L.Normal] : MarkedC4.normalGen L ≤ 2 := by
  letI : IsCyclic E.top.range := isCyclic_of_injective
    (Subgroup.inclusion himage) (Subgroup.inclusion_injective himage)
  apply E.normalGen_le_of_uniform_pair_action 1 1 (inner_uniform E r hr) ?_ L
  intro M hM
  letI := hM
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic M

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 6))

theorem quotientSocle (himage : F.top.range = P)
    (hP : ∀ L : Subgroup P, L.Normal → MarkedC4.normalGen L ≤ 2)
    (c : U) (hcover : ∀ i : Fin 6, ∃ n : ℕ, (F.top c ^ n) 0 = i)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1 := by
    apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
      (F.top.rangeRestrict c) (fun _ : Fin 1 => (0 : Fin 6))
    intro i
    obtain ⟨n,hn⟩ := hcover i
    exact ⟨0,n,hn⟩
  apply F.quotientSocle_of_uniform_pair_action 1 2 hu ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* P := MulEquiv.subgroupCongr himage
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 2 hP L

theorem quotientSocle_of_generators {ι : Type*}
    (outerFrame : Fin 6 × ZMod 2 ≃ X) (innerFrame : Fin 3 × ZMod 2 ≃ Fin 6)
    (generators : ι → Equiv.Perm X) (tops : ι → Equiv.Perm (Fin 6))
    (blocks : ι → Equiv.Perm (Fin 3))
    (hp : ∀ i, BinaryPairFrame.Preserves outerFrame (generators i) (tops i))
    (hq : ∀ i, BinaryPairFrame.Preserves innerFrame (tops i) (blocks i))
    (ci di ri : ι) (hr : blocks ri = rotation)
    (hinner : (∃ si, blocks si = reflection) ∨
      (∀ i, blocks i ∈ Subgroup.zpowers rotation))
    (hcover : ∀ i : Fin 6, ∃ n : ℕ, ((tops ci * tops di) ^ n) 0 = i)
    (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range generators)) ⧸ N) 3 := by
  let F := BinaryPairFrame.ofGenerators outerFrame generators tops hp
  let E := BinaryPairFrame.ofGenerators innerFrame tops blocks hq
  have hP : ∀ L : Subgroup (Subgroup.closure (Set.range tops)),
      L.Normal → MarkedC4.normalGen L ≤ 2 := by
    intro L hL
    letI := hL
    have hri : E.top (closureGenerators tops ri) = rotation :=
      (BinaryPairFrame.ofGenerators_top_generator _ _ _ hq ri).trans hr
    rcases hinner with ⟨si,hsi⟩ | hcyclic
    · exact inner_normalGen_symmetric E (closureGenerators tops ri)
        (closureGenerators tops si) hri
        ((BinaryPairFrame.ofGenerators_top_generator _ _ _ hq si).trans hsi) L
    · apply inner_normalGen_cyclic E (closureGenerators tops ri) hri ?_ L
      rw [BinaryPairFrame.ofGenerators_top_range]
      exact (Subgroup.closure_le _).mpr (by rintro _ ⟨i,rfl⟩; exact hcyclic i)
  apply quotientSocle F (BinaryPairFrame.ofGenerators_top_range _ _ _ hp) hP
    (closureGenerators generators ci * closureGenerators generators di) ?_ N
  intro i
  obtain ⟨n,hn⟩ := hcover i
  have hci : F.top (closureGenerators generators ci) = tops ci :=
    BinaryPairFrame.ofGenerators_top_generator outerFrame generators tops hp ci
  have hdi : F.top (closureGenerators generators di) = tops di :=
    BinaryPairFrame.ofGenerators_top_generator outerFrame generators tops hp di
  refine ⟨n,?_⟩
  change ((F.top (closureGenerators generators ci * closureGenerators generators di)) ^ n) 0 = i
  rw [map_mul,hci,hdi]
  exact hn

end SymmetricSubgroupAsymptotics.NestedBinaryPairSocles

end
