import SymmetricSubgroupAsymptotics.SecondPairChartSocles
import SymmetricSubgroupAsymptotics.SixPairOppositeCycleSocles

/-! The cyclic-image branches of the shared second pair chart admit the
sharper quotient-socle capacity two. The f,r branch uses the established
C4 wreath C3 cover of the actual C2 wreath C3 image. The z,r branch is
itself cyclic. These arguments retain the original correlated pair kernel. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SecondPairChartCyclicImageSocles

open SecondPairChartSocles

abbrev Model := SixPairOppositeCycleSocles.Model

def relabel : Equiv.Perm (Fin 6) where
  toFun := ![0,3,5,1,2,4]
  invFun := ![0,3,4,1,5,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def action : Model →* Equiv.Perm (Fin 6) :=
  relabel.permCongrHom.toMonoidHom.comp SixPairOppositeCycleSocles.literalAction

def modelCode : Fin 5 → Model := ![1,
  SixPairOppositeCycleSocles.oppositeModel * SixPairOppositeCycleSocles.cycleModel,
  1,SixPairOppositeCycleSocles.oppositeModel,1]

theorem code_action (i : Fin 5) (hi : i = 0 ∨ i = 1 ∨ i = 3) :
    action (modelCode i) = pairImage i := by
  revert i
  decide +kernel

theorem source_zero :
    action (QuaternaryTripleTernaryWreathModel.modelGenerators 0) =
      (f*r)*f*(f*r)⁻¹ := by decide +kernel

theorem source_one :
    action (QuaternaryTripleTernaryWreathModel.modelGenerators 1) = (f*r)*f := by
  decide +kernel

theorem range_le (K : Subgroup (Equiv.Perm (Fin 6))) (hr : r ∈ K) (hf : f ∈ K) :
    action.range ≤ K := by
  have hgen : Subgroup.closure (Set.range QuaternaryTripleTernaryWreathModel.modelGenerators) ≤
      K.comap action := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change action (QuaternaryTripleTernaryWreathModel.modelGenerators 0) ∈ K
      rw [source_zero]
      exact K.mul_mem (K.mul_mem (K.mul_mem hf hr) hf) (K.inv_mem (K.mul_mem hf hr))
    · change action (QuaternaryTripleTernaryWreathModel.modelGenerators 1) ∈ K
      rw [source_one]
      exact K.mul_mem (K.mul_mem hf hr) hf
  rw [QuaternaryTripleTernaryWreathModel.model_generated] at hgen
  rintro _ ⟨g,rfl⟩
  exact hgen (Subgroup.mem_top g)

theorem generated_range {ι : Type*} (codes : ι → Fin 5) (fi ri : ι)
    (hf : codes fi = 3) (hr : codes ri = 1)
    (hc : ∀ i, codes i = 0 ∨ codes i = 1 ∨ codes i = 3) :
    Subgroup.closure (Set.range (fun i => pairImage (codes i))) = action.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨modelCode (codes i),code_action _ (hc i)⟩
  · apply range_le
    · exact Subgroup.subset_closure ⟨ri,by
        change pairImage (codes ri) = r
        rw [hr]
        rfl⟩
    · exact Subgroup.subset_closure ⟨fi,by
        change pairImage (codes fi) = f
        rw [hf]
        rfl⟩

theorem image_normalGen (L : Subgroup action.range) (hL : L.Normal) :
    MarkedC4.normalGen L ≤ 1 := by
  letI := hL
  obtain ⟨x,hx⟩ := normal_generating_tuples_of_surjective
    (action.rangeRestrict.comp QuaternaryTripleTernaryWreathModel.sourceMap)
    (action.rangeRestrict_surjective.comp QuaternaryTripleTernaryWreathModel.sourceMap_surjective)
    QuaternaryTripleTernaryNormalGenerators.normal_generating_singletons L hL
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle_of_image {P : Subgroup (Equiv.Perm (Fin 6))}
    {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (himage : F.top.range = P)
    (hP : ∀ L : Subgroup P, L.Normal → MarkedC4.normalGen L ≤ 1)
    (c : U) (hcover : ∀ i : Fin 6, ∃ n : ℕ, (F.top c ^ n) 0 = i)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1 := by
    apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
      (F.top.rangeRestrict c) (fun _ : Fin 1 => (0 : Fin 6))
    intro i
    obtain ⟨n,hn⟩ := hcover i
    exact ⟨0,n,hn⟩
  apply F.quotientSocle_of_uniform_pair_action 1 1 hu ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* P := MulEquiv.subgroupCongr himage
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 1 hP L

theorem wreath_quotientSocle_of_codes {ι : Type*}
    (gs : ι → Equiv.Perm (Fin 12)) (codes : ι → Fin 5)
    (hp : ∀ i, BinaryPairFrame.Preserves outerFrame (gs i) (pairImage (codes i)))
    (fi ri : ι) (hf : codes fi = 3) (hr : codes ri = 1)
    (hc : ∀ i, codes i = 0 ∨ codes i = 1 ∨ codes i = 3)
    (N : Subgroup (Subgroup.closure (Set.range gs))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range gs)) ⧸ N) 2 := by
  let F := BinaryPairFrame.ofGenerators outerFrame gs (fun i => pairImage (codes i)) hp
  have hfi : F.top (closureGenerators gs fi) = f :=
    (BinaryPairFrame.ofGenerators_top_generator _ _ _ hp fi).trans (by
      change pairImage (codes fi) = f
      rw [hf]
      rfl)
  have hri : F.top (closureGenerators gs ri) = r :=
    (BinaryPairFrame.ofGenerators_top_generator _ _ _ hp ri).trans (by
      change pairImage (codes ri) = r
      rw [hr]
      rfl)
  apply quotientSocle_of_image F
    ((BinaryPairFrame.ofGenerators_top_range _ _ _ hp).trans
      (generated_range codes fi ri hf hr hc)) image_normalGen
    (closureGenerators gs fi * closureGenerators gs ri) ?_ N
  intro i
  obtain ⟨n,hn⟩ := f_cycle_cover i
  refine ⟨n,?_⟩
  rw [map_mul,hfi,hri]
  exact hn

theorem cyclic_quotientSocle_of_codes {ι : Type*}
    (gs : ι → Equiv.Perm (Fin 12)) (codes : ι → Fin 5)
    (hp : ∀ i, BinaryPairFrame.Preserves outerFrame (gs i) (pairImage (codes i)))
    (zi ri : ι) (hz : codes zi = 4) (hr : codes ri = 1)
    (hc : ∀ i, codes i = 0 ∨ codes i = 1 ∨ codes i = 4)
    (N : Subgroup (Subgroup.closure (Set.range gs))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range gs)) ⧸ N) 2 := by
  let F := BinaryPairFrame.ofGenerators outerFrame gs (fun i => pairImage (codes i)) hp
  have hzi : F.top (closureGenerators gs zi) = z :=
    (BinaryPairFrame.ofGenerators_top_generator _ _ _ hp zi).trans (by
      change pairImage (codes zi) = z
      rw [hz]
      rfl)
  have hri : F.top (closureGenerators gs ri) = r :=
    (BinaryPairFrame.ofGenerators_top_generator _ _ _ hp ri).trans (by
      change pairImage (codes ri) = r
      rw [hr]
      rfl)
  have himage : F.top.range ≤ Subgroup.zpowers (z*r) := by
    rw [BinaryPairFrame.ofGenerators_top_range]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    change pairImage (codes i) ∈ Subgroup.zpowers (z*r)
    rcases hc i with hi | hi | hi
    · rw [hi]
      exact (Subgroup.zpowers _).one_mem
    · rw [hi]
      have he : pairImage 1 = (z*r)^4 := by decide +kernel
      rw [he]
      exact (Subgroup.zpowers _).pow_mem (Subgroup.mem_zpowers _) 4
    · rw [hi]
      have he : pairImage 4 = (z*r)^3 := by decide +kernel
      rw [he]
      exact (Subgroup.zpowers _).pow_mem (Subgroup.mem_zpowers _) 3
  letI : IsCyclic F.top.range := isCyclic_of_injective
    (Subgroup.inclusion himage) (Subgroup.inclusion_injective himage)
  apply quotientSocle_of_image F rfl ?_ (closureGenerators gs zi * closureGenerators gs ri) ?_ N
  · intro L hL
    letI := hL
    exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic L
  · intro i
    obtain ⟨n,hn⟩ := z_cycle_cover i
    refine ⟨n,?_⟩
    rw [map_mul,hzi,hri]
    exact hn

end SymmetricSubgroupAsymptotics.SecondPairChartCyclicImageSocles

end
