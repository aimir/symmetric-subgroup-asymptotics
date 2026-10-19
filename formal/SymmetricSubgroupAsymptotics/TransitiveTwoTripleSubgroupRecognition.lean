import SymmetricSubgroupAsymptotics.TwoTripleProperUpperModelCovers
import SymmetricSubgroupAsymptotics.TwoTripleTransitiveKernelNontrivial
import SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts

/-! Every actual transitive subgroup of the standard two-triple wreath
receives an axes, quarter-turn, or full-wreath structural chart. Offset
lifts and correlated ternary kernels are retained in the actual pullback.
No normal-generator conclusion is a recognition input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.TransitiveTwoTripleSubgroupRecognition
open SemidirectProduct
open TwoTripleFullUpperForcesFullWreath
open TwoTripleProperUpperModelCovers
open TransitiveSixNormalGeneratorCharts

def chart (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]
    (hle : P ≤ SixPairLocalWreathSocles.literalAction.range) : Chart P := by
  apply Classical.choice
  let H : Subgroup Model := P.comap SixPairLocalWreathSocles.literalAction
  let U : Subgroup Upper := H.map upper
  let pi : H →* P := (SixPairLocalWreathSocles.literalAction.comp H.subtype).codRestrict P
    (fun g => g.2)
  have hpi : Function.Surjective pi := by
    intro p
    obtain ⟨g,hg⟩ := hle p.2
    refine ⟨⟨g,?_⟩,Subtype.ext hg⟩
    change SixPairLocalWreathSocles.literalAction g ∈ P
    rw [hg]
    exact p.2
  obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P (0 : Fin 6) 1
  obtain ⟨g,hg⟩ := hle p.2
  have hgH : g ∈ H := by change SixPairLocalWreathSocles.literalAction g ∈ P; rw [hg]; exact p.2
  have hgswap : g.right = C2Wreath.gen := swap_of_point g (by rw [hg]; exact hp)
  have hswap : ∃ u : Upper, u ∈ U ∧ u.right = C2Wreath.gen :=
    ⟨upper g,⟨g,hgH,rfl⟩,hgswap⟩
  rcases TwoTripleBinaryUpperRecognition.subgroup_cases U hswap with haxes | hquarter | hfull
  · have hP : P ≤ SixPointTernaryAxesNormalGenerators.literalAction.range := by
      intro p hp
      obtain ⟨k,hk⟩ := hle hp
      have hkH : k ∈ H := by change SixPairLocalWreathSocles.literalAction k ∈ P; rwa [hk]
      have hu := haxes (show upper k ∈ U from ⟨k,hkH,rfl⟩)
      exact ⟨axesWitness k,(axes_cover k hu).trans hk⟩
    exact ⟨.axes 1 (by simpa using hP)⟩
  · have hP : P ≤ SixPointTernaryQuarterTurnNormalGenerators.literalAction.range := by
      intro p hp
      obtain ⟨k,hk⟩ := hle hp
      have hkH : k ∈ H := by change SixPairLocalWreathSocles.literalAction k ∈ P; rwa [hk]
      have hu := hquarter (show upper k ∈ U from ⟨k,hkH,rfl⟩)
      exact ⟨quarterWitness k,(quarter_cover k hu).trans hk⟩
    have hqmem : SixPointTernaryQuarterTurnNormalGenerators.literalAction (quarterWitness g) ∈ P := by
      rw [quarter_cover g (hquarter (show upper g ∈ U from ⟨g,hgH,rfl⟩))]
      exact hgH
    rcases quarter_swap g hgswap with hq | hq
    · exact ⟨.quarter 1 (by simpa using hP) (quarterWitness g) (by simpa using hqmem) hq⟩
    · refine ⟨.quarter 1 (by simpa using hP) (quarterWitness g)⁻¹ ?_ ?_⟩
      · have hconj : MulAut.conj (1 : Equiv.Perm (Fin 6)) = 1 := by
          ext p
          simp [MulAut.conj_apply]
        simpa only [map_inv, hconj, one_smul] using P.inv_mem hqmem
      · simpa only [SemidirectProduct.inv_right,hq,inv_inv]
  · have hU : ∀ u : Upper, ∃ k : Model, k ∈ H ∧ upper k = u := by
      intro u
      have hu : u ∈ U := by rw [hfull]; exact Subgroup.mem_top _
      exact hu
    have hH : H = ⊤ := eq_top_of_full_upper_nonzero_kernel H hU
      (kernel_nontrivial_of_transitive_image H P pi hpi)
    have hP : P = SixPairLocalWreathSocles.literalAction.range := by
      apply le_antisymm hle
      rintro _ ⟨k,rfl⟩
      have hk : k ∈ H := by rw [hH]; exact Subgroup.mem_top _
      exact hk
    exact ⟨.fullWreath 1 (by simpa using hP)⟩

end SymmetricSubgroupAsymptotics.TransitiveTwoTripleSubgroupRecognition
