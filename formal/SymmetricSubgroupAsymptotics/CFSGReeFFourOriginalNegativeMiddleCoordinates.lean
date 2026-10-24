import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeFamily
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeRootIntersections

/-! Actual negative middle coordinates in the original Ree quotient.
Conjugation of the genuine positive block is identified with the intrinsic
negative q-squared block by membership and exact cardinality. This is only
the unipotent block, with no whole rank-one Suzuki identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPerfectProjection CFSGReeFFourOppositeGenerationAssembly
open CFSGReeFFourMiddleNegativeFamily CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourOriginalRootCoordinates
open CFSGReeFFourOriginalRootIntersections CFSGReeFFourOriginalNegativeRootIntersections
open CFSGReeFFourOriginalMinimalParabolics CFSGReeFFourMinimalParabolics
open CFSGReeFFourSimpleBlockPeelingGeneration CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourFixedAmbientHom
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOriginalOppositeAlignment

def originalMiddleWeyl (m : ℕ) (hm : 0<m) : CFSG.Models.ReeF4 m :=
  fixedToOriginal m hm (fixedMiddleWeyl m)

private theorem map_conjugation {G H : Type*} [Group G] [Group H] (F : G→*H) (w x : G) :
    F (w*x*w⁻¹)=F w*F x*(F w)⁻¹ := by rw [map_mul,map_mul,map_inv]

theorem original_middle_conjugate_block (m : ℕ) (hm : 0<m) :
    (originalRootBlock m hm true).map (MulAut.conj (originalMiddleWeyl m hm)).toMonoidHom=
      originalNegativeRootBlock m hm true := by
  letI : Finite (originalModelFixed m) :=
    Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)
  letI : Finite (CFSG.Models.ReeF4 m) :=
    Finite.of_surjective (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)
  apply Subgroup.eq_of_le_of_card_ge
  · rintro z ⟨x,hx,rfl⟩
    rw [original_middle_block_eq_range] at hx
    obtain ⟨y,rfl⟩ := hx
    let g : originalModelFixed m := fixedMiddleWeyl m*y.val*(fixedMiddleWeyl m)⁻¹
    have hV : g∈fixedNegative m :=
      middle_conjugate_middleFixedSubgroup_le m ⟨y.val,y.property,rfl⟩
    have hW : fixedMiddleWeyl m∈simpleParabolic m true := by
      have hh : simpleWeyl m true∈simpleParabolic m true :=
        (show Subgroup.closure {simpleWeyl m true}≤simpleParabolic m true from le_sup_right)
          (Subgroup.subset_closure (Set.mem_singleton _))
      rwa [simpleWeyl_true] at hh
    have hMU : middleFixedSubgroup m≤fixedPositive m := by
      rw [←middle_simple_inversion_eq]
      exact inf_le_left
    have hyU : y.val∈fixedPositive m := hMU y.property
    have hyP := ((positive_le_borel m).trans
      (show fixedBorel m≤simpleParabolic m true from le_sup_left)) hyU
    have hP : g∈simpleParabolic m true :=
      (simpleParabolic m true).mul_mem ((simpleParabolic m true).mul_mem hW hyP)
        ((simpleParabolic m true).inv_mem hW)
    have hg : fixedToOriginal m hm g=
        (MulAut.conj (originalMiddleWeyl m hm)) (middleToOriginalHom m hm y) :=
      map_conjugation (fixedToOriginal m hm) (fixedMiddleWeyl m) y.val
    rw [←original_negative_inf_simpleParabolic]
    exact ⟨⟨g,hV,hg⟩,⟨g,hP,hg⟩⟩
  · have hc := Nat.card_congr ((MulAut.conj (originalMiddleWeyl m hm)).subgroupMap
      (originalRootBlock m hm true)).toEquiv
    change Nat.card (originalRootBlock m hm true)=
      Nat.card ((originalRootBlock m hm true).map (MulAut.conj (originalMiddleWeyl m hm)).toMonoidHom) at hc
    simpa only [←hc,originalRootBlock_card,originalNegativeRootBlock_card,ite_true] using
      (le_rfl : ((2 : ℕ)^(2*m+1))^2≤((2 : ℕ)^(2*m+1))^2)

def originalNegativeMiddleEquiv (m : ℕ) (hm : 0<m) :
    CFSGSuzukiUnipotent.unipotentSubgroup m ≃* originalNegativeRootBlock m hm true :=
  (originalMiddleSuzukiEquiv m hm).symm.trans
    (((MulAut.conj (originalMiddleWeyl m hm)).subgroupMap (originalRootBlock m hm true)).trans
      (MulEquiv.subgroupCongr (original_middle_conjugate_block m hm)))

def originalNegativeMiddleEmbedding (m : ℕ) (hm : 0<m) :
    CFSGSuzukiUnipotent.unipotentSubgroup m →* CFSG.Models.ReeF4 m :=
  (originalNegativeRootBlock m hm true).subtype.comp (originalNegativeMiddleEquiv m hm).toMonoidHom

theorem originalNegativeMiddleEmbedding_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (originalNegativeMiddleEmbedding m hm) :=
  Subtype.val_injective.comp (originalNegativeMiddleEquiv m hm).injective

theorem originalNegativeMiddleEmbedding_conjugation (m : ℕ) (hm : 0<m)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    originalNegativeMiddleEmbedding m hm x=originalMiddleWeyl m hm*originalMiddleEmbedding m hm x*
      (originalMiddleWeyl m hm)⁻¹ := rfl

theorem originalNegativeMiddleEmbedding_range (m : ℕ) (hm : 0<m) :
    (originalNegativeMiddleEmbedding m hm).range=originalNegativeRootBlock m hm true := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact (originalNegativeMiddleEquiv m hm x).property
  · intro x hx
    obtain ⟨y,hy⟩ := (originalNegativeMiddleEquiv m hm).surjective ⟨x,hx⟩
    exact ⟨y,congrArg (fun z : originalNegativeRootBlock m hm true=>z.val) hy⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleCoordinates
