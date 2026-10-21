import SymmetricSubgroupAsymptotics.CFSGSuzukiSylowOfNormalizer
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusElements
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import SymmetricSubgroupAsymptotics.External.CFSG.Index

/-! Exact Suzuki good-Sylow assembly. The actual ambient normalizer
intersection and the actual opposite-U generation equality are temporary
explicit parameters here. This file does not assert either parameter;
the final family installer must replace both by their proved matrix
theorems. The pinned classifier's positive-m guard is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

/-- Transport two-conjugate generation from an actual ambient subgroup
into that SAME subgroup as a group in its own right. -/
theorem two_conjugates_generate_subgroup {A : Type*} [Group A]
    (G U : Subgroup A) (hUG : U≤G) (w : A) (hw : w∈G)
    (hgen : Subgroup.closure ((U : Set A) ∪ U.map (MulAut.conj w).toMonoidHom)=G) :
    Subgroup.closure ((U.subgroupOf G : Set G) ∪
      (U.subgroupOf G).map (MulAut.conj (⟨w,hw⟩ : G)).toMonoidHom)=⊤ := by
  let K := Subgroup.closure ((U.subgroupOf G : Set G) ∪
    (U.subgroupOf G).map (MulAut.conj (⟨w,hw⟩ : G)).toMonoidHom)
  have hU : U≤K.map G.subtype := by
    intro x hx
    refine ⟨⟨x,hUG hx⟩,?_,rfl⟩
    exact Subgroup.subset_closure (Or.inl hx)
  have hC : U.map (MulAut.conj w).toMonoidHom≤K.map G.subtype := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨(⟨w,hw⟩ : G)*⟨x,hUG hx⟩*(⟨w,hw⟩ : G)⁻¹,?_,rfl⟩
    apply Subgroup.subset_closure
    exact Or.inr ⟨⟨x,hUG hx⟩,hx,rfl⟩
  have hle := (Subgroup.closure_le (K.map G.subtype)).mpr (Set.union_subset hU hC)
  rw [hgen] at hle
  apply top_unique
  intro g _
  obtain ⟨x,hx,he⟩ := hle g.property
  exact (Subtype.ext he : x=g) ▸ hx

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.CFSGSuzukiGoodSylow
open CFSGSuzukiUnipotent CFSGSuzukiSylowOfNormalizer CFSGReduction

def modelWeyl (m : ℕ) : ActualGroup m :=
  ⟨CFSGSuzukiTorus.weylElement m,CFSGSuzukiTorus.weylElement_mem_model m⟩

variable (m : ℕ)
    (hN : Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) ⊓
      CFSG.Models.SuzukiConstruction.subgroup m≤borelEnvelope m)
    (hgen : Subgroup.closure ((unipotentSubgroup m : Set (Ambient m)) ∪
      (unipotentSubgroup m).map
        (MulAut.conj (CFSGSuzukiTorus.weylElement m)).toMonoidHom)=
      CFSG.Models.SuzukiConstruction.subgroup m)

include hgen

theorem model_opposite_generate :
    Subgroup.closure ((modelUnipotent m : Set (ActualGroup m)) ∪
      (modelUnipotent m).map (MulAut.conj (modelWeyl m)).toMonoidHom)=⊤ :=
  two_conjugates_generate_subgroup (CFSG.Models.SuzukiConstruction.subgroup m)
    (unipotentSubgroup m) (unipotentSubgroup_le_model m)
    (CFSGSuzukiTorus.weylElement m) (CFSGSuzukiTorus.weylElement_mem_model m) hgen

include hN

/-- Conditional on the two exact actual-matrix results, the witness is
the original unitriangular two-Sylow with the original Weyl matrix. -/
theorem goodSylowPrime_of_normalizer_and_opposite :
    GoodSylowPrime (CFSG.Models.Suzuki m) 2 := by
  refine ⟨by decide,modelSylow m hN,modelWeyl m,?_,?_⟩
  · exact modelSylow_normalizer_soluble m hN
  · exact model_opposite_generate m hgen

/-- Exact pinned model adapter; m=0 is not silently inserted into the
classifier's Suzuki constructor. -/
theorem suzukiIndex_goodSylowPrime_of_normalizer_and_opposite (hm : 1 ≤ m) :
    GoodSylowPrime (CFSG.Index.Model (.suzuki m hm)) 2 :=
  goodSylowPrime_of_normalizer_and_opposite m hN hgen

end SymmetricSubgroupAsymptotics.CFSGSuzukiGoodSylow
