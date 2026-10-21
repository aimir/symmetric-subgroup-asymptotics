import SymmetricSubgroupAsymptotics.CFSGSuzukiModelTorusCard
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment
import SymmetricSubgroupAsymptotics.CFSGSuzukiIndexNumerics

/-! Outer automorphisms of the literal Suzuki model. Inner alignment
preserves the actual opposite pair, its faithful U restriction lies in
the proved intrinsic torus normalizer, and the actual inner torus q-1
factor cancels. No abstract Suzuki automorphism classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound
open CFSGSuzukiFieldParameters CFSGSuzukiPairRestriction
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiBorelIntersection CFSGSuzukiAlignedAutomorphisms
open CFSGOuterCardinalityAlignment PrimitiveSocleRawStructure

theorem outer_card_le (m : ℕ) (hm : 1≤m) :
    Nat.card (Outer (CFSG.Models.Suzuki m))≤2*m+1 := by
  apply outer_card_le_of_aligned_bound (pairStabilizer m) (modelTorus m)
    (d:=2*m+1)
  · intro f
    obtain ⟨g,hU,hO,_⟩ := exists_inner_preserve_U_opposite_torus m f
    exact ⟨g,hU,hO⟩
  · exact modelTorus_conj_mem_pair m
  · exact inner_modelTorus_injective m
  · rw [modelTorus_card]
    exact pairStabilizer_card_le m hm

/-- The quantitative simple-index packet for the pinned positive Suzuki
branch. The simplicity instance is the literal transferred model instance. -/
theorem simpleIndexBounds (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.Suzuki m) ell) :
    ell^2<Nat.card (CFSG.Models.Suzuki m) ∧
      (Nat.card (Outer (CFSG.Models.Suzuki m)) : ℝ)≤3*Real.logb 2 ell :=
  CFSGSuzukiIndexNumerics.simpleIndexBounds_of_outer_card m hm (outer_card_le m hm) ell hell

end SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound
