import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeadCommonOpposite
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarStandardPlane
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicPointCoverage
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalGallery

/-! Any two actual singular planes with a common point in natural
dimensions4/5 have a literal common opposite. The shared point is
normalized by an original root word, the checked head-case witness is
used, and the SAME inverse natural matrix transports it back. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGHermitianOrthogonalSpan
open CFSGSerreOrdinaryTwists

private theorem disjoint_inverse_map {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (S : Submodule K V) (R : Submodule K W)
    (h : Disjoint (S.map e.toLinearMap) R) : Disjoint S (R.map e.symm.toLinearMap) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hxR
  obtain ⟨u, hu, rfl⟩ := hxR
  have hm : e (e.symm u) ∈ S.map e.toLinearMap := ⟨e.symm u, hx, rfl⟩
  rw [LinearEquiv.apply_symm_apply] at hm
  have hu0 := (Submodule.disjoint_def.mp h) u hm hu
  rw [hu0, map_zero]

theorem unitary_maximal_plane_finrank_two (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (R : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (hR : MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) R) :
    Module.finrank (q.Extension 2) R = 2 := by
  obtain ⟨g, hg⟩ := exists_normalize_maximal_to_starPlane q s hs R hR
  have hh := congrArg (fun S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) =>
    Module.finrank (q.Extension 2) S) hg
  simpa only [unitarySubspaceImage_finrank, starPlane_finrank] using hh

theorem exists_unitary_planes_common_opposite_of_shared_vector (q : CFSG.PrimePower)
    (s : ℕ) (hs : s ≤ 1)
    (S T : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 3) x y = 0)
    (hT : ∀ x ∈ T, ∀ y ∈ T, unitaryNaturalPair q (s + 3) x y = 0)
    (hdS : Module.finrank (q.Extension 2) S = 2)
    (hdT : Module.finrank (q.Extension 2) T = 2)
    (x : Fin (s + 4) → q.Extension 2) (hxS : x ∈ S) (hxT : x ∈ T) (hx : x ≠ 0) :
    ∃ R : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2),
      MaximalIsotropic (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) R ∧
      Disjoint S R ∧ Disjoint T R := by
  obtain ⟨g, a, ha, haxis⟩ := exists_isotropic_vector_axis q (s + 1) x hx (hS x hxS x hxS)
  let e := unitaryNaturalLinearEquiv q (s + 3) g
  let A := unitarySubspaceImage q (s + 3) g S
  let B := unitarySubspaceImage q (s + 3) g T
  have hhead (U : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2)) (hxU : x ∈ U) :
      Pi.single (0 : Fin (s + 4)) 1 ∈ unitarySubspaceImage q (s + 3) g U := by
    have hm : a • Pi.single (0 : Fin (s + 4)) 1 ∈ unitarySubspaceImage q (s + 3) g U :=
      ⟨x, hxU, haxis⟩
    have hh := (unitarySubspaceImage q (s + 3) g U).smul_mem a⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hh
  have hA := unitarySubspaceImage_pair_zero q (s + 3) g S hS
  have hB := unitarySubspaceImage_pair_zero q (s + 3) g T hT
  have hdA : Module.finrank (q.Extension 2) A = 2 :=
    (unitarySubspaceImage_finrank q (s + 3) g S).trans hdS
  have hdB : Module.finrank (q.Extension 2) B = 2 :=
    (unitarySubspaceImage_finrank q (s + 3) g T).trans hdT
  obtain ⟨R, hR, hAR, hBR⟩ := exists_unitary_head_planes_common_opposite q s hs A B
    (hhead S hxS) (hhead T hxT) hA hB hdA hdB
  let Q := R.map e.symm.toLinearMap
  have hQ : ∀ u ∈ Q, ∀ v ∈ Q, unitaryNaturalPair q (s + 3) u v = 0 := by
    rintro u ⟨u', hu, rfl⟩ v ⟨v', hv, rfl⟩
    have hh := unitaryNaturalLinearEquiv_pair q (s + 3) g (e.symm u') (e.symm v')
    change unitaryNaturalPair q (s + 3) (e (e.symm u')) (e (e.symm v')) = _ at hh
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hh
    exact hh.symm.trans (hR.1 u' hu v' hv)
  have hdQ : Module.finrank (q.Extension 2) Q = 2 := by
    change Module.finrank (q.Extension 2) (R.map e.symm.toLinearMap) = 2
    rw [LinearEquiv.finrank_map_eq]
    exact unitary_maximal_plane_finrank_two q s hs R hR
  exact ⟨Q, unitary_isotropic_plane_maximal q s hs Q hQ hdQ,
    disjoint_inverse_map e S R hAR, disjoint_inverse_map e T R hBR⟩

theorem unitary_gallery_common_opposite (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (S T : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)))
    (hstep : GalleryStep (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S T) :
    ∃ R : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      Disjoint S.val R.val ∧ Disjoint T.val R.val := by
  have hdS := unitary_maximal_plane_finrank_two q s hs S.val S.property
  have hdT := unitary_maximal_plane_finrank_two q s hs T.val T.property
  have hdim : 1 ≤ Module.finrank (q.Extension 2) ↥(S.val ⊓ T.val) := by
    change Module.finrank (q.Extension 2) S.val ≤
      Module.finrank (q.Extension 2) ↥(S.val ⊓ T.val) + 1 at hstep
    rw [hdS] at hstep
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hdim)
  obtain ⟨R, hR, hSR, hTR⟩ := exists_unitary_planes_common_opposite_of_shared_vector q s hs
    S.val T.val S.property.1 T.property.1 hdS hdT x hx.1 hx.2 hx0
  exact ⟨⟨R, hR⟩, hSR, hTR⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
