import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCompressionDimension
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryResidualRayAvoidance
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPlaneMaximality
import SymmetricSubgroupAsymptotics.CFSGHermitianResidueOppositePlane

/-! A literal common-opposite witness for any two isotropic planes
containing the first axis in natural dimensions4/5. Their compressed
residues are lines; a third actual singular ray supplies the last-axis
plane. No common-opposite or thickness hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan CFSGHermitianHyperbolicCompression
open CFSGTwistedAUnitaryUpperArrays

theorem exists_unitary_head_planes_common_opposite (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (S T : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (heS : Pi.single (0 : Fin (s + 4)) 1 ∈ S)
    (heT : Pi.single (0 : Fin (s + 4)) 1 ∈ T)
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 3) x y = 0)
    (hT : ∀ x ∈ T, ∀ y ∈ T, unitaryNaturalPair q (s + 3) x y = 0)
    (hdS : Module.finrank (q.Extension 2) S = 2)
    (hdT : Module.finrank (q.Extension 2) T = 2) :
    ∃ R : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2),
      MaximalIsotropic (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) R ∧
      Disjoint S R ∧ Disjoint T R := by
  let e := unitarySplitLinearEquiv q (s + 1)
  let A := S.map e.toLinearMap
  let B := T.map e.toLinearMap
  have hdA := unitaryCompressedPlane_finrank_one q (s + 1) S heS hS hdS
  have hdB := unitaryCompressedPlane_finrank_one q (s + 1) T heT hT hdT
  obtain ⟨v, hv, hnorm, hvA, hvB⟩ := exists_unitary_singular_vector_outside_two_lines q (s + 1)
    (by omega) (unitaryCompressedSpace q (s + 1) S) (unitaryCompressedSpace q (s + 1) T) hdA hdB
  have hvA' : v ∉ compressedSpace A := by
    intro h
    apply hvA
    exact unitaryCompressedSpace_split_eq q (s + 1) S ▸ h
  have hvB' : v ∉ compressedSpace B := by
    intro h
    apply hvB
    exact unitaryCompressedSpace_split_eq q (s + 1) T ▸ h
  have hzA : ∀ x ∈ A, x (.inr (.inr ())) = 0 := by
    rintro x ⟨y, hy, rfl⟩
    change y (Fin.last (s + 3)) = 0
    simpa only [unitaryNaturalPair_first] using hS _ heS y hy
  have hzB : ∀ x ∈ B, x (.inr (.inr ())) = 0 := by
    rintro x ⟨y, hy, rfl⟩
    change y (Fin.last (s + 3)) = 0
    simpa only [unitaryNaturalPair_first] using hT _ heT y hy
  let C := residueOppositePlane v
  have hCnorm : hermitianPair (definingFieldAutomorphism q 2) (middleForm q (s + 1)) v v = 0 := by
    change dotProduct _ (Matrix.mulVec (-(signedReversalUnit (q.Extension 2) (s + 1) : Mat (q.Extension 2) (s + 1))) v) = 0
    rw [Matrix.neg_mulVec, dotProduct_neg]
    change -unitaryNaturalPair q (s + 1) v v = 0
    rw [hnorm, neg_zero]
  have hC := residueOppositePlane_pair_zero (definingFieldAutomorphism q 2)
    (parity q (s + 1)) (middleForm q (s + 1)) v hCnorm
  have hdC : Module.finrank (q.Extension 2) C = 2 := residueOppositePlane_finrank v hv
  have hdAC : Disjoint A C := residueOppositePlane_disjoint A hzA v hvA'
  have hdBC : Disjoint B C := residueOppositePlane_disjoint B hzB v hvB'
  let R := C.map e.symm.toLinearMap
  have hR : ∀ x ∈ R, ∀ y ∈ R, unitaryNaturalPair q (s + 3) x y = 0 := by
    rintro x ⟨u, hu, rfl⟩ y ⟨w, hw, rfl⟩
    rw [unitaryNaturalPair_split]
    change hermitianPair (definingFieldAutomorphism q 2) (blockForm (parity q (s + 1)) (middleForm q (s + 1)))
      (e (e.symm u)) (e (e.symm w)) = 0
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hC u hu w hw
  have hdR : Module.finrank (q.Extension 2) R = 2 := by
    change Module.finrank (q.Extension 2) (C.map e.symm.toLinearMap) = 2
    rw [LinearEquiv.finrank_map_eq]
    exact hdC
  have disjoint_pullback (U : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
      (hU : Disjoint (U.map e.toLinearMap) C) : Disjoint U R := by
    apply Submodule.disjoint_def.mpr
    intro x hx hxR
    obtain ⟨u, hu, rfl⟩ := hxR
    have hmem : e (e.symm u) ∈ U.map e.toLinearMap := ⟨e.symm u, hx, rfl⟩
    rw [LinearEquiv.apply_symm_apply] at hmem
    have hu0 := (Submodule.disjoint_def.mp hU) u hmem hu
    rw [hu0, map_zero]
  exact ⟨R, unitary_isotropic_plane_maximal q s hs R hR hdR,
    disjoint_pullback S hdAC, disjoint_pullback T hdBC⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
