import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters

/-! Actual smaller split-D words transport first to penultimate axes
inside every relative rank at least three, preserving the final pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankAxisTransport
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedA2FixedField CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDAllRankBlockMembership CFSGTwistedDAllRankBlockAction
open CFSGTwistedDHyperbolicBlockCoordinates CFSGTwistedDHyperbolicBlockMatrices

theorem scalarBlock_basis_action (n : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (fixedField q) (n + 2))ˣ) (i j : Index (n + 2))
    (hg : (g : Mat (fixedField q) (n + 2)) *ᵥ Pi.single i 1 = Pi.single j 1) :
    (scalarBlockHom n q g : Mat (q.Extension 2) (n + 3)) *ᵥ
      Pi.single (blockIndex (n + 2) i) 1 = Pi.single (blockIndex (n + 2) j) 1 := by
  rw [scalarBlockHom_val, Matrix.mulVec_single_one]
  funext x
  obtain ⟨x, rfl⟩ := (blockEquiv (n + 2)).surjective x
  cases x with
  | inl k =>
    change blockMatrixHom (q.Extension 2) (n + 2)
      ((g : Mat (fixedField q) (n + 2)).map (fixedField q).subtype)
      (blockIndex (n + 2) k) (blockIndex (n + 2) i) = _
    rw [blockMatrixHom_block_block]
    have hk := congrFun hg k
    rw [Matrix.mulVec_single_one] at hk
    have hf := congrArg (fun a : fixedField q => (a : q.Extension 2)) hk
    simpa only [Matrix.col, Matrix.map_apply, Pi.single_apply,
      Matrix.transpose_apply, blockEquiv_inl,
      (blockIndex_injective (n + 2)).eq_iff, apply_ite, map_one, map_zero] using hf
  | inr k =>
    change blockMatrixHom (q.Extension 2) (n + 2)
      ((g : Mat (fixedField q) (n + 2)).map (fixedField q).subtype)
      (blockEquiv (n + 2) (Sum.inr k)) (blockIndex (n + 2) i) = _
    rw [blockMatrixHom_apply, (blockEquiv (n + 2)).symm_apply_apply,
      blockEquiv_symm_blockIndex]
    have hne : blockIndex (n + 2) j ≠ blockEquiv (n + 2) (Sum.inr k) := by
      intro h
      change blockEquiv (n + 2) (Sum.inl j) = blockEquiv (n + 2) (Sum.inr k) at h
      have he := (blockEquiv (n + 2)).injective h
      cases he
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Pi.single_apply, if_neg (Ne.symm hne)]

theorem exists_axis_to_pen (n : ℕ) (q : CFSG.PrimePower) :
    ∃ u : relativeRootGroup (n + 1) q,
      (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl (pen (n + 1))) 1 ∧
      ∀ v : Index (n + 3) → q.Extension 2,
        ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
            (Sum.inl (last (n + 1))) = v (Sum.inl (last (n + 1))) ∧
        ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
            (Sum.inr (last (n + 1))) = v (Sum.inr (last (n + 1))) := by
  let i : Index (n + 2) := Sum.inl (Fin.last (n + 1))
  have hn : (Pi.single i (1 : fixedField q) : Index (n + 2) → fixedField q) ≠ 0 := by
    intro h
    have he := congrFun h i
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using he)
  have hQ : CFSGOrthogonalDIndexQuadraticForm.splitQ (fixedField q)
      (Pi.single i (1 : fixedField q)) = 0 :=
    by
      simpa only [CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm_apply] using
        CFSGSplitQuadraticBasisParameters.positive_norm (fixedField q) (Fin.last (n + 1)) 1
  obtain ⟨g, hg⟩ := CFSGOrthogonalDIndexVectorCoordinates.exists_normalize_singular
    (fixedField q) n (Pi.single i 1) hn hQ
  have hgi : (↑(g.val⁻¹) : Mat (fixedField q) (n + 2)) *ᵥ
      Pi.single (Sum.inl 0) 1 = Pi.single i 1 := by
    rw [← hg, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let u := blockRelativeHom n q g⁻¹
  have hu : u.val = scalarBlockHom n q (g⁻¹).val := rfl
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact scalarBlock_basis_action n q g.val⁻¹ (Sum.inl 0) i hgi
  · intro v
    rw [hu, scalarBlockHom_val]
    exact ⟨blockMatrixHom_positive_last _ _ _ _, blockMatrixHom_negative_last _ _ _ _⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankAxisTransport
