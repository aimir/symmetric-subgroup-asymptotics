import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeBlockMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters

/-! Actual smaller split-D words transport positive coordinate axes
inside the literal relative subgroup while fixing the final pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeAxisTransport
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedA2FixedField CFSGTwistedDRelativeChainLift
open CFSGTwistedDRelativeBlockMembership CFSGTwistedDHyperbolicBlockLift
open CFSGTwistedDHyperbolicBlockCoordinates CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockMembership

theorem scalarBlock_basis_action (s : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (fixedField q) (s + 3))ˣ) (i j : Index (s + 3))
    (hg : (g : Mat (fixedField q) (s + 3)) *ᵥ Pi.single i 1 = Pi.single j 1) :
    (scalarBlockHom s q g : Mat (q.Extension 2) (s + 4)) *ᵥ
      Pi.single (blockIndex (s + 3) i) 1 = Pi.single (blockIndex (s + 3) j) 1 := by
  rw [scalarBlockHom_val, Matrix.mulVec_single_one]
  funext x
  obtain ⟨x, rfl⟩ := (blockEquiv (s + 3)).surjective x
  cases x with
  | inl k =>
    change blockMatrixHom (q.Extension 2) (s + 3)
      ((g : Mat (fixedField q) (s + 3)).map (fixedField q).subtype)
      (blockIndex (s + 3) k) (blockIndex (s + 3) i) = _
    rw [blockMatrixHom_block_block]
    have hk := congrFun hg k
    rw [Matrix.mulVec_single_one] at hk
    have hf := congrArg (fun a : fixedField q => (a : q.Extension 2)) hk
    simpa only [Matrix.col, Matrix.map_apply, Pi.single_apply,
      Matrix.transpose_apply, blockEquiv_inl,
      (blockIndex_injective (s + 3)).eq_iff, apply_ite, map_one, map_zero] using hf
  | inr k =>
    change blockMatrixHom (q.Extension 2) (s + 3)
      ((g : Mat (fixedField q) (s + 3)).map (fixedField q).subtype)
      (blockEquiv (s + 3) (Sum.inr k)) (blockIndex (s + 3) i) = _
    rw [blockMatrixHom_apply, (blockEquiv (s + 3)).symm_apply_apply,
      blockEquiv_symm_blockIndex]
    have hne : blockIndex (s + 3) j ≠ blockEquiv (s + 3) (Sum.inr k) := by
      intro h
      change blockEquiv (s + 3) (Sum.inl j) = blockEquiv (s + 3) (Sum.inr k) at h
      have he := (blockEquiv (s + 3)).injective h
      cases he
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Pi.single_apply, if_neg (Ne.symm hne)]

theorem exists_axis_to_pen (s : ℕ) (q : CFSG.PrimePower) :
    ∃ u : relativePreimage s q,
      (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl (pen (s + 2))) 1 ∧
      ∀ v : Index (s + 4) → q.Extension 2,
        ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
            (Sum.inl (last (s + 2))) = v (Sum.inl (last (s + 2))) ∧
        ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
            (Sum.inr (last (s + 2))) = v (Sum.inr (last (s + 2))) := by
  let i : Index (s + 3) := Sum.inl (Fin.last (s + 2))
  have hn : (Pi.single i (1 : fixedField q) : Index (s + 3) → fixedField q) ≠ 0 := by
    intro h
    have he := congrFun h i
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using he)
  have hQ : CFSGOrthogonalDIndexQuadraticForm.splitQ (fixedField q)
      (Pi.single i (1 : fixedField q)) = 0 :=
    by
      simpa only [CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm_apply] using
        CFSGSplitQuadraticBasisParameters.positive_norm (fixedField q) (Fin.last (s + 2)) 1
  obtain ⟨g, hg⟩ := CFSGOrthogonalDIndexVectorCoordinates.exists_normalize_singular
    (fixedField q) (s + 1) (Pi.single i 1) hn hQ
  have hgi : (↑(g.val⁻¹) : Mat (fixedField q) (s + 3)) *ᵥ
      Pi.single (Sum.inl 0) 1 = Pi.single i 1 := by
    rw [← hg, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  obtain ⟨u, hu⟩ := exists_relative_lift s q g⁻¹
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact scalarBlock_basis_action s q g.val⁻¹ (Sum.inl 0) i hgi
  · intro v
    rw [hu, scalarBlockHom_val]
    exact ⟨blockMatrixHom_positive_last _ _ _ _, blockMatrixHom_negative_last _ _ _ _⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeAxisTransport
