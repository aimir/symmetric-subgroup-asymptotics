import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalKernel
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedTransfer

/-! Genuine middle commutator witnesses on the actual defining-fixed
radical. The actual vector quotient has checked full difference span,
and its kernel is already original-derived. Consequently the WHOLE
outer radical maps into the ORIGINAL fixed group's derived subgroup for
rank>=3, including q=2. No full-upper factorization is claimed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

theorem blockFixedMatrixHom_middle (q : CFSG.PrimePower) (s : ℕ) (a : naturalFixed s q) :
    blockFixedMatrixHom q s (naturalFixedMiddleHom q s a) = middleUnit a.val.val := by
  apply Units.ext
  change Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
    (Matrix.reindex (splitEquiv s) (splitEquiv s) (middleArray (a.val.val : Mat (q.Extension 2) s))) = _
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
  all_goals rfl

def radicalMiddleConjugate (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (g : fixedRadical q s) : fixedRadical q s :=
  ⟨naturalFixedMiddleHom q s a * g.val * (naturalFixedMiddleHom q s a)⁻¹, by
    change blockFixedMatrixHom q s
      (naturalFixedMiddleHom q s a * g.val * (naturalFixedMiddleHom q s a)⁻¹) ∈ arrayGroup
    rw [map_mul, map_mul, map_inv, blockFixedMatrixHom_middle]
    exact middle_conjugate_mem_arrayGroup a.val.val _ g.property⟩

theorem fixedRadicalParameter_middle_conjugate (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (g : fixedRadical q s) :
    fixedRadicalParameterHom q s (radicalMiddleConjugate q s a g) =
      Multiplicative.ofAdd ((a.val.val : Mat (q.Extension 2) s) *ᵥ
        (fixedRadicalParameterHom q s g).toAdd) := by
  change Multiplicative.ofAdd (fun i =>
    (blockFixedMatrixHom q s (naturalFixedMiddleHom q s a * g.val * (naturalFixedMiddleHom q s a)⁻¹) :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
        (.inr (.inl i)) (.inr (.inr ()))) =
    Multiplicative.ofAdd ((a.val.val : Mat (q.Extension 2) s) *ᵥ
      (fun i => (blockFixedMatrixHom q s g.val :
        Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
          (.inr (.inl i)) (.inr (.inr ()))))
  rw [map_mul, map_mul, map_inv, blockFixedMatrixHom_middle]
  exact vectorParameterHom_middle_conjugate a.val.val (radicalBlockHom q s g)

def radicalMiddleCommutator (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (g : fixedRadical q s) : fixedRadical q s :=
  radicalMiddleConjugate q s a g * g⁻¹

theorem fixedRadicalParameter_middle_commutator (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (g : fixedRadical q s) :
    fixedRadicalParameterHom q s (radicalMiddleCommutator q s a g) =
      Multiplicative.ofAdd ((a.val.val : Mat (q.Extension 2) s) *ᵥ
        (fixedRadicalParameterHom q s g).toAdd - (fixedRadicalParameterHom q s g).toAdd) := by
  change fixedRadicalParameterHom q s (radicalMiddleConjugate q s a g * g⁻¹) = _
  rw [map_mul, map_inv, fixedRadicalParameter_middle_conjugate]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv, sub_eq_add_neg]

theorem radicalToOriginal_middle_commutator (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalFixed s q) (g : fixedRadical q s) :
    radicalToOriginal q s (radicalMiddleCommutator q s a g) =
      ⁅naturalFixedToOriginal q (s + 2) (naturalFixedMiddleHom q s a), radicalToOriginal q s g⁆ := by
  change naturalFixedToOriginal q (s + 2)
    (naturalFixedMiddleHom q s a * g.val * (naturalFixedMiddleHom q s a)⁻¹ * g.val⁻¹) =
    ⁅naturalFixedToOriginal q (s + 2) (naturalFixedMiddleHom q s a),
      naturalFixedToOriginal q (s + 2) g.val⁆
  simp only [map_mul, map_inv, commutatorElement_def]

theorem fixedRadical_original_derived (q : CFSG.PrimePower) (s : ℕ) (hs : 1 ≤ s)
    (g : fixedRadical q s) : radicalToOriginal q s g ∈ commutator (Fixed (s + 2) q) := by
  apply CFSGMatrixMovingSpan.image_le_commutator_of_difference_span
    (fixedMatrixHom q s) (fixedMatrix_difference_span_eq_top q s hs)
    (radicalToOriginal q s) (fixedRadicalParameterHom q s)
    (fixedRadicalParameterHom_surjective q s)
    (fixedRadicalParameter_kernel_original_derived q s) ?_ g
  intro a v
  obtain ⟨u, hu⟩ := fixedRadicalParameterHom_surjective q s (Multiplicative.ofAdd v)
  refine ⟨radicalMiddleCommutator q s a u, ?_, ?_⟩
  · rw [radicalToOriginal_middle_commutator, commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)
  · rw [fixedRadicalParameter_middle_commutator, hu]
    rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
