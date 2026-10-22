import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedMonomial
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMonomialSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalMiddleAction

/-! An inner radical, including the small rank-two field-two radical,
is transported into the large OUTER radical by the actual paired Weyl
word. Consequently its embedded image is original-derived. We do not
claim that the smaller radical is derived in its own source group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryMatrixSupport

theorem pairedPermutation_middle_head (s : ℕ) :
    pairPermutation (endpointNode (s)).castSucc (endpointNode (s)).succ
      (endpointNode (s)).rev.castSucc (endpointNode (s)).rev.succ
      (splitEquiv (s + 1) (.inr (.inl 0))) = (0 : Fin (s + 4)) := by
  have ha : splitEquiv (s + 1) (.inr (.inl 0)) = (endpointNode (s)).succ := by
    apply Fin.ext
    rfl
  have hp : (endpointNode (s)).castSucc = (0 : Fin (s + 4)) := rfl
  have hpr : (endpointNode (s)).castSucc ≠ (endpointNode (s)).rev.castSucc := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    simp only [endpointNode, Fin.val_castSucc, Fin.val_rev] at hv
    omega
  have hpt : (endpointNode (s)).castSucc ≠ (endpointNode (s)).rev.succ := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    simp only [endpointNode, Fin.val_castSucc, Fin.val_succ, Fin.val_rev] at hv
    omega
  rw [ha]
  change (Equiv.swap (endpointNode s).rev.castSucc (endpointNode s).rev.succ)
    ((Equiv.swap (endpointNode s).castSucc (endpointNode s).succ) (endpointNode s).succ) = _
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hpr hpt, hp]

theorem pairedPermutation_middle_last (s : ℕ) :
    pairPermutation (endpointNode (s)).castSucc (endpointNode (s)).succ
      (endpointNode (s)).rev.castSucc (endpointNode (s)).rev.succ
      (splitEquiv (s + 1) (.inr (.inl (Fin.last (s + 1))))) = Fin.last (s + 3) := by
  have hb : splitEquiv (s + 1) (.inr (.inl (Fin.last (s + 1)))) =
      (endpointNode (s)).rev.castSucc := by
    apply Fin.ext
    simp only [splitEquiv, splitIndex, Equiv.coe_fn_mk, endpointNode,
      Fin.val_last, Fin.val_castSucc, Fin.val_rev]
    omega
  have ht : (endpointNode (s)).rev.succ = Fin.last (s + 3) := by
    apply Fin.ext
    simp only [endpointNode, Fin.val_succ, Fin.val_rev, Fin.val_last]
    omega
  have hrp : (endpointNode (s)).rev.castSucc ≠ (endpointNode (s)).castSucc := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    simp only [endpointNode, Fin.val_castSucc, Fin.val_rev] at hv
    omega
  have hrq : (endpointNode (s)).rev.castSucc ≠ (endpointNode (s)).succ := by
    intro he
    have hv := congrArg (fun i : Fin (s + 4) => i.val) he
    simp only [endpointNode, Fin.val_castSucc, Fin.val_succ, Fin.val_rev] at hv
    omega
  rw [hb]
  simp only [pairPermutation, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hrp hrq,
    Equiv.swap_apply_left, ht]

theorem paired_conjugate_middle_supported_mem (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 1) q)
    (hdiag : ∀ i, (g.val.val : Mat (q.Extension 2) (s + 1)) i i = 1)
    (hsupport : ∀ i j, i ≠ 0 → j ≠ Fin.last (s + 1) →
      (g.val.val : Mat (q.Extension 2) (s + 1)) i j =
        (1 : Mat (q.Extension 2) (s + 1)) i j) :
    (endpointPairWeyl q s)⁻¹ * naturalFixedMiddleHom q (s + 1) g *
      endpointPairWeyl q s ∈ fixedRadical q (s + 1) := by
  obtain ⟨hd, hs⟩ := naturalFixedMiddleHom_support q (s + 1) g 0 (Fin.last (s + 1))
    hdiag hsupport
  apply (mem_fixedRadical_iff_natural_support q (s + 1) _).mpr
  constructor
  · change ∀ i, ((↑((endpointPairWeyl q s).val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *
        ((naturalFixedMiddleHom q (s + 1) g).val.val : Mat (q.Extension 2) (s + 3)) *
        ((endpointPairWeyl q s).val.val : Mat (q.Extension 2) (s + 3))) i i = 1
    exact inverse_monomial_conjugation_diag_one _ _ _ (endpointPairWeyl_monomial q s)
      (pairWeights_ne_zero _ _) _ hd
  · have hh := inverse_monomial_conjugation_support (endpointPairWeyl q s).val.val
      _ _ (endpointPairWeyl_monomial q s) (pairWeights_ne_zero _ _)
      ((naturalFixedMiddleHom q (s + 1) g).val.val : Mat (q.Extension 2) (s + 3))
      (splitEquiv (s + 1) (.inr (.inl 0)))
      (splitEquiv (s + 1) (.inr (.inl (Fin.last (s + 1))))) hd hs
    rw [pairedPermutation_middle_head, pairedPermutation_middle_last] at hh
    exact hh

theorem paired_conjugate_middle_radical_mem (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q s) :
    (endpointPairWeyl q (s + 1))⁻¹ * naturalFixedMiddleHom q (s + 2) g.val *
      endpointPairWeyl q (s + 1) ∈ fixedRadical q (s + 2) := by
  obtain ⟨hd, hs⟩ := (mem_fixedRadical_iff_natural_support q s g.val).mp g.property
  exact paired_conjugate_middle_supported_mem q (s + 1) g.val hd hs

theorem image_mem_normal_of_inverse_conjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (N : Subgroup H) [N.Normal] (W A : G)
    (hu : f (W⁻¹ * A * W) ∈ N) : f A ∈ N := by
  have hc := (inferInstance : N.Normal).conj_mem _ hu (f W)
  simpa only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hc

set_option maxHeartbeats 800000 in
theorem embedded_fixedRadical_original_derived (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q s) :
    naturalFixedToOriginal q (s + 4) (naturalFixedMiddleHom q (s + 2) g.val) ∈
      commutator (Fixed (s + 4) q) := by
  let W : naturalFixed (s + 4) q := endpointPairWeyl q (s + 1)
  let A : naturalFixed (s + 4) q := naturalFixedMiddleHom q (s + 2) g.val
  let f : naturalFixed (s + 4) q →* Fixed (s + 4) q := naturalFixedToOriginal q (s + 4)
  let u : fixedRadical q (s + 2) :=
    ⟨W⁻¹ * A * W, paired_conjugate_middle_radical_mem q s g⟩
  have hu := fixedRadical_original_derived q (s + 2) (by omega) u
  have hu' : f (W⁻¹ * A * W) ∈ commutator (Fixed (s + 4) q) := hu
  exact image_mem_normal_of_inverse_conjugate f _ W A hu'

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
