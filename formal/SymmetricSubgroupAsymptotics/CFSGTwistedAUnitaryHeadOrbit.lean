import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalFixedSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralDerived

/-! The ACTUAL upper group separates the first coordinate of every
nonzero natural vector. Central radical parameters detect the last
coordinate, and the proved same-radical fixed-space theorem detects all
middle coordinates. There is no assumed transitive orbit or full SU. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryNaturalRadical

theorem exists_upper_head_ne_zero (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x ≠ 0) :
    ∃ u : naturalUnipotent (s + 2) q,
      ((u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x) 0 ≠ 0 := by
  classical
  by_contra hn
  have hU (u : naturalUnipotent (s + 2) q) :
      ((u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x) 0 = 0 := by
    by_contra hu
    exact hn ⟨u, hu⟩
  let y : Index (Fin (s + 1)) → q.Extension 2 := x ∘ splitEquiv s
  have hyhead : y (.inl ()) = 0 := by
    have h := hU 1
    simpa only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] using h
  have hR (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b) :
      (upperArray (firstRow q s v) v b *ᵥ y) (.inl ()) = 0 := by
    have h := hU (radicalElement q s v b hb)
    rw [radicalElement_matrix] at h
    change (Matrix.reindex (splitEquiv s) (splitEquiv s)
      (upperArray (firstRow q s v) v b) *ᵥ x) (splitEquiv s (.inl ())) = 0 at h
    rw [reindex_mulVec_apply] at h
    exact h
  obtain ⟨t, ht, htc⟩ := exists_nonzero_central_parameter q s
  have hcentral := hR 0 t htc
  rw [upperArray_mulVec_head, firstRow_zero_eq, zero_dotProduct, add_zero,
    hyhead, zero_add] at hcentral
  have hylast : y (.inr (.inr ())) = 0 :=
    (mul_eq_zero.mp hcentral).resolve_left ht
  have hfixed : ∀ v b, Condition q s v b →
      upperArray (firstRow q s v) v b *ᵥ y = y := by
    intro v b hb
    ext p
    rcases p with u | (i | u)
    · cases u
      exact (hR v b hb).trans hyhead.symm
    · rw [upperArray_mulVec_middle, hylast, mul_zero, add_zero]
    · cases u
      exact upperArray_mulVec_last _ _ _ _
  have hm := ((radicalArrays_fixed_iff q s y).mp hfixed).1
  have hy : y = 0 := by
    funext p
    rcases p with u | (i | u)
    · cases u
      exact hyhead
    · exact hm i
    · cases u
      exact hylast
  apply hx
  funext i
  obtain ⟨p, rfl⟩ := (splitEquiv s).surjective i
  exact congrFun hy p

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
