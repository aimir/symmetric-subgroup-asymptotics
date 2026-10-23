import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicVectorClearing
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLineNormalization

/-! Every nonzero signed-isotropic vector line is an ACTUAL conjugate
central point. The proof uses actual opposite pivot, radical clearing
and the literal three-root Weyl word; no transitive-orbit hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters
open CFSGTwistedAUnitaryNaturalRadical

theorem exists_isotropic_vector_axis (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x ≠ 0)
    (hiso : unitaryNaturalPair q (s + 2) x x = 0) :
    ∃ (h : naturalFixed (s + 2) q) (a : q.Extension 2), a ≠ 0 ∧
      (h.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x = a • Pi.single (0 : Fin (s + 3)) 1 := by
  obtain ⟨v, _, hb⟩ := exists_opposite_last_ne_zero q s x hx
  let y := (v.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x
  have hy : unitaryNaturalPair q (s + 2) y y = 0 :=
    (hermitianPair_isometry _ _ _ (naturalFixed_signedForm q (s + 2) v) x x).trans hiso
  obtain ⟨u, hu⟩ := upper_clear_isotropic_vector q s y hy hb
  obtain ⟨t, ht, htc⟩ := exists_nonzero_central_parameter q s
  let W := outerWeylFixed q s t htc
  let U := upperFixedHom q (s + 2) u
  refine ⟨W * U * v, t * y (Fin.last (s + 2)), mul_ne_zero ht hb, ?_⟩
  change (((W.val.val : Mat (q.Extension 2) (s + 2)) *
    (u.val.val : Mat (q.Extension 2) (s + 2))) *
      (v.val.val : Mat (q.Extension 2) (s + 2))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu]
  have hw := outerWeyl_last_action q s t htc ht (y (Fin.last (s + 2)))
  change (W.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
      Pi.single (Fin.last (s + 2)) (y (Fin.last (s + 2))) = _ at hw
  rw [hw]
  funext i
  by_cases hi : i = 0 <;> simp [Pi.single_apply, hi]

theorem exists_conjugateCentralPoint_of_isotropic (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 4) → q.Extension 2) (hx : x ≠ 0)
    (hiso : unitaryNaturalPair q (s + 3) x x = 0) :
    ∃ g : naturalFixed (s + 3) q,
      conjugateCentralPoint q (s + 1) g = (q.Extension 2) ∙ x := by
  obtain ⟨h, a, ha, he⟩ := exists_isotropic_vector_axis q (s + 1) x hx hiso
  have hh := congrArg (fun y : Fin (s + 4) → q.Extension 2 =>
    (↑(h.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ y) he
  have hv : x = a • unitaryCentralVector q s h⁻¹ := by
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_smul] using hh
  refine ⟨h⁻¹, ?_⟩
  rw [conjugateCentralPoint_eq_span, hv]
  exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) _).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
