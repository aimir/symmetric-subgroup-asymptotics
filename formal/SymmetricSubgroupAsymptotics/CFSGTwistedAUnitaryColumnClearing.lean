import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryClearingParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalFixedSpace

/-! A literal signed-isotropic hyperbolic column with nonzero last
coordinate is cleared by one actual radical array. The central radical
equation is proved from isotropy, not assumed as a separate parameter
or supplied full-unitary generation statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryColumnClearing
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

theorem upper_clear_column (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (eps : K) (heps : eps = 1 ∨ eps = -1) (H : Matrix J J K)
    (x : Index J → K) (hb : x (.inr (.inr ())) ≠ 0)
    (hiso : sigma (x (.inl ())) * x (.inr (.inr ())) +
      hermitianNorm sigma H (fun i => x (.inr (.inl i))) +
      eps * sigma (x (.inr (.inr ()))) * x (.inl ()) = 0) :
    ∃ (v : J → K) (c : K),
      sigma c + eps * c = -hermitianNorm sigma H v ∧
      upperArray (radicalRow sigma eps H v) v c *ᵥ x =
        Pi.single (.inr (.inr ())) (x (.inr (.inr ()))) := by
  let a := x (.inl ())
  let b := x (.inr (.inr ()))
  let z : J → K := fun i => x (.inr (.inl i))
  refine ⟨clearVector b z, clearCentral sigma eps a b,
    clearing_central_condition sigma hsigma eps heps H a b z hb hiso, ?_⟩
  ext p
  rcases p with u | (i | u)
  · cases u
    rw [upperArray_mulVec_head]
    have hh := clearing_head_zero sigma eps heps H a b z hb hiso
    simpa only [a, b, z, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, if_false] using hh
  · rw [upperArray_mulVec_middle]
    change z i + ((-b⁻¹) * z i) * b = _
    have he : (.inr (.inl i) : Index J) ≠ .inr (.inr ()) := by simp
    rw [Pi.single_eq_of_ne he]
    have hb' : b ≠ 0 := hb
    field_simp [hb'] <;> ring
  · cases u
    rw [upperArray_mulVec_last, Pi.single_eq_same]

omit [DecidableEq J] in
theorem blockForm_quadratic (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (x : Index J → K) :
    dotProduct (sigma ∘ x) (blockForm eps H *ᵥ x) =
      sigma (x (.inl ())) * x (.inr (.inr ())) +
        hermitianNorm sigma H (fun i => x (.inr (.inl i))) +
        eps * sigma (x (.inr (.inr ()))) * x (.inl ()) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, blockForm,
    hermitianNorm, Function.comp_apply, mul_add, add_assoc, mul_assoc, mul_comm eps]

theorem block_isometry_column_isotropic (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (B : Matrix (Index J) (Index J) K)
    (hB : (sigma.toRingHom.mapMatrix B).transpose * blockForm eps H * B = blockForm eps H) :
    sigma (B (.inl ()) (.inl ())) * B (.inr (.inr ())) (.inl ()) +
      hermitianNorm sigma H (fun i => B (.inr (.inl i)) (.inl ())) +
      eps * sigma (B (.inr (.inr ())) (.inl ())) * B (.inl ()) (.inl ()) = 0 := by
  rw [← blockForm_quadratic sigma eps H (fun i => B i (.inl ()))]
  have he := congrArg (fun M : Matrix (Index J) (Index J) K => M (.inl ()) (.inl ())) hB
  have hprod : dotProduct (sigma ∘ (fun i => B i (.inl ())))
      (blockForm eps H *ᵥ (fun i => B i (.inl ()))) =
      ((sigma.toRingHom.mapMatrix B).transpose * blockForm eps H * B) (.inl ()) (.inl ()) := by
    rw [Matrix.dotProduct_mulVec]
    rfl
  rw [hprod]
  exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryColumnClearing
