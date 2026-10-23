import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveUnipotentSeparation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexJointKernel

/-! Projective commutation of two ACTUAL central-root elements reflects
to natural commutation in all characteristics. The two rank-one roots
have a common nonzero fixed vector, and the genuine cover kernel is
scalar. No parity division or odd-characteristic argument is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical

theorem unitaryProjectiveCover_eq_of_joint_fixed (q : CFSG.PrimePower) (s : ℕ)
    (u v : naturalFixed (s + 3) q) (he : unitaryProjectiveCover q s u = unitaryProjectiveCover q s v)
    (x : Fin (s + 4) → q.Extension 2) (hx : x ≠ 0)
    (hu : (u.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x = x)
    (hv : (v.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x = x) : u = v := by
  obtain ⟨a, ha⟩ := unitaryProjectiveCover_eq_scalar q s u v he
  have hax : x = a • x := by
    calc
      x = (u.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x := hu.symm
      _ = a • x := by rw [ha, Matrix.smul_mulVec, hv]
  have ha1 : a = 1 := smul_left_injective (q.Extension 2) hx
    (by simpa only [one_smul] using hax.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa only [ha1, one_smul] using ha

private theorem extreme_conjugate_fixed {K : Type} [Field K] (r : ℕ)
    (g : (Mat K r)ˣ) (b : K) (x : Fin (r + 1) → K)
    (hx : (((g⁻¹ : (Mat K r)ˣ) : Mat K r) *ᵥ x) (Fin.last r) = 0) :
    ((g : Mat K r) * (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *
      ((g⁻¹ : (Mat K r)ˣ) : Mat K r)) *ᵥ x = x := by
  have he : (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *ᵥ
      (((g⁻¹ : (Mat K r)ˣ) : Mat K r) *ᵥ x) =
        (((g⁻¹ : (Mat K r)ˣ) : Mat K r) *ᵥ x) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, hx, mul_zero]
    have hz : Function.update (0 : Fin (r + 1) → K) 0 (0 : K) = 0 := by
      funext i
      by_cases hi : i = 0 <;> simp [Function.update_apply, hi]
    rw [hz, add_zero]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he,
    Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

def centralRootAxisFunctional (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) :
    (Fin (s + 4) → q.Extension 2) →ₗ[q.Extension 2] q.Extension 2 where
  toFun x := ((↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ x) (Fin.last (s + 3))
  map_add' x y := by simp only [Matrix.mulVec_add, Pi.add_apply]
  map_smul' a x := by simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem conjugate_central_roots_joint_fixed (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) (b c : q.Extension 2)
    (hb : Condition q (s + 1) 0 b) (hc : Condition q (s + 1) 0 c) :
    ∃ x : Fin (s + 4) → q.Extension 2, x ≠ 0 ∧
      ((g * centralFixed q (s + 1) b hb * g⁻¹).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x = x ∧
      ((h * centralFixed q (s + 1) c hc * h⁻¹).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x = x := by
  let f : Fin 2 → Module.Dual (q.Extension 2) (Fin (s + 4) → q.Extension 2) :=
    fun i => if i = 0 then centralRootAxisFunctional q s g else centralRootAxisFunctional q s h
  obtain ⟨x, hx, hker⟩ := CFSGOrthogonalDIndexJointKernel.exists_nonzero_joint_kernel f (by
    simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
    omega)
  have hg0 : centralRootAxisFunctional q s g x = 0 := by simpa only [f, if_pos rfl] using hker 0
  have hh0 : centralRootAxisFunctional q s h x = 0 := by
    simpa only [f, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hker 1
  refine ⟨x, hx, ?_, ?_⟩
  · change ((g.val.val : Mat (q.Extension 2) (s + 3)) *
      ((centralFixed q (s + 1) b hb).val.val : Mat (q.Extension 2) (s + 3)) *
        (↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3))) *ᵥ x = x
    have hm : ((centralFixed q (s + 1) b hb).val.val : Mat (q.Extension 2) (s + 3)) =
        1 + Matrix.single (0 : Fin (s + 4)) (Fin.last (s + 3)) b := radicalCentral_matrix q (s + 1) b hb
    rw [hm]
    exact extreme_conjugate_fixed (s + 3) g.val.val b x hg0
  · change ((h.val.val : Mat (q.Extension 2) (s + 3)) *
      ((centralFixed q (s + 1) c hc).val.val : Mat (q.Extension 2) (s + 3)) *
        (↑(h.val.val⁻¹) : Mat (q.Extension 2) (s + 3))) *ᵥ x = x
    have hm : ((centralFixed q (s + 1) c hc).val.val : Mat (q.Extension 2) (s + 3)) =
        1 + Matrix.single (0 : Fin (s + 4)) (Fin.last (s + 3)) c := radicalCentral_matrix q (s + 1) c hc
    rw [hm]
    exact extreme_conjugate_fixed (s + 3) h.val.val c x hh0

theorem projective_central_roots_commute_iff (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) (b c : q.Extension 2)
    (hb : Condition q (s + 1) 0 b) (hc : Condition q (s + 1) 0 c) :
    Commute (unitaryProjectiveCover q s (g * centralFixed q (s + 1) b hb * g⁻¹))
        (unitaryProjectiveCover q s (h * centralFixed q (s + 1) c hc * h⁻¹)) ↔
      Commute (g * centralFixed q (s + 1) b hb * g⁻¹)
        (h * centralFixed q (s + 1) c hc * h⁻¹) := by
  let u := g * centralFixed q (s + 1) b hb * g⁻¹
  let v := h * centralFixed q (s + 1) c hc * h⁻¹
  constructor
  · intro he
    obtain ⟨x, hx, hu, hv⟩ := conjugate_central_roots_joint_fixed q s g h b c hb hc
    change Commute u v
    have hproj : unitaryProjectiveCover q s (u * v) = unitaryProjectiveCover q s (v * u) :=
      ((unitaryProjectiveCover q s).map_mul u v).trans
        (he.eq.trans ((unitaryProjectiveCover q s).map_mul v u).symm)
    have hufixed : ((u * v).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x = x := by
      change ((u.val.val : Mat (q.Extension 2) (s + 3)) *
        (v.val.val : Mat (q.Extension 2) (s + 3))) *ᵥ x = x
      rw [← Matrix.mulVec_mulVec, hv, hu]
    have hvfixed : ((v * u).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x = x := by
      change ((v.val.val : Mat (q.Extension 2) (s + 3)) *
        (u.val.val : Mat (q.Extension 2) (s + 3))) *ᵥ x = x
      rw [← Matrix.mulVec_mulVec, hu, hv]
    exact unitaryProjectiveCover_eq_of_joint_fixed q s (u * v) (v * u) hproj x hx hufixed hvfixed
  · intro he
    change unitaryProjectiveCover q s u * unitaryProjectiveCover q s v =
      unitaryProjectiveCover q s v * unitaryProjectiveCover q s u
    rw [← map_mul, ← map_mul, he.eq]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
