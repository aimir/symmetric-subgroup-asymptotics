import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing
import SymmetricSubgroupAsymptotics.CFSGRankOneRootCommutation

/-! Nonidentity actual central-root elements commute exactly when
their point labels are orthogonal for the literal signed Hermitian
form. Both natural and ORIGINAL projective commutation are retained,
uniformly including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical

private theorem commute_map_iff {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (hf : Function.Injective f) (a b : G) :
    Commute (f a) (f b) ↔ Commute a b := by
  constructor
  · intro h
    apply hf
    simpa only [map_mul] using h.eq
  · intro h
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul, h.eq]

private theorem commute_scaled_rankOne_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (u v : V) (f g : V →ₗ[K] K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hf : f ≠ 0)
    (hfu : f u = 0) (hr : f v = 0 ↔ g u = 0) :
    Commute (1 + a • f.smulRight u : Module.End K V) (1 + b • g.smulRight v) ↔ f v = 0 := by
  have hs (c : K) (l : V →ₗ[K] K) (w : V) : (c • l).smulRight w = c • l.smulRight w := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, smul_smul]
  rw [← hs, ← hs]
  have hfu' : (a • f) u = 0 := by simp only [LinearMap.smul_apply, hfu, smul_zero]
  have hr' : (a • f) v = 0 ↔ (b • g) u = 0 := by
    simpa only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero_iff_left ha,
      mul_eq_zero_iff_left hb] using hr
  rw [CFSGRankOneRootCommutation.commute_one_add_rankOne_iff u v (a • f) (b • g)
    (smul_ne_zero ha hf) hfu' hr']
  exact mul_eq_zero_iff_left ha

private theorem extreme_conjugate_apply {K : Type} [Field K] (r : ℕ)
    (g : (Mat K r)ˣ) (b : K) (x : Fin (r + 1) → K) :
    ((g : Mat K r) * (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *
      ((g⁻¹ : (Mat K r)ˣ) : Mat K r)) *ᵥ x =
        x + (b * ((((g⁻¹ : (Mat K r)ˣ) : Mat K r) *ᵥ x) (Fin.last r))) •
          ((g : Mat K r) *ᵥ Pi.single 0 1) := by
  have hs (c : K) : Function.update (0 : Fin (r + 1) → K) 0 c = c • Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0 <;> simp [Function.update_apply, hi]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, hs,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private def matrixUnitsEndHom {K I : Type*} [Field K] [Fintype I] [DecidableEq I] :
    (Matrix I I K)ˣ →* Module.End K (I → K) where
  toFun g := Matrix.mulVecLin (g : Matrix I I K)
  map_one' := Matrix.mulVecLin_one
  map_mul' g h := Matrix.mulVecLin_mul (g : Matrix I I K) (h : Matrix I I K)

def unitaryNaturalEndHom (q : CFSG.PrimePower) (r : ℕ) :
    naturalFixed r q →* Module.End (q.Extension 2) (Fin (r + 1) → q.Extension 2) :=
  matrixUnitsEndHom.comp (fixedMatrixHom q r)

theorem unitaryNaturalEndHom_injective (q : CFSG.PrimePower) (r : ℕ) :
    Function.Injective (unitaryNaturalEndHom q r) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLin'.injective he

theorem unitaryNaturalEndHom_central_root (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) (b : q.Extension 2) (hb : Condition q (s + 1) 0 b) :
    unitaryNaturalEndHom q (s + 3) (g * centralFixed q (s + 1) b hb * g⁻¹) =
      1 + b • (centralRootAxisFunctional q s g).smulRight (unitaryCentralVector q s g) := by
  apply LinearMap.ext
  intro x
  change ((g.val.val : Mat (q.Extension 2) (s + 3)) *
    ((centralFixed q (s + 1) b hb).val.val : Mat (q.Extension 2) (s + 3)) *
      (↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3))) *ᵥ x = _
  have hm : ((centralFixed q (s + 1) b hb).val.val : Mat (q.Extension 2) (s + 3)) =
      1 + Matrix.single (0 : Fin (s + 4)) (Fin.last (s + 3)) b := radicalCentral_matrix q (s + 1) b hb
  rw [hm, extreme_conjugate_apply]
  change x + (b * centralRootAxisFunctional q s g x) • unitaryCentralVector q s g =
    x + b • (centralRootAxisFunctional q s g x • unitaryCentralVector q s g)
  rw [smul_smul]

theorem natural_central_roots_commute_iff_pair_zero (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) (b c : q.Extension 2)
    (hb : Condition q (s + 1) 0 b) (hc : Condition q (s + 1) 0 c) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    Commute (g * centralFixed q (s + 1) b hb * g⁻¹) (h * centralFixed q (s + 1) c hc * h⁻¹) ↔
      unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) (unitaryCentralVector q s h) = 0 := by
  rw [← commute_map_iff (unitaryNaturalEndHom q (s + 3))
    (unitaryNaturalEndHom_injective q (s + 3)),
    unitaryNaturalEndHom_central_root, unitaryNaturalEndHom_central_root]
  rw [commute_scaled_rankOne_iff _ _ _ _ b c hb0 hc0
    (centralRootAxisFunctional_ne_zero q s g) (centralRootAxisFunctional_self q s g)
    (centralRootAxisFunctional_zero_reciprocal q s g h)]
  rw [unitaryCentralVector_pair]

theorem projective_central_roots_commute_iff_pair_zero (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) (b c : q.Extension 2)
    (hb : Condition q (s + 1) 0 b) (hc : Condition q (s + 1) 0 c) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    Commute (unitaryProjectiveCover q s (g * centralFixed q (s + 1) b hb * g⁻¹))
      (unitaryProjectiveCover q s (h * centralFixed q (s + 1) c hc * h⁻¹)) ↔
        unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) (unitaryCentralVector q s h) = 0 := by
  rw [projective_central_roots_commute_iff]
  exact natural_central_roots_commute_iff_pair_zero q s g h b c hb hc hb0 hc0

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
