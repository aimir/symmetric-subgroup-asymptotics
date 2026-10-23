import SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.Tactic.FieldSimp

/-! The literal quadratic-extension norm is an actual quadratic form
over the fixed field. Its anisotropy and nondegenerate polar pairing
hold at every field size, including q=2. Trace surjectivity supplies an
explicit nonzero polar test; division by two is never used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
open CFSGTwistedDLinearParameters CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists

def normEmbedding (q : CFSG.PrimePower) :
    q.Extension 2 →ₗ[fixedField q] fixedSpace 0 q where
  toFun a := (linearParameters 0 q).symm (0, (0, a))
  map_add' a b := by
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' a b := by
    rw [← map_smul]
    congr 1
    simp only [Prod.smul_mk, smul_zero, RingHom.id_apply]

def normForm (q : CFSG.PrimePower) : QuadraticForm (fixedField q) (q.Extension 2) :=
  (fixedQuadraticForm 0 q).comp (normEmbedding q)

theorem normForm_apply (q : CFSG.PrimePower) (a : q.Extension 2) :
    normForm q a = Algebra.norm (fixedField q) a := by
  change fixedQuadraticForm 0 q ((linearParameters 0 q).symm (0, (0, a))) = _
  rw [quadratic_parameters]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem polar_coe (q : CFSG.PrimePower) (a b : q.Extension 2) :
    (((normForm q).polarBilin a b : fixedField q) : q.Extension 2) =
      a * definingFieldAutomorphism q 2 b + b * definingFieldAutomorphism q 2 a := by
  change (fixedField q).subtype (normForm q (a + b) - normForm q a - normForm q b) = _
  rw [map_sub, map_sub, normForm_apply, normForm_apply, normForm_apply]
  change ((Algebra.norm (fixedField q) (a + b) : fixedField q) : q.Extension 2) -
    ((Algebra.norm (fixedField q) a : fixedField q) : q.Extension 2) -
      ((Algebra.norm (fixedField q) b : fixedField q) : q.Extension 2) = _
  rw [norm_coe q (a + b), norm_coe q a, norm_coe q b, map_add]
  ring

theorem anisotropic (q : CFSG.PrimePower) (a : q.Extension 2) (ha : normForm q a = 0) : a = 0 := by
  have hm : a * definingFieldAutomorphism q 2 a = 0 := by
    rw [← norm_coe, ← normForm_apply, ha]
    rfl
  rcases mul_eq_zero.mp hm with h | h
  · exact h
  · exact (definingFieldAutomorphism q 2).injective (h.trans (map_zero _).symm)

theorem normForm_ne_zero (q : CFSG.PrimePower) {a : q.Extension 2} (ha : a ≠ 0) :
    normForm q a ≠ 0 := fun he => ha (anisotropic q a he)

theorem polar_left_nondegenerate (q : CFSG.PrimePower) (a : q.Extension 2)
    (ha : ∀ b, (normForm q).polarBilin a b = 0) : a = 0 := by
  by_contra hne
  obtain ⟨t, ht⟩ := CFSGTwistedAQuadraticTrace.exists_trace_eq_fixed q 1 (map_one _)
  let sigma := definingFieldAutomorphism q 2
  have hs : sigma (sigma a) = a := CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
  have hsInv : sigma ((sigma a)⁻¹) = a⁻¹ :=
    (map_inv₀ sigma (sigma a)).trans (congrArg Inv.inv hs)
  have hsa : sigma a ≠ 0 := fun he => hne (sigma.injective (he.trans (map_zero _).symm))
  let b := (sigma a)⁻¹ * t
  have hp : a * sigma b + b * sigma a = 1 := by
    calc
      a * sigma b + b * sigma a = sigma t + t := by
        dsimp only [b]
        simp only [map_mul]
        rw [hsInv]
        field_simp [hne, hsa] <;> ring
      _ = 1 := (add_comm _ _).trans ht
  have he := congrArg (fun x : fixedField q => (x : q.Extension 2)) (ha b)
  dsimp only at he
  rw [polar_coe] at he
  change a * sigma b + b * sigma a = 0 at he
  exact one_ne_zero (hp.symm.trans he)

end SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
