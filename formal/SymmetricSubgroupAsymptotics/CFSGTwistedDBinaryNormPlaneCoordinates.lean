import SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! One actual trace-one extension element gives symplectic coordinates
on the literal anisotropic norm plane in characteristic two. The linear
map is proved injective by its actual polar Gram matrix and surjective
by the existing exact field cardinalities, not by form recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryNormPlaneCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists

def traceOne (q : CFSG.PrimePower) : q.Extension 2 :=
  (CFSGTwistedAQuadraticTrace.exists_trace_eq_fixed q 1 (map_one _)).choose

theorem traceOne_spec (q : CFSG.PrimePower) :
    traceOne q + definingFieldAutomorphism q 2 (traceOne q) = 1 :=
  (CFSGTwistedAQuadraticTrace.exists_trace_eq_fixed q 1 (map_one _)).choose_spec

def pairLinear (q : CFSG.PrimePower) :
    (fixedField q × fixedField q) →ₗ[fixedField q] q.Extension 2 where
  toFun x := x.1 • (1 : q.Extension 2) + x.2 • traceOne q
  map_add' x y := by simp [add_smul, add_assoc, add_left_comm]
  map_smul' a x := by simp [smul_add, smul_smul]

theorem pair_polar (q : CFSG.PrimePower) (hq : q.prime = 2)
    (x y : fixedField q × fixedField q) :
    (normForm q).polarBilin (pairLinear q x) (pairLinear q y) = x.1*y.2+x.2*y.1 := by
  letI : CharP (fixedField q) 2 := Eq.mp
    (congrArg (fun n : ℕ => CharP (fixedField q) n) hq)
    (inferInstance : CharP (fixedField q) q.prime)
  have hself (z : q.Extension 2) : (normForm q).polarBilin z z = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    exact CharTwo.add_self_eq_zero _
  have h1t : (normForm q).polarBilin 1 (traceOne q) = 1 := by
    apply Subtype.ext
    rw [polar_coe]
    simpa only [map_one, one_mul, mul_one, add_comm] using traceOne_spec q
  have ht1 : (normForm q).polarBilin (traceOne q) 1 = 1 := by
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h1t
  change (normForm q).polarBilin (x.1 • 1 + x.2 • traceOne q)
    (y.1 • 1 + y.2 • traceOne q) = _
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    hself, h1t, ht1, mul_zero, mul_one, zero_add, add_zero]
  ring

theorem pairLinear_bijective (q : CFSG.PrimePower) (hq : q.prime = 2) :
    Function.Bijective (pairLinear q) := by
  have hinj : Function.Injective (pairLinear q) := by
    intro x y he
    apply Prod.ext
    · calc
        x.1 = (normForm q).polarBilin (pairLinear q (0,1)) (pairLinear q x) := by
          rw [pair_polar q hq]; simp
        _ = (normForm q).polarBilin (pairLinear q (0,1)) (pairLinear q y) := congrArg _ he
        _ = y.1 := by rw [pair_polar q hq]; simp
    · calc
        x.2 = (normForm q).polarBilin (pairLinear q (1,0)) (pairLinear q x) := by
          rw [pair_polar q hq]; simp
        _ = (normForm q).polarBilin (pairLinear q (1,0)) (pairLinear q y) := congrArg _ he
        _ = y.2 := by rw [pair_polar q hq]; simp
  apply hinj.bijective_of_nat_card_le
  simpa only [Nat.card_prod, fixedField_card, CFSGTwistedANaturalMatrices.extension_two_card,
    pow_two] using (le_refl (q.order * q.order))

def pairEquiv (q : CFSG.PrimePower) (hq : q.prime = 2) :
    (fixedField q × fixedField q) ≃ₗ[fixedField q] q.Extension 2 :=
  LinearEquiv.ofBijective (pairLinear q) (pairLinear_bijective q hq)

end SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryNormPlaneCoordinates
