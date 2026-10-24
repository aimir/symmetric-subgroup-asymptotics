import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalNegativeScalars
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneConstraint
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! Actual positive and negative simple-root scalars of any conjugator
are reciprocal. Applying its conjugation to the literal rank-one Weyl
relation and the checked coefficient-one inverse constraint proves this
in every characteristic, without a torus recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalScalarReciprocity
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRankOneConstraint CFSGNormTwoGeckSelfRootConjugation
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem scalar_word_intertwining {G K : Type*} [Group G] [Field K]
    (x y : K→G) (d : G) (c e : K)
    (hx : ∀t,d*x t*d⁻¹=x (c*t)) (hy : ∀t,d*y t*d⁻¹=y (e*t))
    (hword : (x 1*y (-1)*x 1)*x 1=y (-1)*(x 1*y (-1)*x 1)) :
    (x c*y (-e)*x c)*x c=y (-e)*(x c*y (-e)*x c) := by
  let f := (MulAut.conj d).toMonoidHom
  have hX (t : K) : f (x t)=x (c*t) := hx t
  have hY (t : K) : f (y t)=y (e*t) := hy t
  have h := congrArg f hword
  simpa only [map_mul,hX,hY,mul_one,mul_neg] using h

theorem negative_scalar_eq_inverse (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (i : Fin 6) (c e : Kˣ)
    (hpos : ∀t,d*canonicalRoot rawData K false i t*d⁻¹=
      canonicalRoot rawData K false i ((c:K)*t))
    (hneg : ∀t,d*canonicalRoot rawData K true i t*d⁻¹=
      canonicalRoot rawData K true i ((e:K)*t)) : e=c⁻¹ := by
  have hrel : canonicalWeyl rawData K i*canonicalRoot rawData K false i 1=
      canonicalRoot rawData K true i (-1)*canonicalWeyl rawData K i := by
    have h := congrArg (fun z : (Matrix GeckIndex GeckIndex K)ˣ=>z*canonicalWeyl rawData K i)
      (self_root_word A hs hp E6Base E6Index K i 1)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  have hinter := scalar_word_intertwining
    (fun t=>canonicalRoot rawData K false i t) (fun t=>canonicalRoot rawData K true i t)
    d (c:K) (e:K) hpos hneg hrel
  have hc := canonical_word_inverse_constraint A hs hp E6Base E6Index K i
    (c:K) (-(e:K)) (c:K) (-(e:K)) (neg_ne_zero.mpr (Units.ne_zero e)) hinter
  have hval : (c:K)*(e:K)=1 := by
    have hz : 1-(c:K)*(e:K)=0 := by
      simpa only [sub_eq_add_neg,mul_neg] using hc
    exact (sub_eq_zero.mp hz).symm
  have hunit : c*e=1 := Units.ext hval
  have h := congrArg (fun a : Kˣ=>c⁻¹*a) hunit
  simpa only [←mul_assoc,inv_mul_cancel,one_mul,mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalScalarReciprocity
