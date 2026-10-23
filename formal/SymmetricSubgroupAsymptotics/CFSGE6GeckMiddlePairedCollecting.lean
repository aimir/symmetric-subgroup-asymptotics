import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleAThreeCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylExchange
import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters

/-! The actual folded middle-edge commutator has a paired factor with
coefficient -ab and a singleton factor with coefficient Norm(a)b.
All identities hold literally over the same E6 Geck matrices; no trace
at one, characteristic division, or common-field premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedCollecting
open CFSGE6GeckMiddleAThreeCollecting CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckAdjacentWeylExchange
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

theorem firstMiddle_weyl_three (K : Type) [CommRing K] (a : K) :
    firstMiddle K a=canonicalWeyl rawData K 3*canonicalRoot rawData K false 2 (-a)*
      (canonicalWeyl rawData K 3)⁻¹ :=
  adjacent_weyl_exchange A hs hp E6Base E6Index K 2 3
    (by rw [E6_cartan];decide) (by rw [E6_cartan];decide) a

theorem secondMiddle_weyl_three (K : Type) [CommRing K] (a : K) :
    secondMiddle K a=canonicalWeyl rawData K 3*canonicalRoot rawData K false 4 (-a)*
      (canonicalWeyl rawData K 3)⁻¹ :=
  adjacent_weyl_exchange A hs hp E6Base E6Index K 4 3
    (by rw [E6_cartan];decide) (by rw [E6_cartan];decide) a

theorem paired_middle_product (K : Type) [Field K] (sigma : K≃+*K)
    (a b : K) (hb : sigma b=b) :
    secondMiddle K (sigma a*b)*firstMiddle K (a*b)=
      canonicalWeyl rawData K 3*rawPairedHom K sigma false 1 (Multiplicative.ofAdd (-(a*b)))*
        (canonicalWeyl rawData K 3)⁻¹ := by
  rw [secondMiddle_weyl_three,firstMiddle_weyl_three]
  have hc : Commute (canonicalRoot rawData K false 4 (-(sigma a*b)))
      (canonicalRoot rawData K false 2 (-(a*b))) :=
    orthogonal_signed_roots A hs hp E6Base E6Index K 4 2
      (by rw [E6_cartan];decide) false false _ _
  calc
    _=canonicalWeyl rawData K 3*(canonicalRoot rawData K false 4 (-(sigma a*b))*
        canonicalRoot rawData K false 2 (-(a*b)))*(canonicalWeyl rawData K 3)⁻¹ := by group
    _=canonicalWeyl rawData K 3*(canonicalRoot rawData K false 2 (-(a*b))*
        canonicalRoot rawData K false 4 (-(sigma a*b)))*(canonicalWeyl rawData K 3)⁻¹ := by rw [hc.eq]
    _=_ := by
      change canonicalWeyl rawData K 3*(canonicalRoot rawData K false 2 (-(a*b))*
        canonicalRoot rawData K false 4 (-(sigma a*b)))*(canonicalWeyl rawData K 3)⁻¹=
        canonicalWeyl rawData K 3*(canonicalRoot rawData K false 2 (-(a*b))*
          canonicalRoot rawData K false 4 (sigma (-(a*b))))*(canonicalWeyl rawData K 3)⁻¹
      rw [map_neg,map_mul,hb]

theorem middle_paired_commutator (K : Type) [Field K] (sigma : K≃+*K)
    (a b : K) (hb : sigma b=b) :
    ⁅rawPairedHom K sigma false 1 (Multiplicative.ofAdd a),
      rawSingletonHom K false 1 (Multiplicative.ofAdd b)⁆=
      highestMiddle K (a*sigma a*b)*
        (canonicalWeyl rawData K 3*rawPairedHom K sigma false 1 (Multiplicative.ofAdd (-(a*b)))*
          (canonicalWeyl rawData K 3)⁻¹) := by
  change ⁅canonicalRoot rawData K false 2 a*canonicalRoot rawData K false 4 (sigma a),
    canonicalRoot rawData K false 3 b⁆=_
  rw [middle_commutator,mul_assoc,paired_middle_product K sigma a b hb]

theorem norm_parameter_fixed (K : Type) [CommRing K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (a b : K) (hb : sigma b=b) :
    sigma (a*sigma a*b)=a*sigma a*b := by
  rw [map_mul,map_mul,hsigma,hb]
  ring

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedCollecting
