import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleGaussFactor

/-! Parameterized paired rank-one words are the product of the two
literal orthogonal simple rank-one words. Their ratio to the paired
unit-parameter Weyl word is therefore the actual product of two tori. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6PairedFixedRoots
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPairedA2Commutator
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckSimpleGaussFactor CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix

private theorem paired_rank_one {G : Type*} [Group G] (a b c d : G)
    (hbc : Commute b c) (hba : Commute b a) (hda : Commute d a) :
    (a*b)*(c*d)*(a*b)=(a*c*a)*(b*d*b) := by
  rw [hbc.mul_mul_mul_comm a d]
  exact (hba.mul_left hda).mul_mul_mul_comm (a*c) b

private theorem torus_product {G : Type*} [Group G] (A B w v : G)
    (hwv : Commute w v) (hBw : Commute B w) :
    (A*B)*(w*v)⁻¹=(A*w⁻¹)*(B*v⁻¹) := by
  calc
    _=A*(B*(v⁻¹*w⁻¹)) := by group
    _=A*(B*(w⁻¹*v⁻¹)) := by rw [hwv.inv_inv.eq]
    _=A*((B*w⁻¹)*v⁻¹) := by group
    _=A*((w⁻¹*B)*v⁻¹) := by rw [hBw.inv_right.eq]
    _=_ := by group

def pairedParameterWeyl (K : Type) [Field K] (sigma : RingAut K) (j : Fin 2) (t : Kˣ) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  rawPairedHom K sigma false j (Multiplicative.ofAdd (t : K))*
    rawPairedHom K sigma true j (Multiplicative.ofAdd (-(t : K)⁻¹))*
    rawPairedHom K sigma false j (Multiplicative.ofAdd (t : K))

def pairedParameterTorus (K : Type) [Field K] (sigma : RingAut K) (j : Fin 2) (t : Kˣ) :
    (Matrix GeckIndex GeckIndex K)ˣ := pairedParameterWeyl K sigma j t*(pairedMatrixWeyl K j)⁻¹

theorem pairedParameterWeyl_eq (K : Type) [Field K] (sigma : RingAut K) (j : Fin 2) (t : Kˣ) :
    pairedParameterWeyl K sigma j t=
      parameterWeyl CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K (pairedNode j) t*
      parameterWeyl CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K (pairedPartner j)
        ((Units.map sigma.toMonoidHom) t) := by
  have hcartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index (pairedPartner j) (pairedNode j)=0 := by
    rw [E6_cartan]
    fin_cases j <;> decide
  change (canonicalRoot rawData K false (pairedNode j) (t : K)*
      canonicalRoot rawData K false (pairedPartner j) (sigma (t : K)))*
    (canonicalRoot rawData K true (pairedNode j) (-(t : K)⁻¹)*
      canonicalRoot rawData K true (pairedPartner j) (sigma (-(t : K)⁻¹)))*
    (canonicalRoot rawData K false (pairedNode j) (t : K)*
      canonicalRoot rawData K false (pairedPartner j) (sigma (t : K)))=
    (canonicalRoot rawData K false (pairedNode j) (t : K)*
      canonicalRoot rawData K true (pairedNode j) (-(t : K)⁻¹)*
      canonicalRoot rawData K false (pairedNode j) (t : K))*
    (canonicalRoot rawData K false (pairedPartner j) (sigma (t : K))*
      canonicalRoot rawData K true (pairedPartner j) (-(sigma (t : K))⁻¹)*
      canonicalRoot rawData K false (pairedPartner j) (sigma (t : K)))
  rw [map_neg,map_inv₀]
  exact paired_rank_one _ _ _ _
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ hcartan false true _ _)
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ hcartan false false _ _)
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ hcartan true false _ _)

theorem pairedParameterTorus_eq (K : Type) [Field K] (sigma : RingAut K) (j : Fin 2) (t : Kˣ) :
    pairedParameterTorus K sigma j t=
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K (pairedNode j) t*
      parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K (pairedPartner j)
        ((Units.map sigma.toMonoidHom) t) := by
  have hcartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index (pairedNode j) (pairedPartner j)=0 := by
    rw [E6_cartan]
    exact pairedNode_cartan j
  have hcross (neg : Bool) (a : K) : Commute (canonicalWeyl rawData K (pairedNode j))
      (canonicalRoot rawData K neg (pairedPartner j) a) :=
    orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ hcartan neg a
  have hwp : Commute (canonicalWeyl rawData K (pairedNode j))
      (parameterWeyl CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
        (pairedPartner j) ((Units.map sigma.toMonoidHom) t)) :=
    ((hcross false _).mul_right (hcross true _)).mul_right (hcross false _)
  rw [pairedParameterTorus,pairedParameterWeyl_eq]
  change (_*_)*(canonicalWeyl rawData K (pairedNode j)*canonicalWeyl rawData K (pairedPartner j))⁻¹=_
  rw [parameterTorus,parameterTorus,CFSGNormTwoGeckWeylSquareTorus.parameterWeyl_one,CFSGNormTwoGeckWeylSquareTorus.parameterWeyl_one]
  exact torus_product _ _ _ _
    (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ hcartan)
    hwp.symm

end SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl
