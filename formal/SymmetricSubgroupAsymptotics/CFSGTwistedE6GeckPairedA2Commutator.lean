import SymmetricSubgroupAsymptotics.CFSGCommutatorProductCrossCommute
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! The two paired E6 simple orbits form two commuting A2 edges. Their
literal paired-root commutator is a paired Weyl conjugate with coefficient
ONE, uniformly in the coefficient ring and diagram-field parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedA2Commutator
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6PairedFixedRoots
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckParameterizedCollecting CFSGNormTwoGeckOrthogonalWeyl
open CFSGSerreQuadraticMatrix CFSGGeckSerreRepresentation
open CFSGCommutatorProductCrossCommute

private abbrev partner (i : Fin 2) : Fin 6 := CFSG.Models.e6Twist (pairedNode i)

private theorem cross_cartan (i j : Fin 2) :
    cartan E6Base E6Index (pairedNode i) (partner j)=0 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> decide

private theorem cross_cartan_rev (i j : Fin 2) :
    cartan E6Base E6Index (partner i) (pairedNode j)=0 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> decide

private theorem edge_cartan (i j : Fin 2) (hij : i≠j) :
    cartan E6Base E6Index (pairedNode i) (pairedNode j)= -1 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem partner_edge_cartan (i j : Fin 2) (hij : i≠j) :
    cartan E6Base E6Index (partner i) (partner j)= -1 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

def pairedMatrixRoot (K : Type) [CommRing K] (sigma : K≃+*K) (j : Fin 2) (t : K) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  canonicalRoot rawData K false (pairedNode j) t*
    canonicalRoot rawData K false (partner j) (sigma t)

def pairedMatrixWeyl (K : Type) [CommRing K] (i : Fin 2) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  canonicalWeyl rawData K (pairedNode i)*canonicalWeyl rawData K (partner i)

theorem paired_adjacent_commutator (K : Type) [CommRing K] (sigma : K≃+*K)
    (i j : Fin 2) (hij : i≠j) (t a : K) :
    ⁅pairedMatrixRoot K sigma i t,pairedMatrixRoot K sigma j a⁆=
      pairedMatrixWeyl K i*pairedMatrixRoot K sigma j (a*t)*(pairedMatrixWeyl K i)⁻¹ := by
  let R (j : Fin 6) (a : K) := canonicalRoot rawData K false j a
  let W (j : Fin 6) := canonicalWeyl rawData K j
  have hcomm : ⁅R (pairedNode i) t*R (partner i) (sigma t),
      R (pairedNode j) a*R (partner j) (sigma a)⁆=
      ⁅R (pairedNode i) t,R (pairedNode j) a⁆*
        ⁅R (partner i) (sigma t),R (partner j) (sigma a)⁆ :=
    commutator_mul_mul _ _ _ _
      (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K _ _ (cross_cartan i i) false false t (sigma t))
      (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K _ _ (cross_cartan i j) false false t (sigma a))
      (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K _ _ (cross_cartan_rev i j) false false (sigma t) a)
      (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K _ _ (cross_cartan j j) false false a (sigma a))
  have hfirst : ⁅R (pairedNode i) t,R (pairedNode j) a⁆=
      W (pairedNode i)*R (pairedNode j) (a*t)*(W (pairedNode i))⁻¹ :=
    adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K _ _ (edge_cartan i j hij) t a
  have hsecond : ⁅R (partner i) (sigma t),R (partner j) (sigma a)⁆=
      W (partner i)*R (partner j) (sigma a*sigma t)*(W (partner i))⁻¹ :=
    adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K _ _ (partner_edge_cartan i j hij) (sigma t) (sigma a)
  change ⁅R (pairedNode i) t*R (partner i) (sigma t),
    R (pairedNode j) a*R (partner j) (sigma a)⁆=
      (W (pairedNode i)*W (partner i))*
        (R (pairedNode j) (a*t)*R (partner j) (sigma (a*t)))*
          (W (pairedNode i)*W (partner i))⁻¹
  rw [hcomm,hfirst,hsecond,←map_mul]
  exact conjugate_product_of_cross_commute _ _ _ _
    (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K _ _ (cross_cartan i i))
    (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K _ _ (cross_cartan_rev i j) false (a*t))
    (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K _ _ (cross_cartan i j) false (sigma (a*t)))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedA2Commutator
