import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckMixedAdjacentCollecting
import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters

/-! The actual paired E6 A2 has the same coefficient-one opposite-simple
incidence. Self-root conjugation and the Weyl-square sign are proved
componentwise on its two orthogonal A2 blocks, retaining all parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckPairedMixedA2
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6GeckPairedA2Commutator
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl CFSGNormTwoGeckSelfRootConjugation
open CFSGNormTwoGeckAdjacentCartanSign CFSGSerreQuadraticMatrix CFSGGeckSerreRepresentation
open CFSGCommutatorProductCrossCommute CFSGA2MixedCommutator

private theorem cross (i j : Fin 2) : cartan E6Base E6Index (pairedNode i) (pairedPartner j)=0 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> decide

private theorem cross_rev (i j : Fin 2) : cartan E6Base E6Index (pairedPartner i) (pairedNode j)=0 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> decide

private theorem edge (i j : Fin 2) (hij : i≠j) : cartan E6Base E6Index (pairedNode i) (pairedNode j)= -1 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem partner_edge (i j : Fin 2) (hij : i≠j) : cartan E6Base E6Index (pairedPartner i) (pairedPartner j)= -1 := by
  rw [E6_cartan]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem pair_square {G : Type*} [Group G] (p q x y x' y' : G)
    (hpq : Commute p q) (hqx : Commute q x) (hpy : Commute p y)
    (hpx : p^2*x=x'*p^2) (hqy : q^2*y=y'*q^2) :
    (p*q)^2*(x*y)=(x'*y')*(p*q)^2 := by
  have hx : p^2*x*(p^2)⁻¹=x' := by rw [hpx]; group
  have hy : q^2*y*(q^2)⁻¹=y' := by rw [hqy]; group
  have he := conjugate_product_of_cross_commute (p^2) (q^2) x y
    (hpq.pow_pow 2 2) (hqx.pow_left 2) (hpy.pow_left 2)
  rw [hx,hy] at he
  calc
    _=((p^2*q^2)*(x*y)*(p^2*q^2)⁻¹)*(p^2*q^2) := by rw [←hpq.mul_pow]; group
    _=(x'*y')*(p^2*q^2) := by rw [←he]
    _=_ := by rw [←hpq.mul_pow]

theorem paired_self_root (K : Type) [Field K] (sigma : RingAut K) (i : Fin 2) (a : K) :
    pairedMatrixWeyl K i*rawPairedHom K sigma false i (Multiplicative.ofAdd a)*
      (pairedMatrixWeyl K i)⁻¹=rawPairedHom K sigma true i (Multiplicative.ofAdd (-a)) := by
  let W (j : Fin 6) := canonicalWeyl rawData K j
  let R (j : Fin 6) (t : K) := canonicalRoot rawData K false j t
  have he := conjugate_product_of_cross_commute
    (W (pairedNode i)) (W (pairedPartner i)) (R (pairedNode i) a) (R (pairedPartner i) (sigma a))
    (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ (cross i i))
    (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ (cross_rev i i) false a)
    (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ (cross i i) false (sigma a))
  change (W (pairedNode i)*W (pairedPartner i))*(R (pairedNode i) a*R (pairedPartner i) (sigma a))*
    (W (pairedNode i)*W (pairedPartner i))⁻¹=
      canonicalRoot rawData K true (pairedNode i) (-a)*canonicalRoot rawData K true (pairedPartner i) (sigma (-a))
  rw [←he]
  dsimp only [W,R]
  rw [self_root_word,self_root_word,map_neg]

theorem paired_adjacent_square_sign (K : Type) [Field K] (sigma : RingAut K)
    (i j : Fin 2) (hij : i≠j) (a : K) :
    (pairedMatrixWeyl K i)^2*rawPairedHom K sigma false j (Multiplicative.ofAdd a)=
      rawPairedHom K sigma false j (Multiplicative.ofAdd (-a))*(pairedMatrixWeyl K i)^2 := by
  change (canonicalWeyl rawData K (pairedNode i)*canonicalWeyl rawData K (pairedPartner i))^2*
    (canonicalRoot rawData K false (pairedNode j) a*canonicalRoot rawData K false (pairedPartner j) (sigma a))=
      (canonicalRoot rawData K false (pairedNode j) (-a)*canonicalRoot rawData K false (pairedPartner j) (sigma (-a)))*
      (canonicalWeyl rawData K (pairedNode i)*canonicalWeyl rawData K (pairedPartner i))^2
  rw [map_neg]
  exact pair_square _ _ _ _ _ _
    (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ (cross i i))
    (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ (cross_rev i j) false a)
    (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K _ _ (cross i j) false (sigma a))
    (adjacent_cartan_square_sign CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      (pairedNode i) (pairedNode j) (edge j i hij.symm) K false a)
    (adjacent_cartan_square_sign CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      (pairedPartner i) (pairedPartner j) (partner_edge j i hij.symm) K false (sigma a))

theorem paired_mixed_adjacent (K : Type) [Field K] (sigma : RingAut K)
    (i j : Fin 2) (hij : i≠j) (a b : K) :
    ⁅rawPairedHom K sigma true i (Multiplicative.ofAdd a),
      pairedMatrixWeyl K i*rawPairedHom K sigma false j (Multiplicative.ofAdd b)*(pairedMatrixWeyl K i)⁻¹⁆=
      rawPairedHom K sigma false j (Multiplicative.ofAdd (a*b)) := by
  apply mixed_of_positive
    (fun t=>rawPairedHom K sigma false i (Multiplicative.ofAdd t))
    (fun t=>rawPairedHom K sigma false j (Multiplicative.ofAdd t))
    (fun t=>rawPairedHom K sigma true i (Multiplicative.ofAdd t)) (pairedMatrixWeyl K i)
  · intro t u
    simpa only [mul_comm u t] using paired_adjacent_commutator K sigma i j hij t u
  · exact paired_self_root K sigma i
  · exact paired_adjacent_square_sign K sigma i j hij

end SymmetricSubgroupAsymptotics.CFSGE6GeckPairedMixedA2
