import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTuple
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope
import SymmetricSubgroupAsymptotics.CFSGProductTorusAction

/-! The four literal D4 rank-one tori realize the folded G2 Cartan
scalar map on both signs. Compatible tuples factor as the actual short
orbit torus and the central-node torus; this is a matrix-word identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProductTorus
open CFSGGTwoD4GeckScalarTorus CFSGGTwoD4GeckScalarTuple
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckShortTorusConjugation CFSGTrialityGeckShortParameterWeyl
open CFSGNormTwoGeckTorusHom CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckDiagonalTorus
open CFSGNormTwoCoordinateSignedTorusConjugation CFSGNormTwoGeckBorelEnvelope
open CFSGProductTorusAction CFSGIntegerMatrixPowerHom CFSGIntegerMatrixPairing
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.D 4
variable (K : Type) [Field K]

def simpleTorusHom (i : Fin 4) : Kˣ→*(Matrix GeckIndex GeckIndex K)ˣ :=
  parameterTorusHom A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i

theorem simple_tori_commute : Pairwise fun i j=>∀t u,
    Commute (simpleTorusHom K i t) (simpleTorusHom K j u) := by
  intro i j _ t u
  change _*_=_*_
  apply Units.ext
  simp only [Units.val_mul,simpleTorusHom,parameterTorusHom_apply,
    torus_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

def rawProductTorus : (Fin 4→Kˣ)→*(Matrix GeckIndex GeckIndex K)ˣ :=
  productTorusHom (simpleTorusHom K) (simple_tori_commute K)

@[simp] theorem rawProductTorus_mulSingle (i : Fin 4) (t : Kˣ) :
    rawProductTorus K (Pi.mulSingle i t)=
      parameterTorus A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i t := by
  exact (MonoidHom.noncommPiCoprod_mulSingle (hcomm:=simple_tori_commute K)
    (simpleTorusHom K) i t).trans (parameterTorusHom_apply _ _ _ _ _ K i t)

theorem rawProductTorus_mem_torus (x : Fin 4→Kˣ) :
    rawProductTorus K x∈torusGroup A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K := by
  let T := torusGroup A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K
  apply Pi.mulSingle_induction (fun y : Fin 4→Kˣ=>rawProductTorus K y∈T) x
  · rw [map_one]
    exact T.one_mem
  · intro y z hy hz
    rw [map_mul]
    exact T.mul_mem hy hz
  · intro i t
    rw [rawProductTorus_mulSingle]
    exact Subgroup.subset_closure ⟨(i,t),rfl⟩

private def rawSimpleHom (neg : Bool) (j : Fin 4) :
    Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ where
  toFun t := canonicalRoot rawData K neg j t.toAdd
  map_one' := canonicalRoot_zero rawData K neg j
  map_mul' t u := (canonicalRoot_add rawData K neg j t.toAdd u.toAdd).symm

private theorem simple_pairing (i j : Fin 4) :
    integerPairing A (Index i : Roots A).val (Index j : Roots A).val=A j i := by
  change integerPairing A (Pi.single i 1) (Pi.single j 1)=A j i
  simp only [integerPairing,Matrix.toBilin'_single]
  exact (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ=>M i j) (CartanMatrix.D_transpose 4)).symm

theorem rawProductTorus_signed_action (x : Fin 4→Kˣ) (neg : Bool) (j : Fin 4) (a : K) :
    rawProductTorus K x*canonicalRoot rawData K neg j a*(rawProductTorus K x)⁻¹=
      canonicalRoot rawData K neg j (a*(if neg then (powerHom (G:=Kˣ) A x j : K)⁻¹
        else (powerHom (G:=Kˣ) A x j : K))) := by
  have he := product_action (simpleTorusHom K) (simple_tori_commute K) (if neg then -A else A)
    (rawSimpleHom K neg) (by
      intro i t k b
      change parameterTorusHom A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i t*
          canonicalRoot rawData K neg k b*
          (parameterTorusHom A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i t)⁻¹=_
      rw [parameterTorusHom_apply]
      have hsigned := torus_conjugate_signed A (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K i k t neg b
      change parameterTorus A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i t*
          canonicalRoot rawData K neg k b*
          (parameterTorus A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i t)⁻¹=
        canonicalRoot rawData K neg k (b*(t : K)^(if neg then
          -integerPairing A (Index i : Roots A).val (Index k : Roots A).val
          else integerPairing A (Index i : Roots A).val (Index k : Roots A).val)) at hsigned
      rw [simple_pairing] at hsigned
      cases neg <;> exact hsigned) x j a
  cases neg
  · exact he
  · change rawProductTorus K x*canonicalRoot rawData K true j a*(rawProductTorus K x)⁻¹=
      canonicalRoot rawData K true j (a*(powerHom (G:=Kˣ) (-A) x j : K)) at he
    have hp : powerHom (G:=Kˣ) (-A) x j=(powerHom (G:=Kˣ) A x j)⁻¹ := by
      simp only [powerHom_apply,Matrix.neg_apply,zpow_neg,Finset.prod_inv_distrib]
    rw [hp] at he
    simpa only [if_true,Units.val_inv_eq_inv_val] using he

theorem rawProductTorus_orbit_factors (x : Fin 2→Kˣ) :
    rawProductTorus K (scalarTupleHom x)=shortTorusWord K (RingEquiv.refl K) (x 0)*
      parameterTorus A (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K 1 (x 1) := by
  have hd : scalarTupleHom x=
      ((Pi.mulSingle 0 (x 0)*Pi.mulSingle 2 (x 0))*Pi.mulSingle 3 (x 0))*Pi.mulSingle 1 (x 1) := by
    funext i
    fin_cases i <;> norm_num [scalarTupleHom,Pi.mulSingle_apply,Fin.ext_iff]
  rw [hd]
  simp only [map_mul,rawProductTorus_mulSingle]
  rw [shortTorusWord_eq_product]
  rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProductTorus
