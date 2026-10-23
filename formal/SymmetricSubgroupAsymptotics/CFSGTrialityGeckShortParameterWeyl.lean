import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections
import SymmetricSubgroupAsymptotics.CFSGOrthogonalTripleRankOneWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedTorus

/-! The actual parameterized short-orbit Weyl word is the product of
the three parameterized orthogonal rank-one words, and is the action of
a literal ORIGINAL fixed-subgroup word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGTrialityGeckOriginalFixedSections CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckFixedRootWords CFSGNormTwoGeckOrthogonalWeyl
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckParameterizedWeyl
open CFSGSerreOrdinaryTwists CFSGTrialityTripleFixedRoots CFSGSerreFixedRootElements

def unitFieldMap (K : Type) [Field K] (σ : K ≃+* K) : Kˣ →* Kˣ :=
  Units.map σ.toMonoidHom

theorem unitFieldMap_val (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :
    (unitFieldMap K σ a : K) = σ (a : K) := rfl

def outerParameters (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) : Fin 3 → Kˣ :=
  ![a,unitFieldMap K σ a,unitFieldMap K σ (unitFieldMap K σ a)]

theorem outer_roots_commute (K : Type) [CommRing K] (i j : Fin 3) (hij : i ≠ j)
    (e f : Bool) (a b : K) :
    Commute (canonicalRoot rawData K e (outerNode i) a)
      (canonicalRoot rawData K f (outerNode j) b) := by
  have hc : CFSGGeckSerreRepresentation.cartan Base Index (outerNode i) (outerNode j) = 0 := by
    rw [CFSGTrialityD4NormTwo.cartan_eq]
    exact outerNode_cartan i j hij
  exact orthogonal_signed_roots (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K (outerNode i) (outerNode j) hc e f a b

def shortWeylWord (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :=
  shortOrbit K σ false (a : K) * shortOrbit K σ true (-(a : K)⁻¹) *
    shortOrbit K σ false (a : K)

theorem shortWeylWord_eq_product (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :
    shortWeylWord K σ a =
      parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base Index K 0 a *
      parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base Index K 2 (unitFieldMap K σ a) *
      parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base Index K 3 (unitFieldMap K σ (unitFieldMap K σ a)) := by
  let x (k : Fin 3) := canonicalRoot rawData K false (outerNode k) (outerParameters K σ a k : K)
  let y (k : Fin 3) := canonicalRoot rawData K true (outerNode k) (-(outerParameters K σ a k : K)⁻¹)
  have hxx (i j : Fin 3) (hij : i ≠ j) : Commute (x i) (x j) :=
    outer_roots_commute K i j hij false false _ _
  have hxy (i j : Fin 3) (hij : i ≠ j) : Commute (x i) (y j) :=
    outer_roots_commute K i j hij false true _ _
  have he := CFSGOrthogonalTripleRankOneWord.rank_one_triple x y hxx hxy
  simpa only [x,y,outerParameters,outerNode,unitFieldMap_val,
    shortWeylWord,shortOrbit,parameterWeyl,map_neg,map_inv₀,
    Matrix.cons_val_zero,Matrix.cons_val_succ] using he

def sourceShortParameterWeyl (q : CFSG.PrimePower) (a : (q.Extension 3)ˣ) : Fixed q :=
  orbitRoot q false (a : q.Extension 3) * orbitRoot q true (-(a : q.Extension 3)⁻¹) *
    orbitRoot q false (a : q.Extension 3)

def matrixShortParameterWeyl (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) : MatrixGroup K :=
  matrixShortOrbit K σ false (a : K) * matrixShortOrbit K σ true (-(a : K)⁻¹) *
    matrixShortOrbit K σ false (a : K)

theorem matrixShortParameterWeyl_val (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :
    (matrixShortParameterWeyl K σ a).val = shortWeylWord K σ a := rfl

theorem original_short_orbit_action (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 3) :
    fixedImageAction q (orbitRoot q neg t) = matrixAction (q.Extension 3)
      (matrixShortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t) := by
  change imageRepresentation data (q.Extension 3)
    (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (orbitRoot q neg t)) = _
  rw [orbitRoot_toModel]
  simp only [map_mul,source_root_action,matrixShortOrbit,definingFieldAutomorphism_apply]

theorem sourceShortParameterWeyl_action (q : CFSG.PrimePower) (a : (q.Extension 3)ˣ) :
    fixedImageAction q (sourceShortParameterWeyl q a) = matrixAction (q.Extension 3)
      (matrixShortParameterWeyl (q.Extension 3) (definingFieldAutomorphism q 3) a) := by
  simp only [sourceShortParameterWeyl,matrixShortParameterWeyl,map_mul,original_short_orbit_action]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortParameterWeyl
