import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionFixedPositiveNegative
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl

/-! The actual opposite-unipotent generated subgroup and its outer
rank-one Weyl and torus words. All words belong to the original fixed
group; no ordinary F4 simplicity or middle Suzuki generation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterUnipotentGeneration
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGFFourOriginalMiddleWords
open CFSGReeFFourRelativeSimpleWeyl CFSGFFourOriginalParameterizedTorus
open CFSGReeFFourParameterizedTorusCovariance CFSGReeFFourFixedTorus
open CFSGFFourOriginalProductTorus CFSGFFourE6FixedGeneratedGroup
open CFSGNormTwoGeckOrthogonalWeyl CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckPositivePGroup
open CFSGExceptionalNormTwoBases
open CFSGTwistedE6GeckPositiveTwist
local notation "A" => CartanMatrix.F₄
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData

def oppositeGenerated (m : ℕ) : Subgroup (originalModelFixed m) :=
  fixedPositive m ⊔ fixedNegative m

theorem positive_le (m : ℕ) : fixedPositive m ≤ oppositeGenerated m := le_sup_left
theorem negative_le (m : ℕ) : fixedNegative m ≤ oppositeGenerated m := le_sup_right

private theorem outer_roots_commute (K : Type) [Field K] [Finite K] [CharP K 2]
    (neg neg' : Bool) (a b : K) :
    Commute (modelRoot A K neg 0 a) (modelRoot A K neg' 3 b) := by
  apply Commute.of_map (rawHom_injective K)
  simp only [rawHom_root, folded_root_eq_orbitParameter]
  change Commute (canonicalRoot R K neg 0 a * canonicalRoot R K neg 5 a)
    (canonicalRoot R K neg' 1 b)
  exact (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K 0 1 (by rw [E6_cartan]; decide)
      neg neg' a b).mul_left
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K 5 1 (by rw [E6_cartan]; decide)
        neg neg' a b)

def signedOuterWord (m : ℕ) (neg : Bool) (a : Field m) : Model A (Field m) :=
  modelRoot A (Field m) neg 0 a * modelRoot A (Field m) neg 3 (alpha m a)

theorem signedOuterWord_fixed (m : ℕ) (neg : Bool) (a : Field m) :
    reeAutomorphism m (signedOuterWord m neg a) = signedOuterWord m neg a := by
  simp only [signedOuterWord, map_mul, reeAutomorphism_root]
  change modelRoot A (Field m) neg 3 (alpha m a) *
      modelRoot A (Field m) neg 0 (beta m (alpha m a)) = _
  rw [beta_alpha]
  exact (outer_roots_commute (Field m) neg neg a (alpha m a)).eq.symm

def fixedSignedOuter (m : ℕ) (neg : Bool) (a : Field m) : originalModelFixed m :=
  ⟨signedOuterWord m neg a, signedOuterWord_fixed m neg a⟩

theorem fixedSignedOuter_mem (m : ℕ) (neg : Bool) (a : Field m) :
    fixedSignedOuter m neg a ∈ oppositeGenerated m := by
  have hraw : rawHom (Field m) (signedOuterWord m neg a) ∈
      rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index (Field m) neg := by
    simp only [signedOuterWord, map_mul, rawHom_root, folded_root_eq_orbitParameter]
    change (canonicalRoot R (Field m) neg 0 a * canonicalRoot R (Field m) neg 5 a) *
      canonicalRoot R (Field m) neg 1 (alpha m a) ∈ _
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨(0,a),rfl⟩)
        (Subgroup.subset_closure ⟨(5,a),rfl⟩))
      (Subgroup.subset_closure ⟨(1,alpha m a),rfl⟩)
  cases neg
  · exact positive_le m hraw
  · exact negative_le m hraw

def fixedOuterWeyl (m : ℕ) (a : (Field m)ˣ) : originalModelFixed m :=
  fixedSignedOuter m false (a : Field m) *
    fixedSignedOuter m true (-(a : Field m)⁻¹) * fixedSignedOuter m false (a : Field m)

theorem fixedOuterWeyl_mem (m : ℕ) (a : (Field m)ˣ) :
    fixedOuterWeyl m a ∈ oppositeGenerated m :=
  (oppositeGenerated m).mul_mem
    ((oppositeGenerated m).mul_mem (fixedSignedOuter_mem m false _)
      (fixedSignedOuter_mem m true _)) (fixedSignedOuter_mem m false _)

private theorem triple_interleave {G : Type*} [Group G] (x y u v : G)
    (hxu : Commute x u) (hyu : Commute y u) (hxv : Commute x v) :
    (x*y*x)*(u*v*u) = (x*u)*(y*v)*(x*u) := by
  calc
    _ = (x*(y*x))*(u*(v*u)) := by simp only [mul_assoc]
    _ = (x*u)*((y*x)*(v*u)) := (hyu.mul_left hxu).mul_mul_mul_comm _ _
    _ = (x*u)*((y*v)*(x*u)) := by rw [hxv.mul_mul_mul_comm]
    _ = _ := by simp only [mul_assoc]

theorem fixedOuterWeyl_val (m : ℕ) (a : (Field m)ˣ) :
    (fixedOuterWeyl m a).val = parameterWeyl (Field m) 0 a *
      parameterWeyl (Field m) 3 (unitPower m 0 a) := by
  have ha : (unitPower m 0 a : Field m) = alpha m (a : Field m) := rfl
  change signedOuterWord m false (a : Field m) *
    signedOuterWord m true (-(a : Field m)⁻¹) * signedOuterWord m false (a : Field m) = _
  simp only [signedOuterWord, parameterWeyl, ha, map_neg, map_inv₀]
  exact (triple_interleave _ _ _ _
    (outer_roots_commute (Field m) false false _ _)
    (outer_roots_commute (Field m) true false _ _)
    (outer_roots_commute (Field m) false true _ _)).symm

theorem fixedOuterWeyl_one_val (m : ℕ) :
    (fixedOuterWeyl m 1).val = outerRelativeWeyl m := by
  rw [fixedOuterWeyl_val]
  have hu : unitPower m 0 1 = 1 := by
    apply Units.ext
    change alpha m 1 = 1
    exact map_one _
  simp only [hu, parameterWeyl, Units.val_one, inv_one, outerRelativeWeyl, weyl]

theorem outerRelativeWeyl_mem (m : ℕ) :
    (⟨outerRelativeWeyl m, outerRelativeWeyl_fixed m⟩ : originalModelFixed m) ∈
      oppositeGenerated m := by
  have he : (⟨outerRelativeWeyl m, outerRelativeWeyl_fixed m⟩ : originalModelFixed m) =
      fixedOuterWeyl m 1 := Subtype.ext (fixedOuterWeyl_one_val m).symm
  rw [he]
  exact fixedOuterWeyl_mem m 1

private theorem parameterWeyl_one (K : Type) [Field K] [Finite K] [CharP K 2]
    (i : Fin 4) : parameterWeyl K i 1 = weyl K i := by
  simp only [parameterWeyl, Units.val_one, inv_one, weyl]

private theorem parameterTorus_one (K : Type) [Field K] [Finite K] [CharP K 2]
    (i : Fin 4) : parameterTorus K i 1 = 1 := by
  rw [parameterTorus, parameterWeyl_one, mul_inv_cancel]

private theorem unitPower_one (m : ℕ) (i : Fin 4) : unitPower m i 1 = 1 := by
  apply Units.ext
  rw [unitPower_val, Units.val_one, one_pow]

private theorem outer_parameterWeyls_commute (K : Type) [Field K] [Finite K] [CharP K 2]
    (a b : Kˣ) : Commute (parameterWeyl K 0 a) (parameterWeyl K 3 b) := by
  have hx (neg : Bool) (t : K) :
      Commute (modelRoot A K neg 0 t) (parameterWeyl K 3 b) := by
    unfold parameterWeyl
    exact ((outer_roots_commute K neg false _ _).mul_right
      (outer_roots_commute K neg true _ _)).mul_right
      (outer_roots_commute K neg false _ _)
  unfold parameterWeyl
  exact ((hx false _).mul_left (hx true _)).mul_left (hx false _)

theorem fixedTorus_outer_word (m : ℕ) (a : (Field m)ˣ) :
    fixedTorus m a 1 = fixedOuterWeyl m a * (fixedOuterWeyl m 1)⁻¹ := by
  apply Subtype.ext
  change (fixedTorus m a 1).val =
    (fixedOuterWeyl m a).val * ((fixedOuterWeyl m 1).val)⁻¹
  rw [fixedTorus_val, modelProductTorus_word, fixedOuterWeyl_val, fixedOuterWeyl_one_val]
  change parameterTorus (Field m) 0 a *
      (parameterTorus (Field m) 1 1 *
        (parameterTorus (Field m) 3 (unitPower m 0 a) *
          parameterTorus (Field m) 2 (unitPower m 1 1))) = _
  rw [unitPower_one, parameterTorus_one, parameterTorus_one, one_mul, mul_one]
  have hc : Commute (weyl (Field m) 0) (parameterWeyl (Field m) 3 (unitPower m 0 a)) := by
    rw [← parameterWeyl_one]
    exact outer_parameterWeyls_commute (Field m) 1 _
  unfold parameterTorus outerRelativeWeyl
  rw [hc.inv_left.mul_mul_mul_comm, mul_inv_rev]
  exact congrArg (fun z => (parameterWeyl (Field m) 0 a *
    parameterWeyl (Field m) 3 (unitPower m 0 a)) * z)
      (outer_weyls_commute (Field m)).inv_inv.eq

theorem fixedTorus_outer_mem (m : ℕ) (a : (Field m)ˣ) :
    fixedTorus m a 1 ∈ oppositeGenerated m := by
  rw [fixedTorus_outer_word]
  exact (oppositeGenerated m).mul_mem (fixedOuterWeyl_mem m a)
    ((oppositeGenerated m).inv_mem (fixedOuterWeyl_mem m 1))

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterUnipotentGeneration
