import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeRootActions
import SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive

/-! The commuting six-root parameter group and its exact middle-simple
conjugation actions. This is the node-1 component required for the WHOLE
outer-word y/r identity; it is not an intrinsic head-rank identification.
No selected E6 factor is asserted exceptional-fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeConjugation
open CFSGReeFFourOuterWedgeRootData CFSGReeFFourOuterWedgeRootActions
open CFSGReeFFourOuterStarColumns CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePairCommute CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K

private theorem roots_commute (K : Type) [Field K] :
    Pairwise (fun i j : Fin 6=>∀a b : Multiplicative K,
      Commute (selectedRootHom A hd hs hp ho K (wedgeRoot i).val a)
        (selectedRootHom A hd hs hp ho K (wedgeRoot j).val b)) := by
  intro i j hij a b
  exact positive_pair_commute A hd hs hp ho K _ _
    (wedgeRoot i).property (wedgeRoot j).property
    (pair_zero_or_one i j hij) a.toAdd b.toAdd

def wedgeHom (K : Type) [Field K] :
    Multiplicative (Fin 6→K)→*(Mat K)ˣ :=
  (MonoidHom.noncommPiCoprod (fun i : Fin 6=>selectedRootHom A hd hs hp ho K (wedgeRoot i).val)
    (roots_commute K)).comp (MulEquiv.piMultiplicative (fun _ : Fin 6=>K)).toMonoidHom

theorem wedgeHom_single (K : Type) [Field K] (k : Fin 6) (a : K) :
    wedgeHom K (Multiplicative.ofAdd (Pi.single k a))=parameter K k a := by
  change (MonoidHom.noncommPiCoprod (M := (Mat K)ˣ)
    (fun i : Fin 6=>selectedRootHom A hd hs hp ho K (wedgeRoot i).val)
    (roots_commute K)) (fun j : Fin 6=>Multiplicative.ofAdd ((Pi.single k a : Fin 6→K) j))=_
  have hv : (fun j : Fin 6=>Multiplicative.ofAdd ((Pi.single k a : Fin 6→K) j))=
      Pi.mulSingle k (Multiplicative.ofAdd a) := by
    funext j
    by_cases hj : j=k
    · subst j
      rw [Pi.single_eq_same,Pi.mulSingle_eq_same]
    · rw [Pi.single_eq_of_ne hj,Pi.mulSingle_eq_of_ne hj]
      rfl
  rw [hv]
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _

private theorem wedgeHom_add (K : Type) [Field K] (v w : Fin 6→K) :
    wedgeHom K (Multiplicative.ofAdd (v+w))=
      wedgeHom K (Multiplicative.ofAdd v)*wedgeHom K (Multiplicative.ofAdd w) :=
  (wedgeHom K).map_mul _ _

private theorem target_source_ne (j : Fin 3) (b : Fin 2) :
    raiseTarget j b≠raiseSource j b := by
  fin_cases j <;> fin_cases b <;> decide

private abbrev elementaryShear (K : Type) [Field K] (j : Fin 3) (b : Fin 2) (t : K) :
    AddAut (Fin 6→K) :=
  (CFSGTypeAElementaryMatrices.elementary (target_source_ne j b) t).toLin'.toAddEquiv

private theorem elementaryShear_apply (K : Type) [Field K] (j : Fin 3) (b : Fin 2)
    (t : K) (v : Fin 6→K) :
    elementaryShear K j b t v=v+Pi.single (raiseTarget j b) (t*v (raiseSource j b)) :=
  CFSGAdditiveParameterConjugation.elementary_apply (target_source_ne j b) t v

def shearCoordinates (K : Type) [Field K] (j : Fin 3) (t : K) : AddAut (Fin 6→K) :=
  elementaryShear K j 0 t*elementaryShear K j 1 t

private theorem shear_single (K : Type) [Field K] (j : Fin 3) (k : Fin 6) (t a : K) :
    shearCoordinates K j t (Pi.single k a)=
      if k=raiseSource j 0 then Pi.single k a+Pi.single (raiseTarget j 0) (t*a)
      else if k=raiseSource j 1 then Pi.single k a+Pi.single (raiseTarget j 1) (t*a)
      else Pi.single k a := by
  fin_cases j <;> fin_cases k <;> ext l <;> fin_cases l <;>
    simp [shearCoordinates,elementaryShear_apply,AddAut.mul_apply,
      raiseSource,raiseTarget,Pi.single_apply]

def swapCoordinates (K : Type) [Field K] (j : Fin 3) : AddAut (Fin 6→K) where
  toFun v k := v ((wedgeSwap j).symm k)
  invFun v k := v (wedgeSwap j k)
  left_inv v := by ext k; simp only [Equiv.symm_apply_apply]
  right_inv v := by ext k; simp only [Equiv.apply_symm_apply]
  map_add' _ _ := rfl

private theorem swap_single (K : Type) [Field K] (j : Fin 3) (k : Fin 6) (a : K) :
    swapCoordinates K j (Pi.single k a)=Pi.single (wedgeSwap j k) a := by
  ext l
  change (Pi.single k a : Fin 6→K) ((wedgeSwap j).symm l)=_
  simp only [Pi.single_apply]
  have he : (wedgeSwap j).symm l=k ↔ l=wedgeSwap j k := by
    constructor
    · intro h
      exact ((wedgeSwap j).apply_symm_apply l).symm.trans (congrArg (wedgeSwap j) h)
    · intro h
      exact (congrArg (wedgeSwap j).symm h).trans ((wedgeSwap j).symm_apply_apply k)
  by_cases hl : l=wedgeSwap j k
  · rw [if_pos (he.mpr hl),if_pos hl]
  · rw [if_neg (fun h=>hl (he.mp h)),if_neg hl]

theorem simple_conjugate (K : Type) [Field K] [CharP K 2]
    (j : Fin 3) (t : K) (v : Fin 6→K) :
    canonicalRoot rawData K false (leftStar.step j) t*wedgeHom K (Multiplicative.ofAdd v)*
      (canonicalRoot rawData K false (leftStar.step j) t)⁻¹=
      wedgeHom K (Multiplicative.ofAdd (shearCoordinates K j t v)) := by
  apply CFSGAdditiveParameterConjugation.conjugation_of_single
    (wedgeHom K) (shearCoordinates K j t)
    (canonicalRoot rawData K false (leftStar.step j) t)
  intro k a
  rw [wedgeHom_single,shear_single]
  by_cases hk0 : k=raiseSource j 0
  · rw [if_pos hk0,wedgeHom_add,wedgeHom_single,wedgeHom_single]
    subst k
    exact simple_raise K j 0 t a
  · rw [if_neg hk0]
    by_cases hk1 : k=raiseSource j 1
    · rw [if_pos hk1,wedgeHom_add,wedgeHom_single,wedgeHom_single]
      subst k
      exact simple_raise K j 1 t a
    · rw [if_neg hk1,wedgeHom_single]
      exact simple_fixed K j k (fun h=>h.elim hk0 hk1) t a

theorem weyl_conjugate (K : Type) [Field K] [CharP K 2]
    (j : Fin 3) (v : Fin 6→K) :
    canonicalWeyl rawData K (leftStar.step j)*wedgeHom K (Multiplicative.ofAdd v)*
      (canonicalWeyl rawData K (leftStar.step j))⁻¹=
      wedgeHom K (Multiplicative.ofAdd (swapCoordinates K j v)) := by
  apply CFSGAdditiveParameterConjugation.conjugation_of_single
    (wedgeHom K) (swapCoordinates K j) (canonicalWeyl rawData K (leftStar.step j))
  intro k a
  rw [wedgeHom_single,swap_single,wedgeHom_single]
  exact CFSGReeFFourOuterWedgeRootActions.weyl_conjugate K j k a

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeConjugation
