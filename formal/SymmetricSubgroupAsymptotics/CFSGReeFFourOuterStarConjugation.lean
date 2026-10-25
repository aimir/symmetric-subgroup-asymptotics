import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarRootActions
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSimpleConjugation
import SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation

/-! Literal root-GROUP conjugation on the selected four-root E6 slice.
The coordinate shears and swaps are bound to actual selected root units
by the proved A2 and Weyl identities, not inferred from one-column tests.
No assertion is made about the other head pieces or higher layers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalChainStarData CFSGReeFFourOuterStarColumns
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootStarHom
open CFSGNormTwoCoordinateChainStarRootActions CFSGNormTwoCoordinateChainStarStrings
open CFSGNormTwoCoordinateCharTwoSimpleConjugation CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinatePositivePairCommute
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def starHom (K : Type) [Field K] :
    Multiplicative (Fin 4 → K) →* (Matrix GeckIndex GeckIndex K)ˣ :=
  CFSGNormTwoCoordinateRootStarHom.rawHom A hd hs hp ho K leftStar.root
    (fun i j hij => leftStar.pair i j hij)

private theorem star_commute (K : Type) [Field K] :
    Pairwise (fun i j : Fin 4 => ∀ a b : Multiplicative K,
      Commute (selectedRootHom A hd hs hp ho K (leftStar.root i).val a)
        (selectedRootHom A hd hs hp ho K (leftStar.root j).val b)) := by
  intro i j hij a b
  exact positive_pair_commute A hd hs hp ho K (leftStar.root i).val (leftStar.root j).val
    (leftStar.root i).property (leftStar.root j).property
    (Or.inr (leftStar.pair i j hij)) a.toAdd b.toAdd

private theorem starHom_add (K : Type) [Field K] (v w : Fin 4 → K) :
    starHom K (Multiplicative.ofAdd (v+w)) =
      starHom K (Multiplicative.ofAdd v) * starHom K (Multiplicative.ofAdd w) :=
  (starHom K).map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem starHom_single (K : Type) [Field K] (k : Fin 4) (a : K) :
    starHom K (Multiplicative.ofAdd (Pi.single k a)) =
      selectedRootElement A hd hs hp ho K (leftStar.root k).val a := by
  change (MonoidHom.noncommPiCoprod (M := (Matrix GeckIndex GeckIndex K)ˣ)
    (fun i : Fin 4 => selectedRootHom A hd hs hp ho K (leftStar.root i).val)
    (star_commute K))
    (fun j : Fin 4 => Multiplicative.ofAdd ((Pi.single k a : Fin 4 → K) j)) = _
  have hv : (fun j : Fin 4 => Multiplicative.ofAdd ((Pi.single k a : Fin 4 → K) j)) =
      Pi.mulSingle k (Multiplicative.ofAdd a) := by
    funext j
    by_cases hj : j=k
    · subst j
      rw [Pi.single_eq_same,Pi.mulSingle_eq_same]
    · rw [Pi.single_eq_of_ne hj,Pi.mulSingle_eq_of_ne hj]
      rfl
  rw [hv]
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _

def shearCoordinates (K : Type) [Field K] (j : Fin 3) (t : K) :
    (Fin 4 → K) ≃+ (Fin 4 → K) :=
  (CFSGTypeAElementaryMatrices.elementary (i := j.succ) (j := j.castSucc)
    ((ne_of_lt j.castSucc_lt_succ).symm) t).toLin'.toAddEquiv

theorem shearCoordinates_apply (K : Type) [Field K] (j : Fin 3) (t : K) (v : Fin 4 → K) :
    shearCoordinates K j t v = v + Pi.single j.succ (t*v j.castSucc) :=
  CFSGAdditiveParameterConjugation.elementary_apply ((ne_of_lt j.castSucc_lt_succ).symm) t v

def swapCoordinates (K : Type) [Field K] (j : Fin 3) :
    (Fin 4 → K) ≃+ (Fin 4 → K) where
  toFun v k := v (Equiv.swap j.castSucc j.succ k)
  invFun v k := v (Equiv.swap j.castSucc j.succ k)
  left_inv v := by ext k; simp only [Equiv.swap_apply_self]
  right_inv v := by ext k; simp only [Equiv.swap_apply_self]
  map_add' _ _ := rfl

private theorem swapCoordinates_single (K : Type) [Field K] (j : Fin 3) (k : Fin 4) (a : K) :
    swapCoordinates K j (Pi.single k a) =
      Pi.single (Equiv.swap j.castSucc j.succ k) a := by
  ext l
  change (Pi.single k a : Fin 4 → K) (Equiv.swap j.castSucc j.succ l) =
    (Pi.single (Equiv.swap j.castSucc j.succ k) a : Fin 4 → K) l
  simp only [Pi.single_apply]
  have he : Equiv.swap j.castSucc j.succ l=k ↔ l=Equiv.swap j.castSucc j.succ k := by
    constructor
    · intro h
      have hh := congrArg (Equiv.swap j.castSucc j.succ) h
      simpa only [Equiv.swap_apply_self] using hh
    · intro h
      rw [h,Equiv.swap_apply_self]
  by_cases hl : l=Equiv.swap j.castSucc j.succ k
  · rw [if_pos (he.mpr hl),if_pos hl]
  · rw [if_neg (fun h => hl (he.mp h)),if_neg hl]

private theorem commute_conjugate {G : Type*} [Group G] (u x : G)
    (h : Commute u x) : u*x*u⁻¹=x := by
  rw [h.eq,mul_assoc,mul_inv_cancel,mul_one]

theorem simple_conjugate (K : Type) [Field K] [CharP K 2]
    (j : Fin 3) (t : K) (v : Fin 4 → K) :
    canonicalRoot rawData K false (leftStar.step j) t *
      starHom K (Multiplicative.ofAdd v) *
        (canonicalRoot rawData K false (leftStar.step j) t)⁻¹ =
      starHom K (Multiplicative.ofAdd (shearCoordinates K j t v)) := by
  apply CFSGAdditiveParameterConjugation.conjugation_of_single
    (starHom K) (shearCoordinates K j t)
    (canonicalRoot rawData K false (leftStar.step j) t)
  intro k a
  rw [starHom_single]
  by_cases hk : k=j.castSucc
  · subst k
    have hvec : shearCoordinates K j t (Pi.single j.castSucc a) =
        Pi.single j.castSucc a + Pi.single j.succ (t*a) := by
      rw [shearCoordinates_apply,Pi.single_eq_same]
    rw [hvec]
    rw [starHom_add,starHom_single,starHom_single]
    have hpair : integerPairing A (leftStar.root j.castSucc).val.val
        (E6Index (leftStar.step j) : Roots A).val = -1 := by
      exact (simple_pair A hd hs hp ho leftStar j j.castSucc).trans (by simp)
    have hc := simple_positive_conjugate A hd hs hp ho K
      (leftStar.root j.castSucc).val (leftStar.root j.castSucc).property
      (leftStar.step j) hpair t a
    rw [raised_root A hd hs hp ho leftStar j hpair] at hc
    exact hc
  · have hvec : shearCoordinates K j t (Pi.single k a) = Pi.single k a := by
      simp only [shearCoordinates_apply,Pi.single_eq_of_ne (Ne.symm hk),mul_zero,
        Pi.single_zero,add_zero]
    rw [hvec,starHom_single]
    have hc := other_root_commutes A hd hs hp ho leftStar K j k hk t a
    exact commute_conjugate _ _ hc

theorem weyl_conjugate (K : Type) [Field K] [CharP K 2]
    (j : Fin 3) (v : Fin 4 → K) :
    canonicalWeyl rawData K (leftStar.step j) * starHom K (Multiplicative.ofAdd v) *
        (canonicalWeyl rawData K (leftStar.step j))⁻¹ =
      starHom K (Multiplicative.ofAdd (swapCoordinates K j v)) := by
  apply CFSGAdditiveParameterConjugation.conjugation_of_single
    (starHom K) (swapCoordinates K j) (canonicalWeyl rawData K (leftStar.step j))
  intro k a
  rw [starHom_single,swapCoordinates_single,starHom_single]
  obtain ⟨e,he,hc⟩ := simple_weyl_sign A hd hs hp ho leftStar j k
  have hsign : (e : K)=1 := by
    rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have hh := hc K a
  rw [hsign,one_mul] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarConjugation
