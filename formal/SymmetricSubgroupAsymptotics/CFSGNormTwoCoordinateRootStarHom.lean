import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarInjection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient
import Mathlib.GroupTheory.NoncommPiCoprod

/-! The actual positive root-star is an additive parameter subgroup.
Commutation is proved from the integral pairings, and injectivity is
proved from the genuine first-layer coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarHom
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinatePositivePairCommute CFSGNormTwoCoordinateRootStarInjection
open CFSGNormTwoCoordinateRootHeightQuotient
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K
variable (K : Type) [Field K] {n : ℕ} (f : Fin n→PositiveRoot A)
    (hpair : ∀i j,i≠j→integerPairing A (f i).val.val (f j).val.val=1)

private def tagPi : Multiplicative (Fin n→K)→*(Fin n→Multiplicative K) where
  toFun v j := Multiplicative.ofAdd (v.toAdd j)
  map_one' := rfl
  map_mul' _ _ := rfl

include hpair in
private theorem roots_commute : Pairwise (fun i j=>∀a b:Multiplicative K,
    Commute (selectedRootHom A hd hs hp ho K (f i).val a)
      (selectedRootHom A hd hs hp ho K (f j).val b)) := by
  intro i j hij a b
  exact positive_pair_commute A hd hs hp ho K (f i).val (f j).val
    (f i).property (f j).property (Or.inr (hpair i j hij)) a.toAdd b.toAdd

def rawHom : Multiplicative (Fin n→K)→*(CoordMat A hd hs hp ho K)ˣ :=
  (MonoidHom.noncommPiCoprod (fun j=>selectedRootHom A hd hs hp ho K (f j).val)
    (roots_commute A hd hs hp ho K f hpair)).comp (tagPi K)

theorem rawHom_apply (v : Fin n→K) :
    rawHom A hd hs hp ho K f hpair (Multiplicative.ofAdd v)=
      rootProduct A hd hs hp ho K (fun j=>(f j).val) v := by
  change Finset.univ.noncommProd
    (fun j=>selectedRootElement A hd hs hp ho K (f j).val (v j))
    (fun i _ j _ hij=>roots_commute A hd hs hp ho K f hpair hij
      (Multiplicative.ofAdd (v i)) (Multiplicative.ofAdd (v j)))=_
  rw [←List.toFinset_finRange n,Finset.noncommProd_toFinset _ _ _ (List.nodup_finRange n)]
  rw [←List.ofFn_eq_map]
  rfl

theorem rawHom_mem_positive (v : Multiplicative (Fin n→K)) :
    rawHom A hd hs hp ho K f hpair v∈PositiveGroup A hd hs hp ho K := by
  change Finset.univ.noncommProd
    (fun j=>selectedRootElement A hd hs hp ho K (f j).val (v.toAdd j))
    (fun i _ j _ hij=>roots_commute A hd hs hp ho K f hpair hij
      (Multiplicative.ofAdd (v.toAdd i)) (Multiplicative.ofAdd (v.toAdd j)))∈_
  apply Subgroup.noncommProd_mem
  intro j _
  exact selected_positive_root_mem A hd hs hp ho K (f j).val (f j).property (v.toAdd j)

def positiveHom : Multiplicative (Fin n→K)→*PositiveGroup A hd hs hp ho K :=
  (rawHom A hd hs hp ho K f hpair).codRestrict (PositiveGroup A hd hs hp ho K)
    (rawHom_mem_positive A hd hs hp ho K f hpair)

theorem rawHom_injective (H : (Fin r→ℤ)→+ℤ) (hf : Function.Injective f)
    (hH : ∀j,H (f j).val.val=1) : Function.Injective (rawHom A hd hs hp ho K f hpair) := by
  have hf' : Function.Injective (fun j=>(f j).val) := by
    intro i j he
    exact hf (Subtype.ext he)
  intro v w he
  apply Multiplicative.toAdd.injective
  apply rootProduct_injective A hd hs hp ho K H (fun j=>(f j).val) hf' hH
  rw [←rawHom_apply A hd hs hp ho K f hpair v.toAdd,
    ←rawHom_apply A hd hs hp ho K f hpair w.toAdd]
  exact he

theorem positiveHom_injective (H : (Fin r→ℤ)→+ℤ) (hf : Function.Injective f)
    (hH : ∀j,H (f j).val.val=1) : Function.Injective (positiveHom A hd hs hp ho K f hpair) := by
  intro v w he
  exact rawHom_injective A hd hs hp ho K f hpair H hf hH (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarHom
