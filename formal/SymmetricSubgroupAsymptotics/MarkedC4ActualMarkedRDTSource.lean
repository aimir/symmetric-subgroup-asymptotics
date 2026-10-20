import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkerCoordinateImages
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedSourceRegrouping
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual marked source geometry for ordinary RDT4.6. The independent
physical tail remains on P. Dependent physical factors and ACTUAL marker
coordinate images form the bounded R-side, including vertical markers. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedRDTSource
open ActualGlobalMarkGeneratorRank ActualMarkerCoordinateImages

variable {s u : ℕ} (R : Fin s → Type) [∀ i,Group (R i)] [∀ i,Finite (R i)]
  (P : Fin u → Type) [∀ j,Group (P j)] [∀ j,Finite (P j)]
  (r : ℕ) (A : Subgroup (((∀ i,R i) × (∀ j,P j)) × Marks r))

def physicalFactor (i : Fin s) : A →* R i where
  toFun a := a.val.1.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

def tail : A →* (∀ j,P j) where
  toFun a := a.val.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

def SumFactor : Fin s ⊕ Fin r → Type
  | .inl i => R i
  | .inr j => Factor r A j
instance sumFactorGroup (i : Fin s ⊕ Fin r) : Group (SumFactor R P r A i) := by
  cases i <;> dsimp [SumFactor] <;> infer_instance
instance sumFactorFinite (i : Fin s ⊕ Fin r) : Finite (SumFactor R P r A i) := by
  cases i <;> dsimp [SumFactor] <;> infer_instance

def factorMap : (i : Fin s ⊕ Fin r) → A →* SumFactor R P r A i
  | .inl i => physicalFactor R P r A i
  | .inr j => ontoFactor r A j

abbrev Factors (k : Fin (s+r)) := SumFactor R P r A (finSumFinEquiv.symm k)
def rho : A →* ∀ k,Factors R P r A k where
  toFun a k := factorMap R P r A (finSumFinEquiv.symm k) a
  map_one' := by funext k; exact (factorMap R P r A _).map_one
  map_mul' a b := by funext k; exact (factorMap R P r A _).map_mul a b

abbrev Left := (rho R P r A).range
def regroup : A →* Left R P r A × (∀ j,P j) :=
  (rho R P r A).rangeRestrict.prod (tail R P r A)

theorem regroup_injective : Function.Injective (regroup R P r A) := by
  intro x y he
  have hrho : rho R P r A x=rho R P r A y :=
    congrArg (fun z : Left R P r A × (∀ j,P j) => z.1.val) he
  have hp : x.val.1.2=y.val.1.2 :=
    congrArg (fun z : Left R P r A × (∀ j,P j) => z.2) he
  have hf (i : Fin s ⊕ Fin r) : factorMap R P r A i x=factorMap R P r A i y := by
    have hi := congrFun hrho (finSumFinEquiv i)
    change factorMap R P r A (finSumFinEquiv.symm (finSumFinEquiv i)) x=
      factorMap R P r A (finSumFinEquiv.symm (finSumFinEquiv i)) y at hi
    rw [Equiv.symm_apply_apply] at hi
    exact hi
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · funext i
      exact hf (.inl i)
    · exact hp
  · apply Multiplicative.toAdd.injective
    funext j
    exact congrArg Multiplicative.toAdd (congrArg Subtype.val (hf (.inr j)))

abbrev Source := (regroup R P r A).range
def sourceEquiv : A ≃* Source R P r A :=
  MonoidHom.ofInjective (regroup_injective R P r A)

omit [∀ i,Finite (R i)] [∀ j,Finite (P j)] in
/-- The actual R-side is a literal subdirect product of the bounded
physical quotients and the actual marker coordinate images. -/
theorem left_subdirect (hR : ∀ i,Function.Surjective (physicalFactor R P r A i))
    (k : Fin (s+r)) : Function.Surjective
      ((Pi.evalMonoidHom (Factors R P r A) k).comp (Left R P r A).subtype) := by
  intro x
  have hfactor (i : Fin s ⊕ Fin r) : Function.Surjective (factorMap R P r A i) := by
    cases i with
    | inl i => exact hR i
    | inr j => exact ontoFactor_surjective r A j
  obtain ⟨a,ha⟩ := hfactor (finSumFinEquiv.symm k) x
  exact ⟨⟨rho R P r A a,⟨a,rfl⟩⟩,ha⟩

omit [∀ i,Finite (R i)] [∀ j,Finite (P j)] in
theorem source_tail_surjective (hP : Function.Surjective (tail R P r A)) :
    Function.Surjective ((MonoidHom.snd (Left R P r A) (∀ j,P j)).comp
      (Source R P r A).subtype) := by
  intro p
  obtain ⟨a,ha⟩ := hP p
  exact ⟨⟨regroup R P r A a,⟨a,rfl⟩⟩,ha⟩

omit [∀ i,Finite (R i)] [∀ j,Finite (P j)] in
/-- The extra r marker factors have fixed order at most four. -/
theorem factors_card_le (k : ℕ) (hk : 2≤k)
    (hR : ∀ i,Nat.card (R i)≤2^k) (i : Fin (s+r)) :
    Nat.card (Factors R P r A i)≤2^k := by
  change Nat.card (SumFactor R P r A (finSumFinEquiv.symm i))≤2^k
  generalize finSumFinEquiv.symm i=j
  cases j with
  | inl j => exact hR j
  | inr j => exact factor_card_le_cutoff r A k hk j

omit [∀ i,Finite (R i)] [∀ j,Finite (P j)] in
theorem factors_binary (hR : ∀ i,IsPGroup 2 (R i)) (i : Fin (s+r)) :
    IsPGroup 2 (Factors R P r A i) := by
  change IsPGroup 2 (SumFactor R P r A (finSumFinEquiv.symm i))
  generalize finSumFinEquiv.symm i=j
  cases j with
  | inl j => exact hR j
  | inr j => exact factor_binary r A j

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedRDTSource
