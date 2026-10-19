import SymmetricSubgroupAsymptotics.MarkedC4ActualDerivedNormalQuotientLift
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedNormalBudgetTransport
import Mathlib.Algebra.Order.Floor.Semiring

/-! The actual marked dN budget is constructed as a natural floor of the
sum of ORIGINAL dependent degrees/4. No marked normal-rank cap is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualQuotientMarkedNormalBudget
open ActualMarkZeroNormalRank ActualSubdirectFiltration

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  {M : Type} [CommGroup M] [Finite M] (A : Subgroup ((∀ i,F i) × M))
  (tail : Finset (Fin t))

def tailHom : PhysicalImage A →* ∀ i : {j // j∈tail},F i.val where
  toFun x i := x.val i.val
  map_one' := rfl
  map_mul' _ _ := rfl

def budget (weight : Fin t → ℕ) : ℝ :=
  ∑ i : Fin t,if i∈tail then 0 else (weight i : ℝ)/4
def dN (weight : Fin t → ℕ) : ℕ := ⌊budget tail weight⌋₊

theorem dN_cap (weight : Fin t → ℕ) : (dN tail weight : ℝ)≤budget tail weight := by
  apply Nat.floor_le
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> positivity

/-- Literal physical full-coordinate projections remain onto in the
ACTUAL physical image, independently of all marker behaviour. -/
theorem physical_image_full
    (hfull : ∀ i,Function.Surjective ((Pi.evalMonoidHom F i).comp (physical A)))
    (i : Fin t) : Function.Surjective (coordinate F (PhysicalImage A) i) := by
  intro q
  obtain ⟨a,ha⟩ := hfull i q
  exact ⟨projection A a,ha⟩

/-- Original-factor derived-normal bounds descend to quotient diagonals,
are summed along the actual source filtration, and survive the global mark. -/
theorem marked_budget (K : Fin t → Type) [∀ i,Group (K i)] [∀ i,Finite (K i)]
    (quotient : ∀ i,K i →* F i) (onto : ∀ i,Function.Surjective (quotient i))
    (weight : Fin t → ℕ)
    (horiginal : ∀ (i : Fin t) (N : Subgroup (K i)),N.Normal →
      N≤commutator (K i) →(normalGen N : ℝ)≤(weight i : ℝ)/4)
    (hfull : ∀ i,Function.Surjective ((Pi.evalMonoidHom F i).comp (physical A))) :
    ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ ((tailHom F A tail).comp (projection A)).ker →
      normalGen U≤dN tail weight := by
  apply ActualMarkedNormalBudgetTransport.marked_normal_budget A (tailHom F A tail)
  intro V hVn hV
  letI : V.Normal := hVn
  have hzero : ∀ i∈tail,∀ x∈V,coordinate F (PhysicalImage A) i x=1 := by
    intro i hi x hx
    have ht : tailHom F A tail x=1 := (hV hx).2
    exact congrFun ht ⟨i,hi⟩
  have hreal := ActualDerivedNormalQuotientLift.quotient_word_budget K F quotient onto
    (PhysicalImage A) (physical_image_full F A hfull) tail (fun i => (weight i : ℝ))
    horiginal V (hV.trans inf_le_left) hzero
  exact Nat.le_floor hreal

end SymmetricSubgroupAsymptotics.MarkedC4.ActualQuotientMarkedNormalBudget
