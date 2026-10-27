import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Sum

/-! A complete binomial indexing of all subsets, with cardinal preserved
by the first coordinate. No subset or multiplicity is omitted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteSubsetBinomialIndex
variable (J : Type*) [Fintype J]

def rank (s : Finset J) : Fin (Fintype.card J+1) :=
  ⟨s.card,Nat.lt_succ_of_le (Finset.card_le_univ s)⟩

def fibreEquiv (k : Fin (Fintype.card J+1)) :
    {s : Finset J // rank J s=k} ≃ {s : Finset J // s.card=k.val} where
  toFun s := ⟨s.val,congrArg Fin.val s.property⟩
  invFun s := ⟨s.val,Fin.ext s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def index : Set J ≃
    (Σ k : Fin (Fintype.card J+1), Fin ((Fintype.card J).choose k.val)) :=
  (Fintype.finsetEquivSet.symm.trans (Equiv.sigmaFiberEquiv (rank J)).symm).trans
    (Equiv.sigmaCongrRight fun k => (fibreEquiv J k).trans
      (Fintype.equivFinOfCardEq (Fintype.card_finset_len (α:=J) k.val)))

theorem index_rank (s : Set J) : (index J s).1.val=s.toFinset.card := rfl

end SymmetricSubgroupAsymptotics.FiniteSubsetBinomialIndex
