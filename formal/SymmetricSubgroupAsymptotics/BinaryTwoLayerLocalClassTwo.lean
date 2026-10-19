import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic

/-! A selected four-point local calculation, not a subgroup census. Every
permutation preserving the two physical pairs is retained. In particular
no split or elementary assumption on a subgroup is made. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalClassTwo

abbrev Points := ZMod 2 × ZMod 2

instance pointsPermFintype : Fintype (Equiv.Perm Points) := fintypePerm

def Preserves (a : Equiv.Perm Points) : Prop :=
  ∀ x y : Points, x.1=y.1 → (a x).1=(a y).1

/-- The two literal row tests avoid nested quantified decision instances. -/
def PairRows (a : Equiv.Perm Points) : Prop :=
  (a (0,0)).1=(a (0,1)).1 ∧ (a (1,0)).1=(a (1,1)).1

instance pairRowsDecidable (a : Equiv.Perm Points) : Decidable (PairRows a) := by
  unfold PairRows
  infer_instance

theorem preserves_iff_pairRows (a : Equiv.Perm Points) : Preserves a ↔ PairRows a := by
  constructor
  · intro h
    exact ⟨h (0,0) (0,1) rfl,h (1,0) (1,1) rfl⟩
  · intro h x y hxy
    rcases h with ⟨h0,h1⟩
    rcases x with ⟨x,b⟩
    rcases y with ⟨y,c⟩
    fin_cases x <;> fin_cases y <;> fin_cases b <;> fin_cases c <;>
      simp_all <;> first | exact h0 | exact h0.symm | exact h1 | exact h1.symm

instance preservesDecidable (a : Equiv.Perm Points) : Decidable (Preserves a) :=
  decidable_of_iff (PairRows a) (preserves_iff_pairRows a).symm

private def localDiagonal : Equiv.Perm Points where
  toFun x := (x.1,x.2+1)
  invFun x := (x.1,x.2+1)
  left_inv := by intro x; revert x; decide +kernel
  right_inv := by intro x; revert x; decide +kernel

/-- The two-permutation calculation is separated from centrality. -/
private theorem local_commutator_cases :
    ∀ a b : Equiv.Perm Points, PairRows a → PairRows b →
      a*b*a⁻¹*b⁻¹=1 ∨ a*b*a⁻¹*b⁻¹=localDiagonal := by
  unfold PairRows
  decide +kernel

private theorem local_diagonal_commutes :
    ∀ c : Equiv.Perm Points, PairRows c → localDiagonal*c=c*localDiagonal := by
  unfold PairRows
  decide +kernel

/-- The commutator of two actual pair-preserving four-point permutations
commutes with every other such permutation. The finite pilot is split into
24^2 cases and 24 cases, rather than one 24^3 reduction. -/
theorem commutator_central :
    ∀ a b c : Equiv.Perm Points, Preserves a → Preserves b → Preserves c →
      (a*b*a⁻¹*b⁻¹)*c=c*(a*b*a⁻¹*b⁻¹) := by
  intro a b c ha hb hc
  rcases local_commutator_cases a b ((preserves_iff_pairRows a).mp ha)
    ((preserves_iff_pairRows b).mp hb) with h | h
  · rw [h]
    simp only [one_mul,mul_one]
  · rw [h]
    exact local_diagonal_commutes c ((preserves_iff_pairRows c).mp hc)

end SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalClassTwo
