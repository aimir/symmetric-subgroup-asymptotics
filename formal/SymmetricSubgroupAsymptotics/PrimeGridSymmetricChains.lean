import SymmetricSubgroupAsymptotics.FiniteSymmetricChainProduct
import SymmetricSubgroupAsymptotics.FiniteSymmetricChainTransport
import SymmetricSubgroupAsymptotics.PrimeCosetGridCoordinates

/-! Every actual recursive prime coset grid has symmetric-chain
coordinates for its componentwise order. No antichain width is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

instance primeGridPreorder (p r : ℕ) : Preorder (PrimeCosetGrid p r) :=
  Preorder.lift (primeCosetGridTuple p r)

def primeGridRank (p : ℕ) : (r : ℕ) → PrimeCosetGrid p r → ℕ
  | 0 => fun _ => 0
  | r+1 => fun a => a.1.val+primeGridRank p r a.2

theorem primeGrid_le_iff (p r : ℕ) (a b : PrimeCosetGrid p r) :
    a≤b ↔ primeCosetGridComparable p r a b :=
  primeCosetGridTuple_le_iff p r a b

def primeGridSymmetricChains (p r : ℕ) (hp : 0<p) :
    FiniteSymmetricChains (PrimeCosetGrid p r) (primeGridRank p r) (r*(p-1)) := by
  induction r with
  | zero =>
    refine { Colour := Unit
             finiteColour := inferInstance
             colour := fun _ => ()
             start := fun _ => 0
             start_bound := ?_
             rank_bounds := ?_
             rank_unique := ?_
             rank_surjective := ?_
             chain_le := ?_ }
    · intro c; simp
    · intro x; simp [primeGridRank]
    · intro x y _ _; exact @Subsingleton.elim Unit inferInstance x y
    · intro c t _ hhi
      refine ⟨(),Subsingleton.elim _ _,?_⟩
      change 0=t
      simp only [zero_mul,add_zero] at hhi
      omega
    · intro x y _ _ i
      exact Fin.elim0 i
  | succ r ih =>
    let E := ih.product p hp
    let e : (PrimeCosetGrid p r×Fin p) ≃ PrimeCosetGrid p (r+1) := Equiv.prodComm _ _
    have horder : ∀ a b, e a≤e b ↔ a≤b := by
      intro a b
      rw [primeGrid_le_iff]
      change a.2≤b.2 ∧ primeCosetGridComparable p r a.1 b.1 ↔ a.1≤b.1 ∧ a.2≤b.2
      rw [←primeGrid_le_iff]
      exact and_comm
    have hrank : ∀ a, primeGridRank p (r+1) (e a)=primeGridRank p r a.1+a.2.val := by
      intro a
      change a.2.val+primeGridRank p r a.1=primeGridRank p r a.1+a.2.val
      exact Nat.add_comm _ _
    have hK : r*(p-1)+p-1=(r+1)*(p-1) := by
      rw [Nat.add_sub_assoc hp,add_mul,one_mul]
    have F := E.transport e horder (primeGridRank p (r+1)) hrank
    rw [hK] at F
    exact F

end SymmetricSubgroupAsymptotics
