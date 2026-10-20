import SymmetricSubgroupAsymptotics.SymmetricChainBooleanReplacement
import SymmetricSubgroupAsymptotics.FiniteSymmetricChainTransport

/-! Finite products of positive chains, their actual rank partitions,
and the rank-preserving concatenation of Boolean grids. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

def FiniteChainGrid : List ℕ → Type
  | [] => Unit
  | n::l => Fin n×FiniteChainGrid l

instance finiteChainGridFintype (l : List ℕ) : Fintype (FiniteChainGrid l) := by
  induction l with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons n l ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin n×FiniteChainGrid l))

instance finiteChainGridPreorder (l : List ℕ) : Preorder (FiniteChainGrid l) := by
  induction l with
  | nil => exact inferInstanceAs (Preorder Unit)
  | cons n l ih =>
    letI := ih
    exact inferInstanceAs (Preorder (Fin n×FiniteChainGrid l))

def FiniteChainGrid.rank : (l : List ℕ) → FiniteChainGrid l → ℕ
  | [] => fun _ => 0
  | _n::l => fun x => x.1.val+rank l x.2

def FiniteChainGrid.maxRank (l : List ℕ) : ℕ := (l.map (fun n => n-1)).sum

def FiniteChainGrid.Positive (l : List ℕ) : Prop := ∀ n∈l,0<n

/-- The literal chain product has a genuine symmetric-chain partition. -/
def finiteChainGridSymmetricChains (l : List ℕ) (hl : FiniteChainGrid.Positive l) :
    FiniteSymmetricChains (FiniteChainGrid l) (FiniteChainGrid.rank l)
      (FiniteChainGrid.maxRank l) := by
  induction l with
  | nil =>
    refine { Colour := Unit
             finiteColour := inferInstance
             colour := fun _ => ()
             start := fun _ => 0
             start_bound := ?_
             rank_bounds := ?_
             rank_unique := ?_
             rank_surjective := ?_
             chain_le := ?_ }
    · intro c; simp [FiniteChainGrid.maxRank]
    · intro x; simp [FiniteChainGrid.rank,FiniteChainGrid.maxRank]
    · intro x y _ _; exact @Subsingleton.elim Unit inferInstance x y
    · intro c t _ hhi
      refine ⟨(),Subsingleton.elim _ _,?_⟩
      change t+0≤0 at hhi
      change 0=t
      omega
    · intro x y _ _; exact le_of_eq (@Subsingleton.elim Unit inferInstance x y)
  | cons n l ih =>
    have hn : 0<n := hl n (by simp)
    have htail : FiniteChainGrid.Positive l := fun p hp => hl p (by simp [hp])
    let D := (ih htail).product n hn
    let e : (FiniteChainGrid l×Fin n) ≃ FiniteChainGrid (n::l) := Equiv.prodComm _ _
    have ho : ∀ a b,e a≤e b ↔ a≤b := by
      intro a b
      change a.2≤b.2 ∧ a.1≤b.1 ↔ a.1≤b.1 ∧ a.2≤b.2
      exact and_comm
    have hr : ∀ a,FiniteChainGrid.rank (n::l) (e a)=FiniteChainGrid.rank l a.1+a.2.val := by
      intro a
      exact Nat.add_comm _ _
    have h := D.transport e ho (FiniteChainGrid.rank (n::l)) hr
    have he : FiniteChainGrid.maxRank l+n-1=FiniteChainGrid.maxRank (n::l) := by
      simp only [FiniteChainGrid.maxRank,List.map_cons,List.sum_cons]
      omega
    rw [he] at h
    exact h

/-- Concatenation refers to the original recursive binary points. -/
def binaryGridAppend : (m n : ℕ) →
    (PrimeCosetGrid 2 m×PrimeCosetGrid 2 n) ≃ PrimeCosetGrid 2 (m+n)
  | m,0 => by
    simpa only [Nat.add_zero,PrimeCosetGrid] using Equiv.prodUnique (PrimeCosetGrid 2 m) Unit
  | m,n+1 => {
      toFun := fun a => (a.2.1,binaryGridAppend m n (a.1,a.2.2))
      invFun := fun a => (((binaryGridAppend m n).symm a.2).1,
        (a.1,((binaryGridAppend m n).symm a.2).2))
      left_inv := by
        intro a
        rcases a with ⟨x,⟨i,y⟩⟩
        simp only [Equiv.symm_apply_apply]
      right_inv := by
        intro a
        rcases a with ⟨i,z⟩
        change (i,binaryGridAppend m n ((binaryGridAppend m n).symm z))=(i,z)
        rw [Equiv.apply_symm_apply] }

theorem binaryGridAppend_rank (m n : ℕ) (x : PrimeCosetGrid 2 m×PrimeCosetGrid 2 n) :
    primeGridRank 2 (m+n) (binaryGridAppend m n x)=
      primeGridRank 2 m x.1+primeGridRank 2 n x.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x,⟨i,y⟩⟩
    change i.val+primeGridRank 2 (m+n) (binaryGridAppend m n (x,y))=
      primeGridRank 2 m x+(i.val+primeGridRank 2 n y)
    have h := ih (x,y)
    change primeGridRank 2 (m+n) (binaryGridAppend m n (x,y))=
      primeGridRank 2 m x+primeGridRank 2 n y at h
    rw [h]
    omega

/-- A rank-preserving equivalence transports exact layer cardinalities. -/
theorem rank_card_equiv {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (rI : I → ℕ) (rJ : J → ℕ) (hr : ∀ x,rJ (e x)=rI x) (t : ℕ) :
    (Finset.univ.filter (fun x => rI x=t)).card=
      (Finset.univ.filter (fun y => rJ y=t)).card := by
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hr x).trans (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact e.injective hxy
  · intro y hy
    refine ⟨e.symm y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,e.apply_symm_apply y⟩
    rw [←hr,e.apply_symm_apply]
    exact (Finset.mem_filter.mp hy).2

end SymmetricSubgroupAsymptotics
