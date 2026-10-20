import SymmetricSubgroupAsymptotics.FiniteSymmetricChainPairProduct
import SymmetricSubgroupAsymptotics.PrimeGridSymmetricChains
import SymmetricSubgroupAsymptotics.SolubleCosetGridCoordinates

/-! Every actual soluble coset grid has a constructive symmetric-chain
partition. Its actual middle rank bounds antichains, including after the
numeric reindexing used by the induced representation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

instance solubleGridPreorder (s : SolubleCosetShape) : Preorder s.Carrier := by
  induction s with
  | unit => exact inferInstanceAs (Preorder Unit)
  | step s p r ih =>
    letI := ih
    exact inferInstanceAs (Preorder (s.Carrier×PrimeCosetGrid p r))

def SolubleCosetShape.rank : (s : SolubleCosetShape) → s.Carrier → ℕ
  | .unit => fun _ => 0
  | .step s p r => fun a => s.rank a.1+primeGridRank p r a.2

def SolubleCosetShape.maxRank : SolubleCosetShape → ℕ
  | .unit => 0
  | .step s p r => s.maxRank+r*(p-1)

theorem SolubleCosetShape.le_iff_comparable (s : SolubleCosetShape) (a b : s.Carrier) :
    a≤b ↔ s.Comparable a b := by
  induction s with
  | unit =>
    constructor
    · intro _; trivial
    · intro _; exact le_of_eq (@Subsingleton.elim Unit inferInstance a b)
  | step s p r ih =>
    change a.1≤b.1 ∧ a.2≤b.2 ↔ s.Comparable a.1 b.1 ∧ primeCosetGridComparable p r a.2 b.2
    rw [ih,primeGrid_le_iff]

def SolubleCosetShape.symmetricChains (s : SolubleCosetShape) :
    s.Primes → FiniteSymmetricChains s.Carrier s.rank s.maxRank := by
  induction s with
  | unit =>
    intro _
    refine { Colour := Unit
             finiteColour := inferInstance
             colour := fun _ => ()
             start := fun _ => 0
             start_bound := ?_
             rank_bounds := ?_
             rank_unique := ?_
             rank_surjective := ?_
             chain_le := ?_ }
    · intro c; simp [SolubleCosetShape.maxRank]
    · intro x; simp [SolubleCosetShape.rank,SolubleCosetShape.maxRank]
    · intro x y _ _; exact @Subsingleton.elim Unit inferInstance x y
    · intro c t _ hhi
      refine ⟨(),Subsingleton.elim _ _,?_⟩
      change 0=t
      change t+0≤0 at hhi
      omega
    · intro x y _ _
      exact le_of_eq (@Subsingleton.elim Unit inferInstance x y)
  | step s p r ih =>
    intro hp
    exact (ih hp.1).pairProduct (primeGridSymmetricChains p r hp.2.pos)

def SolubleCosetShape.middleWidth (s : SolubleCosetShape) : ℕ :=
  (Finset.univ.filter (fun a : s.Carrier => s.rank a=s.maxRank/2)).card

theorem SolubleCosetShape.antichain_card_le_middle
    (s : SolubleCosetShape) (hp : s.Primes) (t : Finset s.Carrier)
    (ht : IsAntichain s.Comparable (t : Set s.Carrier)) : t.card≤SolubleCosetShape.middleWidth s := by
  apply (s.symmetricChains hp).antichain_card_le_middle t
  intro a ha b hb hab hle
  exact ht ha hb hab ((s.le_iff_comparable a b).mp hle)

theorem SolubleCosetShape.fin_antichain_card_le_middle
    (s : SolubleCosetShape) (hp : s.Primes) (t : Finset (Fin s.degree))
    (ht : IsAntichain s.finComparable (t : Set (Fin s.degree))) : t.card≤SolubleCosetShape.middleWidth s := by
  have himage : IsAntichain s.Comparable (t.image s.code.symm : Set s.Carrier) := by
    intro a ha b hb hab hr
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    exact ht hi hj (fun h => hab (congrArg s.code.symm h)) hr
  have hcard : (t.image s.code.symm).card=t.card :=
    Finset.card_image_of_injOn (fun _ _ _ _ h => s.code.symm.injective h)
  rw [←hcard]
  exact s.antichain_card_le_middle hp _ himage

end SymmetricSubgroupAsymptotics
