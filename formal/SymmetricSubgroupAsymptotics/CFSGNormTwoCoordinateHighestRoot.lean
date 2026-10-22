import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantRootUnique
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import Mathlib.Data.Finset.Max

/-! Actual existence and uniqueness of the positive unraisable root.
Existence is finite height maximization; the comparison is proved from
the original integral root lattice, not an exceptional root table. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRoot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoPairingBounds CFSGNormTwoCoordinateDominantRootUnique
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoCoordinateHeight
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

include hd hs hp ho

theorem negative_simple_pairing_eq_neg_one (k : Roots A) (hk : ∀j,0≤k.val j)
    (i : Fin r) (hn : integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)<0) :
    integerPairing A k.val (s₀ i : Roots A).val= -1 := by
  have hb : -2 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ) ∧
      integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)≤2 :=
    root_pairing_bounds A hs hp k (s₀ i)
  have hne : integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)≠ -2 := by
    intro he
    have hopp := (root_pairing_eq_neg_two_iff A hs hp k (s₀ i)).mp he
    have hi := congrFun hopp i
    change k.val i= -(Pi.single i (1:ℤ) : Fin r→ℤ) i at hi
    simp [Pi.single_apply] at hi
    have hp := hk i
    omega
  change integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)= -1
  omega

theorem exists_dominant_positive_root (k : Roots A) (hk : ∀i,0≤k.val i) :
    ∃l : Roots A,(∀i,0≤l.val i) ∧
      (∀i,0 ≤ integerPairing A l.val (Pi.single i (1:ℤ) : Fin r→ℤ)) := by
  classical
  have hn : (Finset.univ : Finset (PositiveRoot A)).Nonempty := ⟨⟨k,hk⟩,Finset.mem_univ _⟩
  obtain ⟨l,hl,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (PositiveRoot A))
    (fun l=>height l.val.val) hn
  refine ⟨l.val,l.property,?_⟩
  intro i
  by_contra hn
  have hpair := negative_simple_pairing_eq_neg_one A hd hs hp ho l.val l.property i (lt_of_not_ge hn)
  let a := raisedRoot A hd hs hp ho l.val i hpair
  have ha : ∀j,0≤a.val j := by
    intro j
    change 0≤l.val.val j+(Pi.single i (1:ℤ) : Fin r→ℤ) j
    apply add_nonneg (l.property j)
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hnew : height a.val=height l.val.val+1 := by
    change height (l.val.val+(s₀ i : Roots A).val)=_
    rw [height_add]
    have hi := simple_height A hd hs hp ho (s₀ i)
    change height (s₀ i : Roots A).val=1 at hi
    rw [hi]
  have hle := hmax ⟨a,ha⟩ (Finset.mem_univ _)
  change height a.val≤height l.val.val at hle
  rw [hnew] at hle
  omega

theorem exists_unique_dominant_positive_root (k : Roots A) (hk : ∀i,0≤k.val i) :
    ∃!l : Roots A,(∀i,0≤l.val i) ∧
      (∀i,0 ≤ integerPairing A l.val (Pi.single i (1:ℤ) : Fin r→ℤ)) := by
  obtain ⟨l,hl,hdom⟩ := exists_dominant_positive_root A hd hs hp ho k hk
  refine ⟨l,⟨hl,hdom⟩,?_⟩
  intro a ha
  exact dominant_positive_root_unique A hd hs hp ho a l ha.1 hl ha.2 hdom

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRoot
