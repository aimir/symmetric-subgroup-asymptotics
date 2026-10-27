import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
import SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent
import SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign

/-! Actual positive-root parent paths for every positive-definite norm-two
integer lattice with coordinate roots. No root census, target realization,
source spanning, or Serre faithfulness is assumed. The same result applies
to E6, E7, and E8 and will choose the ORIGINAL source bracket recursion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoPositiveRootParents
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGIntegerPairingPositiveDescent CFSGIntegerHeightSign
variable {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ)

/-- A positive norm-two root has strictly positive coordinate height. -/
theorem height_pos (k : Roots A) (hk : ∀j,0≤k.val j) : 0<height k.val := by
  obtain ⟨i,hi,_⟩ := exists_positive_coordinate_pairing (integerPairing A)
    k.val hk (by rw [k.property]; decide)
  have hsum : k.val i≤height k.val :=
    Finset.single_le_sum (fun j _=>hk j) (Finset.mem_univ i)
  omega

theorem height_coordinate (i : I) : height (Pi.single i (1:ℤ))=1 := by
  simp only [height,Pi.single_apply,Finset.sum_ite_eq',
    Finset.mem_univ,if_true]

variable (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)

include hs hp in
/-- Every nonsimple positive root is obtained by adding ONE coordinate
simple root to an actual positive root of height one less. Its root-string
pairing is minus one, so the subsequent Lie parent coefficient is a unit.
The theorem does not assert the Lie identity; that identity will come from
the definition of the original source path. -/
theorem exists_parent (k : Roots A) (hk : ∀j,0≤k.val j)
    (hn : ∀i,k≠coordinateRoot A hd i) :
    ∃ (i : I) (p : Roots A),
      (∀j,0≤p.val j) ∧ k.val=p.val+Pi.single i 1 ∧
      height p.val+1=height k.val ∧ 0<height p.val ∧
      integerPairing A p.val (Pi.single i 1)= -1 := by
  obtain ⟨i,hi,hpair⟩ := exists_positive_coordinate_pairing (integerPairing A)
    k.val hk (by rw [k.property]; decide)
  have hb := root_pairing_bounds A hs hp k (coordinateRoot A hd i)
  have htwo : integerPairing A k.val (Pi.single i 1)≠2 := by
    intro he
    exact hn i ((root_pairing_eq_two_iff A hs hp k (coordinateRoot A hd i)).mp he)
  have hpair_one : integerPairing A k.val (Pi.single i 1)=1 := by
    have hu : integerPairing A k.val (Pi.single i 1)≤2 := hb.2
    omega
  have haxis : integerPairing A (Pi.single i 1) (Pi.single i 1)=2 := by
    simpa only [integerPairing,Matrix.toBilin'_single] using hd i
  let p : Roots A := ⟨k.val-Pi.single i 1,by
    rw [norm_sub A hs,k.property,haxis,hpair_one]
    norm_num⟩
  have hpnonneg : ∀j,0≤p.val j := by
    intro j
    change 0≤k.val j-(Pi.single i (1:ℤ) : I→ℤ) j
    by_cases hij : i=j
    · subst j
      simpa only [Pi.single_eq_same] using (show 0≤k.val i-1 by omega)
    · simpa only [Pi.single_apply,if_neg (Ne.symm hij),sub_zero] using hk j
  have hcoords : k.val=p.val+Pi.single i 1 := by
    change k.val=(k.val-Pi.single i 1)+Pi.single i 1
    abel
  have hheight : height p.val+1=height k.val := by
    rw [hcoords,height_add,height_coordinate]
  have hparent_pair : integerPairing A p.val (Pi.single i 1)= -1 := by
    change integerPairing A (k.val-Pi.single i 1) (Pi.single i 1)= -1
    rw [map_sub,LinearMap.sub_apply,hpair_one,haxis]
    norm_num
  exact ⟨i,p,hpnonneg,hcoords,hheight,height_pos A p hpnonneg,hparent_pair⟩

/-- The selected parent strictly decreases the NATURAL height used by the
source recursion, without a bounded-root-list or termination assumption. -/
theorem parent_height_lt (k p : Roots A)
    (hpnonneg : ∀j,0≤p.val j) (he : height p.val+1=height k.val) :
    (height p.val).toNat < (height k.val).toNat := by
  have hpos := height_pos A p hpnonneg
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoPositiveRootParents
