import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantRootUnique
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Subgroup.Center

/-! The actual dominant positive root subgroup is central in the literal
Geck matrix image-U. This is proved from original all-field root word
relations, rather than from root-label pairwise intersections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootCentral
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoCoordinateDominantRootUnique CFSGNormTwoCoordinatePositivePairCommute
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem dominant_root_commutes_positive_root (K : Type) [Field K] (k l : Roots A)
    (hk : ∀i,0≤k.val i) (hl : ∀i,0≤l.val i)
    (hdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)) (a b : K) :
    Commute (selectedRootElement A hd hs hp ho K k a) (selectedRootElement A hd hs hp ho K l b) := by
  by_cases he : k=l
  · subst l
    exact selectedRootElement_commute A hd hs hp ho K k a b
  have hge := dominant_pair_nonneg A hs k.val l.val hdom hl
  have hb := root_pairing_bounds A hs hp k l
  have hne : integerPairing A k.val l.val≠2 := fun h=>he ((root_pairing_eq_two_iff A hs hp k l).mp h)
  exact positive_pair_commute A hd hs hp ho K k l hk hl (by omega) a b

theorem positive_le_centralizer_dominant_root (K : Type) [Field K] (k : Roots A)
    (hk : ∀i,0≤k.val i)
    (hdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)) (a : K) :
    PositiveGroup A hd hs hp ho K≤Subgroup.centralizer
      ({selectedRootElement A hd hs hp ho K k a} : Set (CoordMat A hd hs hp ho K)ˣ) := by
  change CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp b₀
    (coordinateIndexEquiv A hd hs hp ho) K false≤_
  rw [positive_group_eq_iSup]
  apply iSup_le
  intro l x hx
  obtain ⟨b,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K l.val x).mp hx
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  have he : y=selectedRootElement A hd hs hp ho K k a := Set.mem_singleton_iff.mp hy
  subst y
  exact (dominant_root_commutes_positive_root A hd hs hp ho K k l.val hk l.property hdom a b).eq

theorem dominant_root_subgroup_le_center (K : Type) [Field K] (k : Roots A)
    (hk : ∀i,0≤k.val i)
    (hdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    (rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)≤
      Subgroup.center (PositiveGroup A hd hs hp ho K) := by
  intro x hx
  obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x.val).mp hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  change y.val*x.val=x.val*y.val
  rw [←ha]
  exact (Subgroup.mem_centralizer_iff.mp
    (positive_le_centralizer_dominant_root A hd hs hp ho K k hk hdom a y.property)
    _ (Set.mem_singleton _)).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootCentral
