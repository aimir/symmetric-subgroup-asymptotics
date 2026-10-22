import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
import SymmetricSubgroupAsymptotics.CFSGParameterCommutatorNormalizer

/-! Genuine normal height tails inside the literal Geck MATRIX image-U.
All root commutators are discharged using the checked actual collecting
relations; tail normality is a conclusion, not a normal-form premise.
No transfer to the original Serre/source projective group is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGIntegerHeightSign CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateRootElementRange

private theorem commutator_eq_one {G : Type*} [Group G] (x y : G) (hc : Commute x y) :
    x*y*x⁻¹*y⁻¹=1 := by rw [hc.eq];group

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

def heightRootGenerators (K : Type) [Field K] (h : ℤ) : Set (CoordMat A hd hs hp ho K)ˣ :=
  {x | ∃k : PositiveRoot A,h≤height k.val.val ∧ ∃a : K,
    selectedRootElement A hd hs hp ho K k.val a=x}

def heightTail (K : Type) [Field K] (h : ℤ) : Subgroup (CoordMat A hd hs hp ho K)ˣ :=
  Subgroup.closure (heightRootGenerators A hd hs hp ho K h)

theorem rootElement_mem_heightTail (K : Type) [Field K] (h : ℤ) (k : Roots A)
    (hk : ∀i,0≤k.val i) (hheight : h≤height k.val) (a : K) :
    selectedRootElement A hd hs hp ho K k a∈heightTail A hd hs hp ho K h :=
  Subgroup.subset_closure ⟨⟨k,hk⟩,hheight,a,rfl⟩

theorem heightTail_antitone (K : Type) [Field K] {h k : ℤ} (hhk : h≤k) :
    heightTail A hd hs hp ho K k≤heightTail A hd hs hp ho K h := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨l,hl,a,rfl⟩
  exact rootElement_mem_heightTail A hd hs hp ho K h l.val l.property (hhk.trans hl) a

theorem heightTail_le_positive (K : Type) [Field K] (h : ℤ) :
    heightTail A hd hs hp ho K h≤rootGroup A hs hp b₀ s₀ K false := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k,hk,a,rfl⟩
  exact selected_positive_root_mem A hd hs hp ho K k.val k.property a

theorem root_commutator_mem_heightTail (K : Type) [Field K] (h : ℤ) (k l : Roots A)
    (hk : ∀i,0≤k.val i) (hl : ∀i,0≤l.val i) (hheight : h≤height l.val) (a b : K) :
    selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K l b*
      (selectedRootElement A hd hs hp ho K k a)⁻¹*(selectedRootElement A hd hs hp ho K l b)⁻¹∈
        heightTail A hd hs hp ho K h := by
  by_cases hkl : k=l
  · subst l
    rw [commutator_eq_one _ _ (selectedRootElement_commute A hd hs hp ho K k a b)]
    exact (heightTail A hd hs hp ho K h).one_mem
  have hopp : k.val≠ -l.val := by
    intro he
    have hz : k.val=0 := by
      funext j
      have hj := congrFun he j
      change k.val j= -(l.val j) at hj
      have := hk j
      have := hl j
      change k.val j=0
      omega
    have hn := k.property
    rw [hz] at hn
    norm_num at hn
  rcases root_pairing_interior A hs hp k l hkl hopp with hneg|hother
  · obtain ⟨ε,_,he⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hneg
    rw [he K a b]
    apply rootElement_mem_heightTail A hd hs hp ho K h (sumRoot A hs k l hneg)
    · exact fun j=>add_nonneg (hk j) (hl j)
    · change h≤height (k.val+l.val)
      rw [height_add]
      have hnonneg : 0≤height k.val := Finset.sum_nonneg (fun j _=>hk j)
      omega
  · have hc := CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute
      A hd hs hp ho K k l hk hl hother a b
    rw [commutator_eq_one _ _ hc]
    exact (heightTail A hd hs hp ho K h).one_mem

theorem rootSubgroup_le_normalizer_heightTail (K : Type) [Field K] (h : ℤ) (k : Roots A)
    (hk : ∀i,0≤k.val i) :
    rootSubgroup A hd hs hp ho K k≤Subgroup.normalizer
      (heightTail A hd hs hp ho K h : Set (CoordMat A hd hs hp ho K)ˣ) := by
  apply CFSGParameterCommutatorNormalizer.range_normalizes_closure
    (G:=(CoordMat A hd hs hp ho K)ˣ)
    (fun a : K=>selectedRootElement A hd hs hp ho K k a)
    (rootSubgroup A hd hs hp ho K k) (heightRootGenerators A hd hs hp ho K h)
    (mem_rootSubgroup_iff_selected A hd hs hp ho K k)
  intro a y hy
  obtain ⟨l,hl,b,rfl⟩ := hy
  exact root_commutator_mem_heightTail A hd hs hp ho K h k l.val hk l.property hl a b

theorem positive_le_normalizer_heightTail (K : Type) [Field K] (h : ℤ) :
    rootGroup A hs hp b₀ s₀ K false≤Subgroup.normalizer
      (heightTail A hd hs hp ho K h : Set (CoordMat A hd hs hp ho K)ˣ) := by
  rw [positive_group_eq_iSup A hd hs hp ho K]
  exact iSup_le (fun k=>rootSubgroup_le_normalizer_heightTail A hd hs hp ho K h k.val k.property)

theorem heightTail_normal_in_positive (K : Type) [Field K] (h : ℤ) :
    ((heightTail A hd hs hp ho K h).subgroupOf (rootGroup A hs hp b₀ s₀ K false)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (heightTail_le_positive A hd hs hp ho K h)).mpr
    (positive_le_normalizer_heightTail A hd hs hp ho K h)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
