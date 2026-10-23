import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCommutators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A literal middle-degree radical and its central highest-root quotient.
The quotient is proved commutative from the actual root commutators. No
coordinate independence or fixed-field descent is used here. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalQuotient
open scoped commutatorElement
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalCommutators
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

abbrev Raw (K : Type) [CommRing K] := (Matrix GeckIndex GeckIndex K)ˣ

def middleGenerators (K : Type) [Field K] : Set (Raw K) :=
  {x | ∃ k : Roots A, (∀ i, 0 ≤ k.val i) ∧ 1 ≤ k.val 1 ∧
    ∃ a : K, selectedRootElement A hd hs hp ho K k a = x}

def middleRadical (K : Type) [Field K] : Subgroup (Raw K) :=
  Subgroup.closure (middleGenerators K)

abbrev highestLine (K : Type) [Field K] : Subgroup (Raw K) :=
  rootSubgroup A hd hs hp ho K (longRoot 2)

theorem middle_root_mem (K : Type) [Field K] (k : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hkmid : 1 ≤ k.val 1) (a : K) :
    selectedRootElement A hd hs hp ho K k a ∈ middleRadical K :=
  Subgroup.subset_closure ⟨k, hk, hkmid, a, rfl⟩

theorem highest_le_middle (K : Type) [Field K] : highestLine K ≤ middleRadical K := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) x).mp hx
  exact middle_root_mem K (longRoot 2) (long_positive 2) (by decide) a

theorem middle_le_centralizer_highest (K : Type) [Field K] :
    middleRadical K ≤ Subgroup.centralizer (highestLine K : Set (Raw K)) := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k, hk, hkmid, a, rfl⟩ z hz
  obtain ⟨b, rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) z).mp hz
  exact (highest_commutes_middle_positive K k hk hkmid b a).eq

abbrev highestInMiddle (K : Type) [Field K] : Subgroup (middleRadical K) :=
  (highestLine K).subgroupOf (middleRadical K)

instance highestInMiddle_normal (K : Type) [Field K] : (highestInMiddle K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (highest_le_middle K)).mpr
    ((middle_le_centralizer_highest K).trans (Subgroup.centralizer_le_normalizer _))

abbrev MiddleQuotient (K : Type) [Field K] := middleRadical K ⧸ highestInMiddle K

def middleParameter (K : Type) [Field K] (k : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hkmid : 1 ≤ k.val 1) :
    Multiplicative K →* middleRadical K :=
  (selectedRootHom A hd hs hp ho K k).codRestrict (middleRadical K)
    (fun a => middle_root_mem K k hk hkmid a.toAdd)

def quotientParameter (K : Type) [Field K] (k : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hkmid : 1 ≤ k.val 1) :
    Multiplicative K →* MiddleQuotient K :=
  (QuotientGroup.mk' (highestInMiddle K)).comp (middleParameter K k hk hkmid)

theorem quotient_parameters_commute (K : Type) [Field K] (k l : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hl : ∀ i, 0 ≤ l.val i)
    (hkmid : 1 ≤ k.val 1) (hlmid : 1 ≤ l.val 1) (a b : Multiplicative K) :
    Commute (quotientParameter K k hk hkmid a) (quotientParameter K l hl hlmid b) := by
  let q : middleRadical K →* MiddleQuotient K := QuotientGroup.mk' (highestInMiddle K)
  let x := middleParameter K k hk hkmid a
  let y := middleParameter K l hl hlmid b
  have hcomm : ⁅x, y⁆ ∈ highestInMiddle K := by
    change selectedRootElement A hd hs hp ho K k a.toAdd *
      selectedRootElement A hd hs hp ho K l b.toAdd *
      (selectedRootElement A hd hs hp ho K k a.toAdd)⁻¹ *
      (selectedRootElement A hd hs hp ho K l b.toAdd)⁻¹ ∈ highestLine K
    exact middle_positive_commutator_mem_highest K k l hk hl hkmid hlmid a.toAdd b.toAdd
  apply commutatorElement_eq_one_iff_commute.mp
  change ⁅q x, q y⁆ = 1
  rw [← map_commutatorElement q]
  exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mpr hcomm


private theorem commutative_of_generators {G : Type*} [Group G] (S : Set G)
    (hgen : Subgroup.closure S = ⊤)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y) : IsMulCommutative G := by
  letI : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy => (hcomm x hx y hy).eq)
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : x ∈ Subgroup.closure S := by rw [hgen]; trivial
  have hy : y ∈ Subgroup.closure S := by rw [hgen]; trivial
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)

theorem quotient_isMulCommutative (K : Type) [Field K] :
    IsMulCommutative (MiddleQuotient K) := by
  let S : Set (middleRadical K) := (middleRadical K).subtype ⁻¹' middleGenerators K
  let q : middleRadical K →* MiddleQuotient K := QuotientGroup.mk' (highestInMiddle K)
  have hgen : Subgroup.closure S = ⊤ := Subgroup.closure_closure_coe_preimage
  have himage : Subgroup.closure (q '' S) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  apply commutative_of_generators (q '' S) himage
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, hkmid, a, ha⟩ := hx
  obtain ⟨l, hl, hlmid, b, hb⟩ := hy
  have hxe : x = middleParameter K k hk hkmid (Multiplicative.ofAdd a) :=
    Subtype.ext ha.symm
  have hye : y = middleParameter K l hl hlmid (Multiplicative.ofAdd b) :=
    Subtype.ext hb.symm
  rw [hxe, hye]
  exact quotient_parameters_commute K k l hk hl hkmid hlmid _ _

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalQuotient
