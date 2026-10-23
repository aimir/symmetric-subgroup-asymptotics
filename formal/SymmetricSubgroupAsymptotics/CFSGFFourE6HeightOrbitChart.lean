import SymmetricSubgroupAsymptotics.CFSGFFourE6OrbitFactorHeightClass
import SymmetricSubgroupAsymptotics.CFSGFFourE6OrbitRepresentativeHeights

/-! Actual per-height products for the nine transported orbit labels.
Intrinsic root-line coordinates prove separation MODULO the next tail,
not merely injection of each individual root line. These are the exact
coset charts consumed by the proved filtered-cardinality inequality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeightOrbitChart
open CFSGFFourE6CentralizerRootPilot CFSGFFourE6CentralizerRootTransport
open CFSGFFourE6OrbitRepresentativeHeights CFSGFFourE6OrbitFactorHeightClass
open CFSGFFourE6PositiveOrbitFactors CFSGFFourOrbitCoordinateChart
open CFSGTwistedE6GeckHeightRootPermutation CFSGTwistedE6GeckIntrinsicHeightAction
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6GeckFixedHeightOrbitLifting
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckPositiveTwist

local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  CFSGNormTwoCoordinateRootHeightFiltration.heightTail_normal_in_positive
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      CFSGExceptionalCartanPositiveDefinite.E6_positive_definite
        CartanMatrix.E₆_off_diag_nonpos K h

abbrev HeightReps (r : List (Fin 4)) (n : ℕ) := {j : Fin 9 // (repHeight r j).val=n}

def rootSlot (r : List (Fin 4)) (n : ℕ) (j : HeightReps r n) : HeightIndex ((n:ℤ)+1) :=
  ⟨transportedRoot r (representative j.val),by
    have h := repHeight_spec r j.val
    rw [j.property] at h
    exact h⟩

theorem rootSlot_disjoint (r : List (Fin 4)) (n : ℕ) (j k : HeightReps r n)
    (he : rootSlot r n j=rootSlot r n k ∨
      rootSlot r n j=heightRootPermutation ((n:ℤ)+1) (rootSlot r n k)) : j=k := by
  apply Subtype.ext
  apply representative_orbits_disjoint j.val k.val
  rcases he with he|he
  · left
    apply transportedRoot_injective r
    exact congrArg (fun t : HeightIndex ((n:ℤ)+1)=>t.val) he
  · right
    apply transportedRoot_injective r
    apply Subtype.ext
    have hv := congrArg (fun t : HeightIndex ((n:ℤ)+1)=>t.val.val) he
    change (transportedRoot r (representative j.val)).val=
      CFSGTwistedE6WeylChamber.diagramRoot (transportedRoot r (representative k.val)).val at hv
    rw [transportedRoot_diagram] at hv
    exact hv

def heightWord (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ)
    (c : ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val) : Positive K :=
  ((Finset.univ : Finset (HeightReps r n)).toList.map
    (fun j=>rootOrbitFactor K (rootSlot r n j).val (c j))).prod

def heightCoordinateChart (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ)
    (c : ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val) :
    RootCoordinates K ((n:ℤ)+1) :=
  orbitChart (fun k : HeightIndex ((n:ℤ)+1)=>RootLine K k.val.val)
    (heightRootPermutation ((n:ℤ)+1))
    (fun k=>(rootLineTwist K (RingEquiv.refl K) ((n:ℤ)+1) k).toMonoidHom) (rootSlot r n) c

theorem heightCoordinateChart_injective (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ) :
    Function.Injective (heightCoordinateChart K r n) :=
  orbitChart_injective (fun k : HeightIndex ((n:ℤ)+1)=>RootLine K k.val.val)
    (heightRootPermutation ((n:ℤ)+1))
    (fun k=>(rootLineTwist K (RingEquiv.refl K) ((n:ℤ)+1) k).toMonoidHom)
    (rootSlot r n) (rootSlot_disjoint r n)

theorem heightWord_mem_of_factors (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ)
    (H : Subgroup (Positive K))
    (c : ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val)
    (hc : ∀j,rootOrbitFactor K (rootSlot r n j).val (c j)∈H) : heightWord K r n c∈H := by
  apply H.list_prod_mem
  intro u hu
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hu
  exact hc j

theorem heightWord_mem_tail (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ)
    (c : ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val) :
    heightWord K r n c∈TailInPositive K ((n:ℤ)+1) := by
  exact heightWord_mem_of_factors K r n _ c
    (fun j=>rootOrbitFactor_mem_tail K ((n:ℤ)+1) (rootSlot r n j) (c j))

theorem heightWord_class (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ)
    (c : ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val) :
    heightClass K ((n:ℤ)+1) (heightWord K r n c)=
      (intrinsicCoordinates K ((n:ℤ)+1) (by omega) (heightCoordinateChart K r n c)).val := by
  let E : RootCoordinates K ((n:ℤ)+1)→*Quotient K ((n:ℤ)+1) :=
    (HeightImage K ((n:ℤ)+1)).subtype.comp
      (intrinsicCoordinates K ((n:ℤ)+1) (by omega)).toMonoidHom
  change heightClass K ((n:ℤ)+1) (heightWord K r n c)=E (heightCoordinateChart K r n c)
  simp only [heightWord,heightCoordinateChart,orbitChart,map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact rootOrbitFactor_heightClass K ((n:ℤ)+1) (by omega) (rootSlot r n j) (c j)

theorem heightWord_coset_separation (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ)
    (c d : ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val)
    (he : (heightWord K r n c)⁻¹*heightWord K r n d∈TailInPositive K (((n:ℤ)+1)+1)) : c=d := by
  have hker : heightClass K ((n:ℤ)+1) ((heightWord K r n c)⁻¹*heightWord K r n d)=1 :=
    (QuotientGroup.eq_one_iff _).mpr he
  have hclass : heightClass K ((n:ℤ)+1) (heightWord K r n c)=
      heightClass K ((n:ℤ)+1) (heightWord K r n d) := by
    rw [map_mul,map_inv,inv_mul_eq_one] at hker
    exact hker
  rw [heightWord_class,heightWord_class] at hclass
  apply heightCoordinateChart_injective K r n
  apply (intrinsicCoordinates K ((n:ℤ)+1) (by omega)).injective
  exact Subtype.ext hclass

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeightOrbitChart
