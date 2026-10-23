import SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSignedCommutation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Distinct folded simple labels commute across opposite signs in the
SAME actual E6 root groups. This uses the original rational EF relation
and its integral two-parameter transport, not a mod-p weight argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitCommutation
open CFSGE6GeckNegativeOrbitRootGroups CFSGE6GeckOrbitRootIntersection
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6RelativeWeylOrbits CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGGeckSerreRepresentation
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
open CFSGSerreQuadraticMatrix

private theorem orbit_indices_ne (a b : Fin 4) (hne : a≠b)
    (i : Fin 6) (hi : i∈orbitWord a) (j : Fin 6) (hj : j∈orbitWord b) : i≠j := by
  have h : ∀a b : Fin 4,a≠b→∀i∈orbitWord a,∀j∈orbitWord b,i≠j := by decide
  exact h a b hne i hi j hj

theorem opposite_simple_commute (K : Type) [Field K] (i j : Fin 6) (hne : i≠j) (a b : K) :
    Commute (canonicalRoot rawData K false i a) (canonicalRoot rawData K true j b) :=
  CFSGSerreQuadraticSignedCommutation.roots_commute rawData K false true i j
    (by rw [rational_E_eq,rational_F_eq,EF,if_neg hne]) a b

theorem orbit_groups_opposite_commute (K : Type) [Field K] (a b : Fin 4) (hne : a≠b)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x∈orbitPositiveGroup K a)
    (y : (Matrix GeckIndex GeckIndex K)ˣ) (hy : y∈orbitNegativeGroup K b) : Commute x y := by
  have hc : orbitPositiveGroup K a≤Subgroup.centralizer
      (orbitNegativeGroup K b : Set ((Matrix GeckIndex GeckIndex K)ˣ)) := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply Subgroup.le_centralizer_iff.mpr
    change (orbitPositiveGroup K b).map (rawOpposition K).toMonoidHom≤
      Subgroup.centralizer (canonicalRootSubgroup rawData K false i :
        Set ((Matrix GeckIndex GeckIndex K)ˣ))
    apply Subgroup.map_le_iff_le_comap.mpr
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    rintro z ⟨t,rfl⟩
    change rawOpposition K (canonicalRoot rawData K false j t)∈
      Subgroup.centralizer (canonicalRootSubgroup rawData K false i :
        Set ((Matrix GeckIndex GeckIndex K)ˣ))
    have he : rawOpposition K (canonicalRoot rawData K false j t)=canonicalRoot rawData K true j t :=
      rawSimple_opposition K false j (Multiplicative.ofAdd t)
    rw [he,Subgroup.mem_centralizer_iff]
    rintro u ⟨s,rfl⟩
    exact (opposite_simple_commute K i j (orbit_indices_ne a b hne i hi j hj) s t).eq
  exact (Subgroup.mem_centralizer_iff.mp (hc hx) y hy).symm

end SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitCommutation
