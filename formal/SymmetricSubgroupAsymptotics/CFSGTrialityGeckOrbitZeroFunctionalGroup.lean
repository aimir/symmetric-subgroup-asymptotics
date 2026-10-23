import SymmetricSubgroupAsymptotics.CFSGTrialityD4SimpleOrbitSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateZeroFunctionalSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFactor
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership

/-! The actual zero-functional positive subgroup is exactly the three
orthogonal outer-root product group or the middle simple root group.
Both containments use original root parameters, without field-size
assumptions or a positive-root census. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOrbitZeroFunctionalGroup
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityD4SimpleOrbitSupport
open CFSGTrialityGeckShortComplementFactor CFSGTrialityFixedWeylWords
open CFSGNormTwoCoordinateZeroFunctionalSupport CFSGNormTwoCoordinateCanonicalSimpleRootLine
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGTrialityGeckSectionHeightMembership
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

def orbitRootGroup (K : Type) [Field K] (a : Bool) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  if a then canonicalRootSubgroup rawData K false 1 else outerGroup K

private theorem simple_root_line (K : Type) [Field K] (i : Fin 4) :
    RootLine K (Index i) = canonicalRootSubgroup rawData K false i := by
  exact rootSubgroup_simple_eq_canonical A hd hs hp ho K i

theorem simple_mem_orbitRootGroup (K : Type) [Field K] (a : Bool)
    (i : Fin 4) (hi : i ∈ orbitWord a) (t : K) :
    canonicalRoot rawData K false i t ∈ orbitRootGroup K a := by
  cases a
  · have he : i = 0 ∨ i = 2 ∨ i = 3 := by simpa [orbitWord] using hi
    rcases he with rfl | rfl | rfl
    · exact outer_root_mem K 0 t
    · exact outer_root_mem K 1 t
    · exact outer_root_mem K 2 t
  · have he : i = 1 := by simpa [orbitWord] using hi
    subst i
    exact ⟨t,rfl⟩

private theorem selected_mem_orbitRootGroup (K : Type) [Field K] (a : Bool)
    (k : Roots A) (hk : ∀ i, 0 ≤ k.val i) (hz : orbitHeight a k.val = 0) (t : K) :
    selectedRootElement A hd hs hp ho K k t ∈ orbitRootGroup K a := by
  obtain ⟨i,hi,rfl⟩ := positive_zero_orbit_root a k hk hz
  have hm : selectedRootElement A hd hs hp ho K (Index i) t ∈ RootLine K (Index i) :=
    (mem_rootSubgroup_iff_selected A hd hs hp ho K (Index i) _).mpr ⟨t,rfl⟩
  rw [simple_root_line] at hm
  obtain ⟨s,he⟩ := hm
  rw [← he]
  exact simple_mem_orbitRootGroup K a i hi s

private theorem simple_mem_zeroFunctionalGroup (K : Type) [Field K] (a : Bool)
    (i : Fin 4) (hi : i ∈ orbitWord a) (t : K) :
    canonicalRoot rawData K false i t ∈ zeroFunctionalGroup A hd hs hp ho K (orbitHeight a) := by
  let k : PositiveRoot A := ⟨Index i,by
    intro j
    change 0 ≤ (Pi.single i (1 : ℤ) : Fin 4 → ℤ) j
    simp only [Pi.single_apply]
    split_ifs <;> omega⟩
  have hz : orbitHeight a k.val.val = 0 := by
    change orbitHeight a (Index i : Roots A).val = 0
    rw [orbitHeight_simple,if_pos hi]
  have hm : canonicalRoot rawData K false i t ∈ RootLine K (Index i) := by
    rw [simple_root_line]
    exact ⟨t,rfl⟩
  obtain ⟨s,he⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (Index i) _).mp hm
  rw [← he]
  exact root_mem_zeroFunctionalGroup A hd hs hp ho K (orbitHeight a) k hz s

theorem zeroFunctionalGroup_eq_orbitRootGroup (K : Type) [Field K] (a : Bool) :
    zeroFunctionalGroup A hd hs hp ho K (orbitHeight a) = orbitRootGroup K a := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,hk,t,rfl⟩
    exact selected_mem_orbitRootGroup K a k.val k.property hk t
  · cases a
    · change (outerProductHom K).range ≤ _
      rw [outerProductHom,MonoidHom.noncommPiCoprod_range]
      apply iSup_le
      intro i
      rintro _ ⟨t,rfl⟩
      apply simple_mem_zeroFunctionalGroup K false (outerNode i) _ t.toAdd
      fin_cases i <;> decide
    · rintro _ ⟨t,rfl⟩
      exact simple_mem_zeroFunctionalGroup K true 1 (by decide) t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOrbitZeroFunctionalGroup
