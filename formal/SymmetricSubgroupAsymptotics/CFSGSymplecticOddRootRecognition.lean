import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentSylow
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentHighestRoot
import SymmetricSubgroupAsymptotics.CFSGSylowCenterConjugacy

/-! In characteristic different from two, the natural long-root
elements of the SAME elementary C group are intrinsically the union
of its defining-characteristic Sylow centres. This proves actual
automorphism invariance, without assuming a root-recognition theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOddRootRecognition
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticUnipotent CFSGSylowCenterRecognition
variable {K : Type} [Field K] [Finite K]

def IsNaturalRootElement (r : ℕ) (hr : 0 < r)
    (A : elementaryRootGroup K (r + 1)) : Prop :=
  ∃ v : Index (r + 1) → K, ∃ a : K, A = actualNaturalRootElement r hr v a

omit [Finite K] in
private theorem first_root_eq_actual (r : ℕ) (hr : 0 < r) (a : K) :
    firstLongRoot K r a = actualNaturalRootElement r hr
      (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) a := by
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [actualNaturalRootElement_apply, firstLongRoot_mulVec_eq_transvection]

theorem sylowCenterElements_isNaturalRootElement (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    {A : elementaryRootGroup K (r + 1)}
    (hA : A ∈ sylowCenterElements (G := elementaryRootGroup K (r + 1)) p) :
    IsNaturalRootElement r hr A := by
  let P := unipotentSylow K p r hr
  obtain ⟨g, z, hz, hg⟩ := exists_conjugate_fixed_sylow_center p P hA
  obtain ⟨a, ha⟩ := center_eq_highestLong_of_two_ne_zero r hr htwo z hz
  have hza : (z : elementaryRootGroup K (r + 1)) = firstLongRoot K r a := by
    exact (congrArg Subtype.val ha).trans (highestLongInU_val r hr a)
  rw [hza, first_root_eq_actual r hr a,
    actualNaturalRootElement_conjugation r hr] at hg
  exact ⟨_, a, hg.symm⟩

theorem naturalRootElement_mem_sylowCenterElements (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r)
    (v : Index (r + 1) → K) (a : K) :
    actualNaturalRootElement r hr v a ∈
      sylowCenterElements (G := elementaryRootGroup K (r + 1)) p := by
  by_cases hv : v = 0
  · have he : actualNaturalRootElement r hr v a = 1 := by
      apply elementary_eq_of_mulVec_eq
      intro x
      rw [actualNaturalRootElement_apply, hv]
      change transvection (r + 1) 0 a x = (1 : Mat K (r + 1)) *ᵥ x
      simp only [transvection_apply, pairing_zero_left, mul_zero, zero_smul,
        add_zero, Matrix.one_mulVec]
    rw [he]
    exact one_mem_sylowCenterElements p
  obtain ⟨g, hg⟩ := exists_elementary_mulVec_first_basis K r hr v hv
  have hroot : firstLongRoot K r a ∈
      sylowCenterElements (G := elementaryRootGroup K (r + 1)) p := by
    refine ⟨unipotentSylow K p r hr, highestLongInU r hr a,
      highestLongInU_mem_center r hr a, highestLongInU_val r hr a⟩
  have h := automorphism_mem_sylowCenterElements p (MulAut.conj g) hroot
  change g * firstLongRoot K r a * g⁻¹ ∈ _ at h
  rw [first_root_eq_actual r hr a, actualNaturalRootElement_conjugation r hr, hg] at h
  exact h

theorem isNaturalRootElement_iff_sylowCenterElements (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (A : elementaryRootGroup K (r + 1)) :
    IsNaturalRootElement r hr A ↔
      A ∈ sylowCenterElements (G := elementaryRootGroup K (r + 1)) p := by
  constructor
  · rintro ⟨v, a, rfl⟩
    exact naturalRootElement_mem_sylowCenterElements p r hr v a
  · exact sylowCenterElements_isNaturalRootElement p r hr htwo

theorem automorphism_isNaturalRootElement_iff (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (f : MulAut (elementaryRootGroup K (r + 1)))
    (A : elementaryRootGroup K (r + 1)) :
    IsNaturalRootElement r hr (f A) ↔ IsNaturalRootElement r hr A := by
  rw [isNaturalRootElement_iff_sylowCenterElements p r hr htwo,
    isNaturalRootElement_iff_sylowCenterElements p r hr htwo]
  exact automorphism_mem_sylowCenterElements_iff p f A

end SymmetricSubgroupAsymptotics.CFSGSymplecticOddRootRecognition
