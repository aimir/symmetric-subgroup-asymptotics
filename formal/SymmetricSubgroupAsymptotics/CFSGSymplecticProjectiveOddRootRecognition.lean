import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveUnipotent
import SymmetricSubgroupAsymptotics.CFSGSymplecticOddRootRecognition
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveNaturalRootLines
import SymmetricSubgroupAsymptotics.CFSGSylowCenterQuotients

/-! Intrinsic odd-characteristic root-element recognition directly
in the original projective C group. No automorphism of the projective
quotient is assumed to lift to the elementary covering group. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveOddRootRecognition
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticUnipotent CFSGSylowCenterRecognition
variable {K : Type} [Field K] [Finite K]

def IsProjectiveNaturalRootElement (r : ℕ) (hr : 0 < r)
    (A : elementaryProjective K (r + 1)) : Prop :=
  ∃ v : Index (r + 1) → K, ∃ a : K,
    A = projectiveNaturalRootHom r hr v (Multiplicative.ofAdd a)

theorem projectiveNaturalRootElement_mem_sylowCenterElements (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r)
    (v : Index (r + 1) → K) (a : K) :
    projectiveNaturalRootHom r hr v (Multiplicative.ofAdd a) ∈
      sylowCenterElements (G := elementaryProjective K (r + 1)) p :=
  map_mem_sylowCenterElements p
    (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))))
    (QuotientGroup.mk'_surjective _)
    (CFSGSymplecticOddRootRecognition.naturalRootElement_mem_sylowCenterElements p r hr v a)

theorem sylowCenterElements_isProjectiveNaturalRootElement (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    {A : elementaryProjective K (r + 1)}
    (hA : A ∈ sylowCenterElements (G := elementaryProjective K (r + 1)) p) :
    IsProjectiveNaturalRootElement r hr A := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  let P := projectiveUnipotentSylow K p r hr
  obtain ⟨g, z, hz, hg⟩ := exists_conjugate_fixed_sylow_center p P hA
  let e := unipotentProjectiveEquiv K r
  let u : unipotent K (r + 1) := e.symm z
  have hu : u ∈ Subgroup.center (unipotent K (r + 1)) :=
    ((Subgroup.centerCongr e).symm ⟨z, hz⟩).property
  obtain ⟨a, ha⟩ := center_eq_highestLong_of_two_ne_zero r hr htwo u hu
  have hzu : (z : elementaryProjective K (r + 1)) = q u.val := by
    have he := congrArg Subtype.val (e.apply_symm_apply z)
    exact he.symm
  have hza : (z : elementaryProjective K (r + 1)) = q (firstLongRoot K r a) := by
    calc
      _ = q u.val := hzu
      _ = _ := congrArg q ((congrArg Subtype.val ha).trans (highestLongInU_val r hr a))
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (elementaryRootGroup K (r + 1))) g
  let v : Index (r + 1) → K := Pi.single (Sum.inl (0 : Fin (r + 1))) 1
  have hfirst : q (firstLongRoot K r a) =
      projectiveNaturalRootHom r hr v (Multiplicative.ofAdd a) := by
    apply congrArg q
    apply elementary_eq_of_mulVec_eq
    intro x
    change ((firstLongRoot K r a).val : Mat K (r + 1)) *ᵥ x =
      ((actualNaturalRootElement r hr v a).val : Mat K (r + 1)) *ᵥ x
    rw [firstLongRoot_mulVec_eq_transvection, actualNaturalRootElement_apply]
  rw [hza, hfirst, ← hg₀] at hg
  rw [projectiveNaturalRootElement_conjugation] at hg
  exact ⟨_, a, hg.symm⟩

theorem isProjectiveNaturalRootElement_iff_sylowCenterElements (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (A : elementaryProjective K (r + 1)) :
    IsProjectiveNaturalRootElement r hr A ↔
      A ∈ sylowCenterElements (G := elementaryProjective K (r + 1)) p := by
  constructor
  · rintro ⟨v, a, rfl⟩
    exact projectiveNaturalRootElement_mem_sylowCenterElements p r hr v a
  · exact sylowCenterElements_isProjectiveNaturalRootElement p r hr htwo

theorem automorphism_isProjectiveNaturalRootElement_iff (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (f : MulAut (elementaryProjective K (r + 1)))
    (A : elementaryProjective K (r + 1)) :
    IsProjectiveNaturalRootElement r hr (f A) ↔
      IsProjectiveNaturalRootElement r hr A := by
  rw [isProjectiveNaturalRootElement_iff_sylowCenterElements p r hr htwo,
    isProjectiveNaturalRootElement_iff_sylowCenterElements p r hr htwo]
  exact automorphism_mem_sylowCenterElements_iff p f A

end SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveOddRootRecognition
