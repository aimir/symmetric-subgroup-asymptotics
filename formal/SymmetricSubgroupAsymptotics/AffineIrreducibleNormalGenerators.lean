import SymmetricSubgroupAsymptotics.AffineSimpleComplementNormalChain
import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-!
# Normal generators inherited from an irreducible affine complement

Every nontrivial normal subgroup of a faithful irreducible affine group
contains the translations. If its image in the complement is nontrivial,
lift normal generators of that image. Their normal closure is nontrivial,
so it already contains the translations and equals the original subgroup.
The translation subgroup itself needs only one ambient normal generator.

Thus a positive uniform bound for normal subgroups of the complement is
inherited without an additional generator. The separate normal-chain
variant needs only comparability of normal subgroups of the complement.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

open SemidirectProduct

variable {p d : ℕ} [Fact p.Prime]
variable (R : Subgroup (GLV p d))

/-- Comparability of normal subgroups passes from the complement to the
faithful irreducible affine group. -/
theorem normal_total_of_irreducible_complement
    (hirr : Irreducible R)
    (hR : ∀ A B : Subgroup R, A.Normal → B.Normal → A ≤ B ∨ B ≤ A) :
    ∀ A B : Subgroup (Aff R), A.Normal → B.Normal → A ≤ B ∨ B ≤ A := by
  intro A B hA hB
  by_cases hAb : A = ⊥
  · left
    rw [hAb]
    exact bot_le
  by_cases hBb : B = ⊥
  · right
    rw [hBb]
    exact bot_le
  letI := hA
  letI := hB
  let π : Aff R →* R := rightHom
  have hπ : Function.Surjective π := rightHom_surjective
  have hkerA : π.ker ≤ A := by
    change (rightHom : Aff R →* R).ker ≤ A
    rw [← range_inl_eq_ker_rightHom]
    exact Vsub_le_normal hirr A hAb
  have hkerB : π.ker ≤ B := by
    change (rightHom : Aff R →* R).ker ≤ B
    rw [← range_inl_eq_ker_rightHom]
    exact Vsub_le_normal hirr B hBb
  rcases hR (A.map π) (B.map π) (hA.map π hπ) (hB.map π hπ) with h | h
  · left
    calc
      A = (A.map π).comap π := (Subgroup.comap_map_eq_self hkerA).symm
      _ ≤ (B.map π).comap π := Subgroup.comap_mono h
      _ = B := Subgroup.comap_map_eq_self hkerB
  · right
    calc
      B = (B.map π).comap π := (Subgroup.comap_map_eq_self hkerB).symm
      _ ≤ (A.map π).comap π := Subgroup.comap_mono h
      _ = A := Subgroup.comap_map_eq_self hkerA

/-- Every quotient socle is normally cyclic when the complement has a
chain of normal subgroups. -/
theorem quotientSocle_one_of_irreducible_normal_total
    (hirr : Irreducible R)
    (hR : ∀ A B : Subgroup R, A.Normal → B.Normal → A ≤ B ∨ B ≤ A)
    (N : Subgroup (Aff R)) [N.Normal] :
    SocleNormalGeneratorBound (Aff R ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total
    (normal_total_of_irreducible_complement R hirr hR) N

/-- A positive uniform ambient normal-generator bound for the complement
is inherited by every normal subgroup of the original affine group. -/
theorem normal_generating_tuples_of_irreducible_complement
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    {t : ℕ} (ht : 0 < t)
    (hR : ∀ M : Subgroup R, M.Normal →
      ∃ x : Fin t → R, Subgroup.normalClosure (Set.range x) = M) :
    ∀ N : Subgroup (Aff R), N.Normal →
      ∃ x : Fin t → Aff R, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  by_cases hNb : N = ⊥
  · refine ⟨fun _ ↦ 1, ?_⟩
    rw [hNb]
    apply le_antisymm _ bot_le
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact one_mem _
  let π : Aff R →* R := rightHom
  have hπ : Function.Surjective π := rightHom_surjective
  by_cases hMb : N.map π = ⊥
  · have hNV : N = Vsub R := by
      apply le_antisymm
      · intro x hx
        apply (mem_Vsub R x).mpr
        have himage : π x ∈ N.map π := ⟨x, hx, rfl⟩
        rw [hMb] at himage
        exact Subgroup.mem_bot.mp himage
      · exact Vsub_le_normal hirr N hNb
    let g : Aff R := inl (Multiplicative.ofAdd v)
    let x : Fin t → Aff R := fun _ ↦ g
    let L := Subgroup.normalClosure (Set.range x)
    have hLV : L ≤ Vsub R := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨i, rfl⟩
      exact ⟨Multiplicative.ofAdd v, rfl⟩
    have hLb : L ≠ ⊥ := by
      intro h
      apply inl_ofAdd_ne_one R hv
      apply Subgroup.mem_bot.mp
      rw [← h]
      exact Subgroup.subset_normalClosure ⟨(⟨0, ht⟩ : Fin t), rfl⟩
    letI : L.Normal := by dsimp [L]; infer_instance
    refine ⟨x, ?_⟩
    change L = N
    exact (le_antisymm hLV (Vsub_le_normal hirr L hLb)).trans hNV.symm
  · obtain ⟨x, hx⟩ := hR (N.map π) (hN.map π hπ)
    have hlift : ∀ i, ∃ y : Aff R, y ∈ N ∧ π y = x i := by
      intro i
      have hxi : x i ∈ N.map π := by
        rw [← hx]
        exact Subgroup.subset_normalClosure (Set.mem_range_self i)
      exact hxi
    choose y hy hπy using hlift
    let L := Subgroup.normalClosure (Set.range y)
    letI : L.Normal := by dsimp [L]; infer_instance
    have hLN : L ≤ N := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨i, rfl⟩
      exact hy i
    have himage : π '' Set.range y = Set.range x := by
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hπy i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨y i, Set.mem_range_self i, hπy i⟩
    have hmap : L.map π = N.map π := by
      dsimp [L]
      rw [Subgroup.map_normalClosure _ _ hπ, himage]
      exact hx
    have hLb : L ≠ ⊥ := by
      intro h
      apply hMb
      rw [← hmap, h, Subgroup.map_bot]
    have hkerL : π.ker ≤ L := by
      change (rightHom : Aff R →* R).ker ≤ L
      rw [← range_inl_eq_ker_rightHom]
      exact Vsub_le_normal hirr L hLb
    refine ⟨y, ?_⟩
    change L = N
    calc
      L = (L.map π).comap π := (Subgroup.comap_map_eq_self hkerL).symm
      _ = (N.map π).comap π := by rw [hmap]
      _ = N := Subgroup.comap_map_eq_self (hkerL.trans hLN)

/-- Every actual normal quotient retains the complement's positive uniform
bound, with no additional position for the affine translations. -/
theorem quotientSocle_of_irreducible_complement_normal_generators
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    {t : ℕ} (ht : 0 < t)
    (hR : ∀ M : Subgroup R, M.Normal →
      ∃ x : Fin t → R, Subgroup.normalClosure (Set.range x) = M)
    (N : Subgroup (Aff R)) [N.Normal] :
    SocleNormalGeneratorBound (Aff R ⧸ N) t :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_of_irreducible_complement R hirr v hv ht hR) N

end AffineModel
end SymmetricSubgroupAsymptotics

end
