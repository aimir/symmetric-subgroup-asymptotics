import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences

/-! An abelian kernel's ambient normal generators lift ordinary
generators of the actual quotient. Normal closure alone would not suffice
for arbitrary kernels. The proof uses the abelian supplement property and
keeps both finite generating sets in the original source. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

open MarkedC4 LargeOrbitGeneratorConsequences

variable {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]

theorem genRank_le_quotient_add_normalGen
    (f : G →* Q) (hf : Function.Surjective f)
    [IsMulCommutative f.ker] :
    genRank G ≤ genRank Q + normalGen f.ker := by
  obtain ⟨S, hcardS, hgenS⟩ := genRank_spec (G := Q)
  let lift : Q → G := fun q => Classical.choose (hf q)
  have hlift : ∀ q, f (lift q) = q := fun q => Classical.choose_spec (hf q)
  let T : Finset G := S.image lift
  let H := Subgroup.closure (T : Set G)
  have hmap : H.map f = ⊤ := by
    dsimp [H]
    rw [MonoidHom.map_closure]
    have himage : f '' (T : Set G) = S := by
      ext q
      simp only [T, Finset.coe_image, Set.mem_image]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        simpa only [hlift] using hy
      · intro hq
        exact ⟨lift q, ⟨q, hq, rfl⟩, hlift q⟩
    rw [himage, hgenS]
  have hsupp : H ⊔ f.ker = ⊤ := by
    apply sup_eq_top_of_map_eq_top f hf H f.ker le_rfl
    apply top_unique
    rw [← hmap]
    exact Subgroup.map_mono le_sup_left
  obtain ⟨A, hcardA, hmemA, hnormalA⟩ := normalGen_spec f.ker
  let e := Fintype.equivFin A
  let x : Fin (Fintype.card A) → G := fun i => (e.symm i).val
  have hrange : Set.range x = (A : Set G) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hg
      exact ⟨e ⟨g, hg⟩, congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)⟩
  have hgenerate : H ⊔ Subgroup.closure (A : Set G) = ⊤ := by
    rw [← hrange]
    exact sup_closure_eq_top_of_abelian_normalClosure f.ker x
      (by rw [hrange]; exact hmemA) (by rw [hrange]; exact hnormalA) H hsupp
  have hclosure : Subgroup.closure ((T ∪ A : Finset G) : Set G) = ⊤ := by
    rw [Finset.coe_union, Subgroup.closure_union]
    exact hgenerate
  calc
    genRank G ≤ (T ∪ A).card := genRank_le hclosure
    _ ≤ T.card + A.card := Finset.card_union_le T A
    _ ≤ S.card + A.card := Nat.add_le_add_right Finset.card_image_le _
    _ = genRank Q + normalGen f.ker := by rw [hcardS, hcardA]

end SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

end
