import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarSubgroup

/-! Ambient conjugacy of all nonzero parameters of the literal D root
star. The conjugators are the checked actual determinant-one form
conjugators, followed by the SAME faithful SL double embedding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarConjugacy
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexStarSubgroup
open CFSGTypeAProjectivePointRoots CFSGTypeAColumnRootConjugacy CFSGTypeABlockEmbedding
variable (K : Type) [Field K]

theorem star_nonidentity_conjugate (s : ℕ) (a b : starRoot K s) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ z : elementaryProjective K (s + 4),
      z * (a : elementaryProjective K (s + 4)) * z⁻¹ = b := by
  obtain ⟨f, hf⟩ := a.property
  obtain ⟨g, hg⟩ := b.property
  have hf0 : f.toAdd ≠ 0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [← hf, show f = 1 from congrArg Multiplicative.ofAdd he, map_one]
    rfl
  have hg0 : g.toAdd ≠ 0 := by
    intro he
    apply hb
    apply Subtype.ext
    rw [← hg, show g = 1 from congrArg Multiplicative.ofAdd he, map_one]
    rfl
  obtain ⟨A, hA⟩ := exists_form_conjugator
    (F := K) (0 : Fin (s + 3)) (⟨1, by omega⟩ : Fin (s + 3))
    (by intro he; have hv := congrArg Fin.val he; change 0 = 1 at hv; omega)
    f.toAdd g.toAdd hf0 hg0
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))
  let j := pi.comp (starEmbedding K s)
  refine ⟨j A, ?_⟩
  rw [← hf, ← hg]
  change j A * j (transvectionSL f.toAdd.property) * (j A)⁻¹ = j (transvectionSL g.toAdd.property)
  have he := congrArg j hA
  simpa only [map_mul, map_inv] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarConjugacy
