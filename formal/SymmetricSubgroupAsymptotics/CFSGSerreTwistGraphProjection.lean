import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible

/-! The first projection of the ACTUAL generated twist graph is onto the
ACTUAL untwisted model. This uses the now-proved invertibility of every
prescribed second root operator. It asserts no functionality, injectivity,
or identification with a Steinberg graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]

/-- Both coordinates of every original graph element remain in the
original untwisted subgroup. -/
theorem twistGraph_le_model_prod (perm : Fin n → Fin n) (exponent : Fin n → ℕ) :
    twistGraph A K perm exponent ≤ (subgroup A K).prod (subgroup A K) := by
  apply (Subgroup.closure_le _).mpr
  rintro gh ⟨negative, i, t, h1, h2⟩
  exact ⟨Subgroup.subset_closure ⟨negative, i, t, h1⟩,
    Subgroup.subset_closure ⟨negative, perm i, t ^ exponent i, h2⟩⟩

theorem twistGraph_fst_image_eq_model (perm : Fin n → Fin n) (exponent : Fin n → ℕ) :
    (twistGraph A K perm exponent).map (MonoidHom.fst (Ambient A K) (Ambient A K)) = subgroup A K := by
  apply le_antisymm
  · rintro g ⟨gh, hgh, rfl⟩
    exact (twistGraph_le_model_prod A K perm exponent hgh).1
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨negative, i, t, hg⟩
    refine ⟨(g, rootEquiv A K negative (perm i) (t ^ exponent i)), ?_, rfl⟩
    exact Subgroup.subset_closure ⟨negative, i, t, hg, rfl⟩

def twistGraphFirstProjection (perm : Fin n → Fin n) (exponent : Fin n → ℕ) :
    twistGraph A K perm exponent →* Model A K where
  toFun g := ⟨g.val.1, (twistGraph_le_model_prod A K perm exponent g.property).1⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl

theorem twistGraphFirstProjection_surjective (perm : Fin n → Fin n) (exponent : Fin n → ℕ) :
    Function.Surjective (twistGraphFirstProjection A K perm exponent) := by
  intro g
  have hg : g.val ∈ (twistGraph A K perm exponent).map
      (MonoidHom.fst (Ambient A K) (Ambient A K)) := by
    rw [twistGraph_fst_image_eq_model]
    exact g.property
  obtain ⟨gh, hgh, he⟩ := hg
  exact ⟨⟨gh, hgh⟩, Subtype.ext he⟩

end SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
