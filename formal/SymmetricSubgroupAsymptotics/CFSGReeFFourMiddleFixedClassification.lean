import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedParameters

/-! Exact fixedness inside the bounded four-coordinate middle cell.
This classifies that actual cell only, and supplies no whole-U cover. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedClassification
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWordInjective
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedModelEquivalence

theorem middleWord_fixed_iff (m : ℕ) (a b c d : Field m) :
    reeAutomorphism m (middleWord m a b c d)=middleWord m a b c d ↔
      b=alpha m a ∧ d=alpha m c+a^2*alpha m a := by
  constructor
  · intro hf
    have he := (middleWord_twist m a b c d).symm.trans hf
    have h := middleWord_parameters_eq m (beta m b) (alpha m a)
      (beta m d+beta m b*alpha m a) (alpha m c+(beta m b)^2*alpha m a) a b c d he
    refine ⟨h.2.1.symm,?_⟩
    have hlast := h.2.2.2.symm
    rw [h.1] at hlast
    exact hlast
  · rintro ⟨rfl,rfl⟩
    exact fixedMiddleWord_fixed m a c

theorem exists_fixedMiddleParameter_of_word (m : ℕ) (g : originalModelFixed m)
    (hg : ∃a b c d : Field m,middleWord m a b c d=g.val) :
    ∃p : Field m×Field m,fixedMiddleParameter m p=g := by
  obtain ⟨a,b,c,d,hg⟩ := hg
  have hf : reeAutomorphism m (middleWord m a b c d)=middleWord m a b c d := by
    rw [hg]
    exact g.property
  obtain ⟨hb,hparamd⟩ := (middleWord_fixed_iff m a b c d).mp hf
  refine ⟨(a,c),Subtype.ext ?_⟩
  change fixedMiddleWord m a c=g.val
  rw [←hg,hb,hparamd]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedClassification
