import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Projector rank descends to a genuinely embedded invariant section.
This is the linear interface used for the literal intersection of the
binary socle with the original retained translation kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.IntertwiningProjectorRank

theorem rank_le {k V W : Type} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (j : V →ₗ[k] W) (hj : Function.Injective j)
    (P : Module.End k V) (Q : Module.End k W)
    (hinter : ∀ v, j (P v)=Q (j v)) :
    Module.finrank k P.range≤Module.finrank k Q.range := by
  let f : P.range →ₗ[k] W := j.comp P.range.subtype
  have hmem : ∀ v : P.range, f v∈Q.range := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    refine ⟨j w,?_⟩
    change Q (j w)=j v.val
    rw [← hinter,hw]
  let fR := f.codRestrict Q.range hmem
  have hf : Function.Injective fR := by
    intro x y h
    apply Subtype.ext
    apply hj
    exact congrArg (fun z : Q.range => (z : W)) h
  exact fR.finrank_le_finrank_of_injective hf

end SymmetricSubgroupAsymptotics.IntertwiningProjectorRank
