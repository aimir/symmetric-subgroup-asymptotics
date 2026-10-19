import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SurjectiveProjectorRank

theorem rank_le {k V W : Type} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (P : Module.End k V) (Q : Module.End k W)
    (hinter : ∀ v, q (P v)=Q (q v)) :
    Module.finrank k Q.range ≤ Module.finrank k P.range := by
  let f : P.range →ₗ[k] W := q.comp P.range.subtype
  have hmem : ∀ v : P.range, f v ∈ Q.range := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨q w, (hinter w).symm.trans (congrArg q hw)⟩
  let fR := f.codRestrict Q.range hmem
  have hf : Function.Surjective fR := by
    intro y
    obtain ⟨w,hw⟩ := y.property
    obtain ⟨v,hv⟩ := hq w
    refine ⟨⟨P v,v,rfl⟩,?_⟩
    apply Subtype.ext
    change q (P v)=y.val
    rw [hinter,hv]
    exact hw
  exact fR.finrank_le_finrank_of_surjective hf

end SymmetricSubgroupAsymptotics.SurjectiveProjectorRank
