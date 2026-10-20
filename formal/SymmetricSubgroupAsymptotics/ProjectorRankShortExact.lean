import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact projector rank sharing along an actual linear quotient map.
The kernel projector is the literal restriction; no replacement section
or supplied total-capacity premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProjectorRankShortExact

theorem range_rank_le {k V W : Type} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (f : V →ₗ[k] W) (P : Module.End k V) (Q : Module.End k W)
    (U : Module.End k f.ker) (hP : P^2=P)
    (hinter : ∀ v, f (P v)=Q (f v))
    (hU : ∀ v : f.ker, (U v : V)=P v) :
    Module.finrank k P.range≤Module.finrank k U.range+Module.finrank k Q.range := by
  let g : P.range →ₗ[k] W := f.comp P.range.subtype
  have hgr : g.range≤Q.range := by
    rintro x ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := v.property
    refine ⟨f w,?_⟩
    change Q (f w)=f v.val
    rw [← hinter,hw]
  have hfix : ∀ v : P.range, P v.val=v.val := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    rw [← hw]
    exact congrArg (fun t : Module.End k V => t w) hP
  let j : g.ker →ₗ[k] f.ker := {
    toFun v := ⟨v.val.val,v.property⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hjr : ∀ v : g.ker, j v∈U.range := by
    intro v
    refine ⟨j v,?_⟩
    apply Subtype.ext
    rw [hU]
    exact hfix v.val
  let jR := j.codRestrict U.range hjr
  have hj : Function.Injective jR := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : U.range => ((z : f.ker) : V)) h
  have hk := jR.finrank_le_finrank_of_injective hj
  have hr := Submodule.finrank_mono hgr
  have hg := g.finrank_range_add_finrank_ker
  omega

end SymmetricSubgroupAsymptotics.ProjectorRankShortExact
