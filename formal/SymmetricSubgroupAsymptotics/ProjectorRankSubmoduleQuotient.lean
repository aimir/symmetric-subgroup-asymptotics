import SymmetricSubgroupAsymptotics.ProjectorRankShortExact

/-! Exact projector sharing directly on a displayed submodule and its
literal mkQ quotient. This avoids replacing the original intersection
with an equal but differently typed kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProjectorRankSubmoduleQuotient

theorem range_rank_le {k V : Type} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Submodule k V) (P : Module.End k V)
    (Q : Module.End k (V ⧸ S)) (U : Module.End k S) (hP : P^2=P)
    (hinter : ∀ v, S.mkQ (P v)=Q (S.mkQ v))
    (hU : ∀ v : S, (U v : V)=P v) :
    Module.finrank k P.range≤Module.finrank k U.range+Module.finrank k Q.range := by
  let g : P.range →ₗ[k] V ⧸ S := S.mkQ.comp P.range.subtype
  have hgr : g.range≤Q.range := by
    rintro x ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := v.property
    refine ⟨S.mkQ w,?_⟩
    change Q (S.mkQ w)=S.mkQ v.val
    rw [← hinter,hw]
  have hfix : ∀ v : P.range, P v.val=v.val := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    rw [← hw]
    exact congrArg (fun t : Module.End k V => t w) hP
  let j : g.ker →ₗ[k] S := {
    toFun v := ⟨v.val.val,by
      have hh : v.val.val∈S.mkQ.ker := v.property
      rwa [Submodule.ker_mkQ] at hh⟩
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
    exact congrArg (fun z : U.range => ((z : S) : V)) h
  have hk := jR.finrank_le_finrank_of_injective hj
  have hr := Submodule.finrank_mono hgr
  have hg := g.finrank_range_add_finrank_ker
  omega

end SymmetricSubgroupAsymptotics.ProjectorRankSubmoduleQuotient
