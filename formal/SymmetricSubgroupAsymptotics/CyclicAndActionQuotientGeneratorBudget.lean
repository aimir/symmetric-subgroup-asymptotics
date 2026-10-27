import SymmetricSubgroupAsymptotics.MetacyclicNormalGenerators
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A quotient detected by a cyclic coordinate and an actual action
coordinate costs at most one plus the generator cost of the action
image. This is an internal kernel-detection tool, not a model premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicAndActionQuotientGeneratorBudget
variable {A C B Q : Type} [Group A] [Finite A] [Group C] [IsCyclic C]
    [Group B] [Group Q]

theorem genRank_le_one_add (beta : A →* Q) (hbeta : Function.Surjective beta)
    (c : A →* C) (r : A →* B)
    (hdetect : c.ker ⊓ r.ker ≤ beta.ker) (b : ℕ)
    (hbudget : MarkedC4.genRank r.range ≤ b) : MarkedC4.genRank Q ≤ 1+b := by
  letI : Finite Q := Finite.of_surjective beta hbeta
  let phi : A →* C × B := c.prod r
  letI : Finite phi.range := Finite.of_surjective phi.rangeRestrict phi.rangeRestrict_surjective
  let t : phi.range →* B := (MonoidHom.snd C B).comp phi.range.subtype
  letI : Finite t.range := Finite.of_surjective t.rangeRestrict t.rangeRestrict_surjective
  let k : t.ker →* C := (MonoidHom.fst C B).comp (phi.range.subtype.comp t.ker.subtype)
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact h
    · have hx : x.val.val.2=1 := x.property
      have hy : y.val.val.2=1 := y.property
      exact hx.trans hy.symm
  letI : IsCyclic t.ker := isCyclic_of_injective k hk
  have ht : t.range=r.range := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      obtain ⟨a,ha⟩ := u.property
      exact ⟨a,congrArg Prod.snd ha⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨phi a,⟨a,rfl⟩⟩,rfl⟩
  have htr : MarkedC4.genRank t.range ≤ b := by rw [ht]; exact hbudget
  let e := QuotientGroup.quotientKerEquivRange t
  have hq : MarkedC4.genRank (phi.range ⧸ t.ker) ≤ b :=
    (MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective).trans htr
  have hsource : MarkedC4.genRank phi.range ≤ 1+b :=
    (MarkedC4.genRank_le_of_normal t.ker).trans
      (Nat.add_le_add MarkedC4.genRank_le_one_of_isCyclic hq)
  have hd : phi.ker ≤ beta.ker := by
    change (c.prod r).ker ≤ beta.ker
    rw [MonoidHom.ker_prod]
    exact hdetect
  let delta : A ⧸ phi.ker →* Q := QuotientGroup.lift phi.ker beta hd
  have hdelta : Function.Surjective delta := by
    intro q
    obtain ⟨a,ha⟩ := hbeta q
    exact ⟨QuotientGroup.mk a,ha⟩
  let ep := QuotientGroup.quotientKerEquivRange phi
  let f : phi.range →* Q := delta.comp ep.symm.toMonoidHom
  have hf : Function.Surjective f := hdelta.comp ep.symm.surjective
  exact (MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective f hf).trans hsource

end SymmetricSubgroupAsymptotics.CyclicAndActionQuotientGeneratorBudget
