import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import Mathlib.GroupTheory.Sylow

/-! Maps to an actual finite p-group are determined by their restriction
to any one original Sylow subgroup. Surjective maps remain surjective.
The injectivity argument uses the joint image of two maps, so it does not
assume that the original source is a p-group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {p : ℕ} [Fact p.Prime] {J Q : Type*} [Group J] [Group Q]
    [Finite J] [Finite Q]

omit [Finite Q] in
theorem sylow_restrict_surjective (P : Sylow p J) (hQ : IsPGroup p Q)
    (f : J→*Q) (hf : Function.Surjective f) :
    Function.Surjective (f.comp (P:Subgroup J).subtype) := by
  have ht : (⊤:Subgroup Q)=(P:Subgroup J).map f :=
    (P.mapSurjective hf).is_maximal' (hQ.to_subgroup ⊤) le_top
  intro q
  have hq : q∈(P:Subgroup J).map f := ht ▸ Subgroup.mem_top q
  obtain ⟨x,hx,hfx⟩ := hq
  exact ⟨⟨x,hx⟩,hfx⟩

def sylowEpimorphismRestriction (P : Sylow p J) (hQ : IsPGroup p Q) :
    GroupEpimorphism J Q→GroupEpimorphism (P:Subgroup J) Q :=
  fun f=>⟨f.1.comp (P:Subgroup J).subtype,sylow_restrict_surjective P hQ f.1 f.2⟩

theorem sylow_pGroup_hom_restriction_injective (P : Sylow p J) (hQ : IsPGroup p Q) :
    Function.Injective (fun f : J→*Q=>f.comp (P:Subgroup J).subtype) := by
  intro f g he
  let d : J→*Q×Q := f.prod g
  have hQQ : IsPGroup p (Q×Q) := by
    obtain ⟨a,ha⟩ := hQ.exists_card_eq
    apply IsPGroup.of_card (n := a+a)
    simp only [Nat.card_prod,ha,pow_add]
  have hd := sylow_restrict_surjective P (hQQ.to_subgroup d.range)
    d.rangeRestrict d.rangeRestrict_surjective
  ext x
  obtain ⟨y,hy⟩ := hd (d.rangeRestrict x)
  have hxy : d (y:J)=d x := congrArg Subtype.val hy
  have hfg : f (y:J)=g (y:J) := DFunLike.congr_fun he y
  exact (congrArg Prod.fst hxy).symm.trans (hfg.trans (congrArg Prod.snd hxy))

theorem sylowEpimorphismRestriction_injective (P : Sylow p J) (hQ : IsPGroup p Q) :
    Function.Injective (sylowEpimorphismRestriction P hQ) := by
  intro f g he
  apply Subtype.ext
  exact sylow_pGroup_hom_restriction_injective P hQ (congrArg Subtype.val he)

theorem groupEpimorphism_card_le_sylow (P : Sylow p J) (hQ : IsPGroup p Q) :
    Nat.card (GroupEpimorphism J Q)≤Nat.card (GroupEpimorphism (P:Subgroup J) Q) := by
  letI : Finite (GroupEpimorphism (P:Subgroup J) Q) :=
    Finite.of_injective (fun f : GroupEpimorphism (P:Subgroup J) Q=>(f.1 : ↥(P:Subgroup J) → Q))
      (fun _ _ h=>Subtype.ext (DFunLike.coe_injective h))
  exact Nat.card_le_card_of_injective _ (sylowEpimorphismRestriction_injective P hQ)

/-! ## Detecting normal subgroups with p-group quotient -/

/-- A normal subgroup whose quotient is a `p`-group is determined by its
intersection with one fixed Sylow `p`-subgroup of the ambient group.

This is the kernel form of `sylow_pGroup_hom_restriction_injective`, but it
allows the two quotient maps to have different codomains.  The common
Sylow kernel first identifies those codomains; injectivity of restriction
then promotes the identification to the complete ambient source.  This is
the exact group-theoretic step used by relative character labels: a
character kernel inside a characteristic `p`-core can be recovered from
its restriction to one actual Sylow subgroup. -/
theorem normal_eq_of_sylow_comap_eq
    (P : Sylow p J) (N M : Subgroup J) [N.Normal] [M.Normal]
    (hN : IsPGroup p (J ⧸ N)) (hM : IsPGroup p (J ⧸ M))
    (h : N.comap (P : Subgroup J).subtype =
      M.comap (P : Subgroup J).subtype) :
    N = M := by
  let f : GroupEpimorphism J (J ⧸ N) :=
    ⟨QuotientGroup.mk' N, QuotientGroup.mk'_surjective N⟩
  let g : GroupEpimorphism J (J ⧸ M) :=
    ⟨QuotientGroup.mk' M, QuotientGroup.mk'_surjective M⟩
  let f' := sylowEpimorphismRestriction P hN f
  let g' := sylowEpimorphismRestriction P hM g
  have hker : f'.1.ker = g'.1.ker := by
    change N.comap (P : Subgroup J).subtype =
      M.comap (P : Subgroup J).subtype
    exact h
  let e : (J ⧸ N) ≃* (J ⧸ M) := epimorphismChangeTarget f' g' hker
  have heq : e.toMonoidHom.comp f.1 = g.1 := by
    apply sylow_pGroup_hom_restriction_injective P hM
    ext x
    exact epimorphismChangeTarget_apply f' g' hker x
  ext x
  change f.1 x = 1 ↔ g.1 x = 1
  rw [← heq]
  exact e.map_eq_one_iff.symm

/-- Kernel version of `normal_eq_of_sylow_comap_eq`.  It is convenient
when the two normal subgroups already occur as kernels of maps whose images
are `p`-groups. -/
theorem hom_ker_eq_of_sylow_ker_eq
    {A B : Type*} [Group A] [Group B]
    (P : Sylow p J) (f : J →* A) (g : J →* B)
    (hf : IsPGroup p f.range) (hg : IsPGroup p g.range)
    (h : (f.comp (P : Subgroup J).subtype).ker =
      (g.comp (P : Subgroup J).subtype).ker) :
    f.ker = g.ker := by
  let ef : (J ⧸ f.ker) ≃* f.range := QuotientGroup.quotientKerEquivRange f
  let eg : (J ⧸ g.ker) ≃* g.range := QuotientGroup.quotientKerEquivRange g
  have hfq : IsPGroup p (J ⧸ f.ker) := hf.of_equiv ef.symm
  have hgq : IsPGroup p (J ⧸ g.ker) := hg.of_equiv eg.symm
  apply normal_eq_of_sylow_comap_eq P f.ker g.ker hfq hgq
  change f.ker.comap (P : Subgroup J).subtype =
    g.ker.comap (P : Subgroup J).subtype
  exact h

end SymmetricSubgroupAsymptotics
