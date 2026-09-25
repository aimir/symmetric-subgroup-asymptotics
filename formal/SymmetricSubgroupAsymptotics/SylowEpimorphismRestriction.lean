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

end SymmetricSubgroupAsymptotics
