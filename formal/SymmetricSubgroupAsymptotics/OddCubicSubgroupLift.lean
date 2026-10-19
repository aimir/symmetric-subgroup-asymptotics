import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction

/-! Lift the WHOLE actual elementary ternary subgroup through a binary
kernel. A Sylow subgroup of its original preimage supplies a cubic lift;
no independent local lifts or split extension are postulated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddCubicSubgroupLift
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

 theorem exists_lift {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
    (pi : G →* B) (hpi : Function.Surjective pi) (hker : IsPGroup 2 pi.ker)
    (O : Subgroup B) (hO : IsPGroup 3 O) (hcubic : ∀ o : O,o^3=1) :
    ∃ P : Subgroup G,IsPGroup 3 P ∧ P≤O.comap pi ∧ P.map pi=O ∧ ∀ p : P,p^3=1 := by
  let H := O.comap pi
  let f : H →* O :=
    { toFun := fun h => ⟨pi h.val,h.property⟩
      map_one' := Subtype.ext pi.map_one
      map_mul' a b := Subtype.ext (pi.map_mul a.val b.val) }
  have hf : Function.Surjective f := by
    intro o
    obtain ⟨g,hg⟩ := hpi o.val
    exact ⟨⟨g,by change pi g∈O; rw [hg]; exact o.property⟩,Subtype.ext hg⟩
  let S : Sylow 3 H := Classical.choice inferInstance
  have hs : Function.Surjective (f.comp (S : Subgroup H).subtype) :=
    sylow_restrict_surjective S hO f hf
  let P : Subgroup G := (S : Subgroup H).map H.subtype
  have hP : IsPGroup 3 P := S.isPGroup'.map H.subtype
  have hPH : P≤H := by
    rintro g ⟨h,_hh,rfl⟩
    exact h.property
  have hmap : P.map pi=O := by
    apply le_antisymm
    · rintro b ⟨g,hg,rfl⟩
      exact hPH hg
    · intro o ho
      obtain ⟨s,hs⟩ := hs ⟨o,ho⟩
      refine ⟨s.val.val,⟨s.val,s.property,rfl⟩,?_⟩
      exact congrArg Subtype.val hs
  refine ⟨P,hP,hPH,hmap,?_⟩
  intro p
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide) P pi.ker hP hker
  apply Subtype.ext
  apply Subgroup.mem_bot.mp
  apply disjoint_iff_inf_le.mp hd
  refine ⟨P.pow_mem p.property 3,?_⟩
  change pi (p.val^3)=1
  rw [map_pow]
  exact congrArg Subtype.val (hcubic ⟨pi p.val,hPH p.property⟩)

end SymmetricSubgroupAsymptotics.OddCubicSubgroupLift
