import SymmetricSubgroupAsymptotics.CFSGConjugateComap
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Restrict an actual ambient opposite-conjugate alignment to an
injectively embedded group whose positive subgroup covers the full
ambient positive group. The negative target is its genuine comap;
no assertion about the rest of the ambient fixed group is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupOppositeAlignmentRestriction
open CFSGConjugateComap CFSGSubgroupConjugateRestriction

theorem restrict_alignment {G H : Type*} [Group G] [Group H]
    (i : G→*H) (hi : Function.Injective i) (U : Subgroup G) (R S : Subgroup H)
    (hU : U.map i=R)
    (halign : ∀g : G,R⊓R.map (MulAut.conj (i g)).toMonoidHom=⊥→
      ∃u∈R,R.map (MulAut.conj (i g)).toMonoidHom=S.map (MulAut.conj u).toMonoidHom)
    (g : G) (hdisj : U⊓U.map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈U,U.map (MulAut.conj g).toMonoidHom=(S.comap i).map (MulAut.conj b).toMonoidHom := by
  have hraw : R⊓R.map (MulAut.conj (i g)).toMonoidHom=⊥ := by
    have hh := congrArg (fun T : Subgroup G=>T.map i) hdisj
    dsimp only at hh
    rwa [Subgroup.map_inf _ _ _ hi,map_conjugate,hU,Subgroup.map_bot] at hh
  obtain ⟨u,hu,he⟩ := halign g hraw
  have huim : u∈U.map i := hU.symm ▸ hu
  obtain ⟨b,hb,hbu⟩ := huim
  have hc : R.comap i=U := by
    rw [←hU,Subgroup.comap_map_eq_self_of_injective (f := i) hi]
  rw [←hbu] at he
  have hh := congrArg (fun T : Subgroup H=>T.comap i) he
  dsimp only at hh
  rw [comap_conjugate,comap_conjugate,hc] at hh
  exact ⟨b,hb,hh⟩

end SymmetricSubgroupAsymptotics.CFSGSubgroupOppositeAlignmentRestriction
