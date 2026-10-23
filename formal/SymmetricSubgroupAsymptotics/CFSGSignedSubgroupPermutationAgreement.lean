import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Commute.Hom

/-! Cross-sign commutation matches the two permutations of intrinsic
subgroup families. The parameter groups may vary with the label, as in
folded singleton and paired root groups over different fields. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSignedSubgroupPermutationAgreement
variable {G I : Type*} [Group G]

theorem permutations_agree (R S : I→Subgroup G)
    (hcross : ∀i j,i≠j→∀a∈R i,∀b∈S j,Commute a b)
    (hdiag : ∀i,∃a∈R i,∃b∈S i,¬Commute a b)
    (f : MulAut G) (sigma tau : Equiv.Perm I)
    (hR : ∀i,(R i).map f.toMonoidHom=R (sigma i))
    (hS : ∀i,(S i).map f.toMonoidHom=S (tau i)) : sigma=tau := by
  classical
  ext i
  let j := tau.symm (sigma i)
  have htau : tau j=sigma i := tau.apply_symm_apply _
  by_contra hne
  have hij : i≠j := by
    intro he
    exact hne ((congrArg tau he).trans htau).symm
  obtain ⟨a,ha,b,hb,hab⟩ := hdiag (sigma i)
  have ha' : a∈(R i).map f.toMonoidHom := by rw [hR];exact ha
  have hb' : b∈(S j).map f.toMonoidHom := by rw [hS,htau];exact hb
  obtain ⟨x,hx,hfx⟩ := ha'
  obtain ⟨y,hy,hfy⟩ := hb'
  apply hab
  have h := (hcross i j hij x hx y hy).map f.toMonoidHom
  simpa only [hfx,hfy] using h

end SymmetricSubgroupAsymptotics.CFSGSignedSubgroupPermutationAgreement
