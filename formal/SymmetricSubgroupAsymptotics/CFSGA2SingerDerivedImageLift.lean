import SymmetricSubgroupAsymptotics.CFSGA2SingerGeneratedDerived

/-! Map the actual selected matrix-root commutator into an original source
image. Only the four generator images need original source witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGA2SingerDerivedImageLift
open CFSGA2SingerGeneratedDerived
variable {T G S : Type*} [Group T] [Group G] [Group S]

def rootLift (root : Bool→Fin 2→T) (neg : Bool) (i : Fin 2) : selectedGroup root :=
  ⟨root neg i,Subgroup.subset_closure ⟨(neg,i),rfl⟩⟩

theorem exists_original_derived_preimage (root : Bool→Fin 2→T) (omega : T)
    (hsquare : ∀neg i,(root neg i)^2=1)
    (hthree : ((root false 0*root true 0*root false 0)*
      (root false 1*root true 1*root false 1))^3=1)
    (hseven : (root false 0*(root false 0*root true 0*root false 0)*
      (root false 1*root true 1*root false 1))^7=1)
    (hopposition : ∀neg i,omega*root neg i*omega⁻¹=root (!neg) i)
    (h : selectedGroup root→*G) (f : S→*G)
    (hsource : ∀neg i,h (rootLift root neg i)∈f.range)
    (neg : Bool) : ∃x : commutator S,f x.val=h (rootLift root neg 0) := by
  have hd : Subgroup.closure ((selectedGroup root).subtype ⁻¹'
      Set.range (fun p : Bool×Fin 2=>root p.1 p.2))=⊤ :=
    Subgroup.closure_closure_coe_preimage
  have htop : (⊤ : Subgroup (selectedGroup root))≤f.range.comap h := by
    rw [←hd]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨p,hp⟩
    have he : x=rootLift root p.1 p.2 := Subtype.ext hp.symm
    rw [he]
    exact hsource p.1 p.2
  have hrange : h.range≤f.range := by
    rintro _ ⟨x,rfl⟩
    exact htop (Subgroup.mem_top x)
  have hm := roots_mem_selected_commutator root omega hsquare hthree hseven hopposition neg
  rw [←Subgroup.map_subtype_commutator] at hm
  rcases hm with ⟨y,hy,he⟩
  have hey : y=rootLift root neg 0 := Subtype.ext he
  have hy' : rootLift root neg 0∈commutator (selectedGroup root) := hey ▸ hy
  have hh : h (rootLift root neg 0)∈(commutator (selectedGroup root)).map h :=
    ⟨rootLift root neg 0,hy',rfl⟩
  rw [map_commutator_eq (selectedGroup root) h] at hh
  have hout := (Subgroup.commutator_mono hrange hrange) hh
  rw [←map_commutator_eq S f] at hout
  rcases hout with ⟨x,hx,hfx⟩
  exact ⟨⟨x,hx⟩,hfx⟩

end SymmetricSubgroupAsymptotics.CFSGA2SingerDerivedImageLift
