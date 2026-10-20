import SymmetricSubgroupAsymptotics.LeadingTermOrbitAntichains
import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import SymmetricSubgroupAsymptotics.RepresentationLeadingAntichain
import SymmetricSubgroupAsymptotics.RepresentationScalarBasisGenerators

/-! Actual module generators from scalar-coordinate raising. Unlike the
intrinsic-head version, this works for arbitrary finite-dimensional group
representations, without a p-group or semisimplicity assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {n : ℕ}

theorem representation_generating_finset_le_of_leading_width
    (rho : Representation k G V) (C : V →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (a0 : Fin n)
    (rel : Fin n → Fin n → Prop) (hrefl : ∀ a, rel a a)
    (hraise : ∀ v a b, RepresentationLeadingAntichain.HasLeading C v a → rel a b →
      ∃ g : G, RepresentationLeadingAntichain.HasLeading C (rho g v) b)
    (w : ℕ) (hwidth : ∀ s : Finset (Fin n), IsAntichain rel (s : Set (Fin n)) → s.card≤w) :
    ∃ S : Finset rho.asModule, Submodule.span k[G] (S : Set rho.asModule)=⊤ ∧ S.card≤w := by
  let W := rho.asModule
  letI : AddCommGroup W := inferInstanceAs (AddCommGroup rho.asModule)
  letI : Module k W := inferInstanceAs (Module k rho.asModule)
  letI : Module k[G] W := inferInstanceAs (Module k[G] rho.asModule)
  let E : W →ₗ[k] (Fin n → k) := C.comp rho.asModuleEquiv.toLinearMap
  have hE : Function.Injective E := hC.comp rho.asModuleEquiv.injective
  have hex (x : W) (hx : x≠0) : ∃ a, FiniteRowLeadingWeight.HasLeading (E x) a :=
    FiniteRowLeadingWeight.exists_leading (fun he => hx (hE (he.trans (map_zero E).symm)))
  let label : W → Fin n := fun x => if hx : x≠0 then (hex x hx).choose else a0
  have hlead (x : W) (hx : x≠0) : FiniteRowLeadingWeight.HasLeading (E x) (label x) := by
    simpa only [label,dif_pos hx] using (hex x hx).choose_spec
  have hcancel : ∀ x y : W, x≠0 → y≠0 → rel (label x) (label y) →
      (PUnit.unit : PUnit)=PUnit.unit → ∃ r : k[G],
        FiniteRowLeadingWeight.weight (E (y-r • x))<FiniteRowLeadingWeight.weight (E y) := by
    intro x y hx hy hr _
    obtain ⟨g,hg⟩ := hraise (rho.asModuleEquiv x) (label x) (label y) (hlead x hx) hr
    let c : k := E y (label y)/C (rho g (rho.asModuleEquiv x)) (label y)
    have he : c*C (rho g (rho.asModuleEquiv x)) (label y)=E y (label y) :=
      div_mul_cancel₀ _ hg.1
    have hscaled : FiniteRowLeadingWeight.HasLeading
        (c • C (rho g (rho.asModuleEquiv x))) (label y) := by
      constructor
      · change c*C (rho g (rho.asModuleEquiv x)) (label y)≠0
        rw [he]
        exact (hlead y hy).1
      · intro b hb
        change c*C (rho g (rho.asModuleEquiv x)) b=0
        rw [hg.2 b hb,mul_zero]
    have hdrop := FiniteRowLeadingWeight.cancellation_decreases_weight
      hscaled (hlead y hy) he
    refine ⟨MonoidAlgebra.single g c,?_⟩
    have hact : E (MonoidAlgebra.single g c • x)=c • C (rho g (rho.asModuleEquiv x)) := by
      rw [Representation.single_smul]
      exact C.map_smul c _
    rw [map_sub,hact]
    exact hdrop
  have hn : ModuleGeneratedBy k[G] W (Module.finrank k V) := by
    change RepresentationGeneratedBy rho (Module.finrank k V)
    exact representationGeneratedBy_scalar_finrank rho
  obtain ⟨S,hS,hcard⟩ := LeadingTermMinimalGenerators.exists_generating_finset_le_colours_mul_width
    (Module.finrank k V) hn (fun x => FiniteRowLeadingWeight.weight (E x))
    rel hrefl label (fun _ => PUnit.unit) w hwidth hcancel
  exact ⟨S,hS,by simpa only [Fintype.card_punit,one_mul] using hcard⟩

end SymmetricSubgroupAsymptotics
