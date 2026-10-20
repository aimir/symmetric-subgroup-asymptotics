import SymmetricSubgroupAsymptotics.CoinducedLeadingOrbitCancellation
import SymmetricSubgroupAsymptotics.LeadingTermOrbitAntichains
import SymmetricSubgroupAsymptotics.TraceySolubleOrbitInducedInput
import SymmetricSubgroupAsymptotics.RepresentationScalarBasisGenerators

/-! The full local orbit coefficient in the actual induced-module
generator argument. This proves the algebraic χ times width bound from
a genuine ordered transversal; no published module bound is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.CoinducedLeadingRows
open FiniteRowLeadingWeight LeadingTermMinimalGenerators

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {n : ℕ}

private theorem rows_injective
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin n, x=h*T a) :
    Function.Injective (rows H rho T) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  obtain ⟨h,hh,a,rfl⟩ := hfactor x
  change f.1 (H.subtype ⟨h,hh⟩*T a)=g.1 (H.subtype ⟨h,hh⟩*T a)
  rw [f.2 ⟨h,hh⟩ (T a),g.2 ⟨h,hh⟩ (T a)]
  exact congrArg (rho ⟨h,hh⟩) (congrFun hfg a)

theorem exists_generating_finset_le_local_orbits_mul_width
    [Finite V] [Nontrivial V]
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G) (a0 : Fin n)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin n, x=h*T a)
    (rel : Fin n → Fin n → Prop) (hrefl : ∀ a, rel a a)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htri : CosetTriangular H T (· < ·) rel)
    (L : Subgroup H) (hL : L.map H.subtype≤H.normalCore)
    (w : ℕ) (hwidth : ∀ s : Finset (Fin n), IsAntichain rel (s : Set (Fin n)) → s.card≤w)
    (M : Subrepresentation (Representation.coind H.subtype rho))
    [FiniteDimensional k M.toSubmodule] :
    ∃ S : Finset M.toRepresentation.asModule,
      Submodule.span k[G] (S : Set M.toRepresentation.asModule)=⊤ ∧
      S.card≤Nat.card (Quotient (representationNonzeroOrbitRel (rho.comp L.subtype)))*w := by
  letI : AddCommGroup M.toSubmodule := Module.addCommMonoidToAddCommGroup k
  let tau := M.toRepresentation
  let W := tau.asModule
  letI : AddCommGroup W := inferInstanceAs (AddCommGroup tau.asModule)
  letI : Module k W := inferInstanceAs (Module k tau.asModule)
  letI : Module k[G] W := inferInstanceAs (Module k[G] tau.asModule)
  let C : W →ₗ[k] (Fin n → V) :=
    (rows H rho T).comp (M.toSubmodule.subtype.comp tau.asModuleEquiv.toLinearMap)
  have hC : Function.Injective C := (rows_injective H rho T hfactor).comp
    (Subtype.val_injective.comp tau.asModuleEquiv.injective)
  have hex (x : W) (hx : x≠0) : ∃ a, HasLeading (C x) a :=
    exists_leading (fun he => hx (hC (he.trans (map_zero C).symm)))
  let label : W → Fin n := fun x => if hx : x≠0 then (hex x hx).choose else a0
  have hlead (x : W) (hx : x≠0) : HasLeading (C x) (label x) := by
    simpa only [label,dif_pos hx] using (hex x hx).choose_spec
  obtain ⟨v0,hv0⟩ := exists_ne (0 : V)
  let coefficient : W → {v : V // v≠0} := fun x =>
    if hx : x≠0 then ⟨C x (label x),(hlead x hx).1⟩ else ⟨v0,hv0⟩
  let O := Quotient (representationNonzeroOrbitRel (rho.comp L.subtype))
  letI : Fintype O := Fintype.ofFinite _
  let colour : W → O := fun x => Quotient.mk _ (coefficient x)
  have hcancel : ∀ x y : W, x≠0 → y≠0 → rel (label x) (label y) →
      colour x=colour y → ∃ r : k[G], weight (C (y-r • x))<weight (C y) := by
    intro x y hx hy hrel hcolour
    have horbit := Quotient.exact hcolour
    obtain ⟨l,hl⟩ := horbit
    have hlocal : rho (l : H) (C x (label x))=C y (label y) := by
      simpa only [coefficient,dif_pos hx,dif_pos hy] using hl
    obtain ⟨g,hg⟩ := same_orbit_cancellation H rho T hfactor rel hunique htri L hL
      (tau.asModuleEquiv x).val (tau.asModuleEquiv y).val
      (label x) (label y) (hlead x hx) (hlead y hy) hrel ⟨l,hlocal⟩
    refine ⟨MonoidAlgebra.of k G g,?_⟩
    have hact : C (MonoidAlgebra.of k G g • x)=
        rows H rho T ((Representation.coind H.subtype rho) g (tau.asModuleEquiv x).val) := by
      change C (MonoidAlgebra.single g (1 : k) • x)=_
      rw [Representation.single_smul,one_smul]
      rfl
    rw [map_sub,hact]
    exact hg
  have hn : ModuleGeneratedBy k[G] W (Module.finrank k M.toSubmodule) := by
    change RepresentationGeneratedBy tau (Module.finrank k M.toSubmodule)
    exact representationGeneratedBy_scalar_finrank
      (k := k) (G := G) (V := M.toSubmodule) tau
  obtain ⟨S,hS,hsize⟩ := exists_generating_finset_le_colours_mul_width
    (Module.finrank k M.toSubmodule) hn (fun x => weight (C x))
    rel hrefl label colour w hwidth hcancel
  refine ⟨S,hS,?_⟩
  simpa only [Nat.card_eq_fintype_card] using hsize

end SymmetricSubgroupAsymptotics.CoinducedLeadingRows
