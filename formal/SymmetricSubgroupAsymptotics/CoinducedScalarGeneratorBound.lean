import SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates
import SymmetricSubgroupAsymptotics.RepresentationLeadingGeneratorBound
import SymmetricSubgroupAsymptotics.FibreAntichainWidth

/-! The dimension times width generator bound for every original
coinduced subrepresentation, retaining all original local fibre twists. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {n d : ℕ}

theorem exists_generating_finset_le_dimension_mul_width
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (basis : Module.Basis (Fin d) k V) (a0 : Fin n) (i0 : Fin d)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin n, x=h*T a)
    (rel : Fin n → Fin n → Prop) (hrefl : ∀ a, rel a a)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htri : CosetTriangular H T (· < ·) rel)
    (w : ℕ) (hwidth : ∀ s : Finset (Fin n), IsAntichain rel (s : Set (Fin n)) → s.card≤w)
    (M : Subrepresentation (Representation.coind H.subtype rho))
    [FiniteDimensional k M.toSubmodule] :
    ∃ S : Finset M.toRepresentation.asModule,
      Submodule.span k[G] (S : Set M.toRepresentation.asModule)=⊤ ∧ S.card≤d*w := by
  letI : AddCommGroup M.toSubmodule := Module.addCommMonoidToAddCommGroup k
  have hw (s : Finset (Fin (n*d)))
      (hs : IsAntichain (fullComparable rel) (s : Set (Fin (n*d)))) : s.card≤d*w := by
    have h := fibre_antichain_card_le s
      (fun a => (finProdFinEquiv.symm a).1) (fun a => (finProdFinEquiv.symm a).2) rel w
      (by intro a b hab; exact finProdFinEquiv.symm.injective hab) hwidth (by
        intro a ha b hb hab hf hr
        exact hs ha hb hab ⟨hf,hr⟩)
    simpa only [Fintype.card_fin] using h
  exact representation_generating_finset_le_of_leading_width M.toRepresentation
    (subrepresentationCoordinates H rho T basis M)
    (subrepresentationCoordinates_injective H rho T basis hfactor M) (label a0 i0)
    (fullComparable rel) (fun a => ⟨rfl,hrefl _⟩)
    (subrepresentation_raising H rho T basis hfactor rel hunique htri M) (d*w) hw

end SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates
