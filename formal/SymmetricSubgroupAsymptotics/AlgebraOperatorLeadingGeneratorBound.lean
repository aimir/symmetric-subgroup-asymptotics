import SymmetricSubgroupAsymptotics.LeadingTermOrbitAntichains
import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import SymmetricSubgroupAsymptotics.RepresentationLeadingGeneratorBound

/-! Leading-term generation using operators in the acting algebra.

The raising operator may be a difference or a product of differences of
group elements. All cancellations take place in the original module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {n d : ℕ}

theorem algebra_generating_finset_le_of_operator_leading_width
    (hd : ModuleGeneratedBy A M d) (C : M →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (a0 : Fin n)
    (rel : Fin n → Fin n → Prop) (hrefl : ∀ a, rel a a)
    (hraise : ∀ v a b, FiniteRowLeadingWeight.HasLeading (C v) a → rel a b →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b)
    (w : ℕ) (hwidth : ∀ s : Finset (Fin n),
      IsAntichain rel (s : Set (Fin n)) → s.card ≤ w) :
    ∃ S : Finset M, Submodule.span A (S : Set M) = ⊤ ∧ S.card ≤ w := by
  have hex (x : M) (hx : x ≠ 0) :
      ∃ a, FiniteRowLeadingWeight.HasLeading (C x) a :=
    FiniteRowLeadingWeight.exists_leading
      (fun he => hx (hC (he.trans (map_zero C).symm)))
  let label : M → Fin n := fun x => if hx : x ≠ 0 then (hex x hx).choose else a0
  have hlead (x : M) (hx : x ≠ 0) :
      FiniteRowLeadingWeight.HasLeading (C x) (label x) := by
    simpa only [label, dif_pos hx] using (hex x hx).choose_spec
  have hcancel : ∀ x y : M, x ≠ 0 → y ≠ 0 → rel (label x) (label y) →
      (PUnit.unit : PUnit) = PUnit.unit → ∃ r : A,
        FiniteRowLeadingWeight.weight (C (y - r • x)) <
          FiniteRowLeadingWeight.weight (C y) := by
    intro x y hx hy hr _
    obtain ⟨r, hrlead⟩ := hraise x (label x) (label y) (hlead x hx) hr
    let c : k := C y (label y) / C (r • x) (label y)
    have he : c * C (r • x) (label y) = C y (label y) :=
      div_mul_cancel₀ _ hrlead.1
    have hscaled : FiniteRowLeadingWeight.HasLeading
        (c • C (r • x)) (label y) := by
      constructor
      · change c * C (r • x) (label y) ≠ 0
        rw [he]
        exact (hlead y hy).1
      · intro b hb
        change c * C (r • x) b = 0
        rw [hrlead.2 b hb, mul_zero]
    have hdrop := FiniteRowLeadingWeight.cancellation_decreases_weight
      hscaled (hlead y hy) he
    refine ⟨c • r, ?_⟩
    have hact : C ((c • r) • x) = c • C (r • x) := by
      rw [smul_assoc, map_smul]
    rw [map_sub, hact]
    exact hdrop
  obtain ⟨S, hS, hcard⟩ :=
    LeadingTermMinimalGenerators.exists_generating_finset_le_colours_mul_width
      d hd (fun x => FiniteRowLeadingWeight.weight (C x)) rel hrefl label
      (fun _ => PUnit.unit) w hwidth hcancel
  exact ⟨S, hS, by simpa only [Fintype.card_punit, one_mul] using hcard⟩

end SymmetricSubgroupAsymptotics
