import SymmetricSubgroupAsymptotics.PermutationBinaryTrivialSection
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-! Trivial sections of the original, possibly nontransitive binary
permutation module. Restriction to the actual orbit subsets jointly
separates the original subrepresentation. The existing coordinate-head
filtration and the proved transitive Boolean-width theorem bound every
invariant surjective quotient, without embedding that quotient back into
the ambient module. This is the orbit-filtration step of a joint budget;
it does not construct a connecting-map slice or a separator. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

variable {k G X W : Type} [Field k] [Group G] [MulAction G X]
    [AddCommGroup W] [Module k W]

/-- Literal restriction of original functions to one actual orbit. -/
def permutationSubrepresentationOrbitRestriction
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (o : MulAction.orbitRel.Quotient G X) :
    M.toRepresentation.IntertwiningMap (permutationFunctionRepresentation k G o.orbit) where
  toLinearMap := {
    toFun := fun m x => (m : X → k) (x : X)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro m
    funext x
    rfl

theorem permutationSubrepresentationOrbitRestriction_jointly_injective
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Function.Injective (fun m o => permutationSubrepresentationOrbitRestriction M o m) := by
  intro m m' he
  apply Subtype.ext
  funext x
  let o : MulAction.orbitRel.Quotient G X := Quotient.mk'' x
  let x' : o.orbit := ⟨x,MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩
  exact congrFun (congrFun he o) x'

/-- The intrinsic head of every original subrepresentation is bounded
by the sum of the widths of its actual transitive orbit coordinates. -/
theorem twoGroup_permutationSubrepresentationHead_le_orbit_widths
    [Finite G] [Finite X] (hG : IsPGroup 2 G)
    (t : MulAction.orbitRel.Quotient G X → ℕ)
    (hcard : ∀ o : MulAction.orbitRel.Quotient G X, Nat.card o.orbit=2^(t o))
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap
      (Representation.trivial k G k)) ≤ ∑ o, (t o).choose (t o/2) := by
  apply representationHom_finrank_le_coordinates
    (fun o : MulAction.orbitRel.Quotient G X => o.orbit → k)
    M.toRepresentation (fun o => permutationFunctionRepresentation k G o.orbit)
    (Representation.trivial k G k) (fun o => (t o).choose (t o/2)) ?_
    (permutationSubrepresentationOrbitRestriction M)
    (permutationSubrepresentationOrbitRestriction_jointly_injective M)
  intro o S
  let x : o.orbit := ⟨o.nonempty_orbit.choose,o.nonempty_orbit.choose_spec⟩
  exact twoGroup_permutationSubrepresentationHead_le_width hG (t o) (hcard o) x S

/-- An actual trivial quotient of the original preimage, with all original
orbit restrictions retained. No section-head monotonicity is asserted. -/
theorem twoGroup_permutation_trivial_quotient_finrank_le_orbit_widths
    [Finite G] [Finite X] (hG : IsPGroup 2 G)
    (t : MulAction.orbitRel.Quotient G X → ℕ)
    (hcard : ∀ o : MulAction.orbitRel.Quotient G X, Nat.card o.orbit=2^(t o))
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m)=q m) :
    Module.finrank k W ≤ ∑ o, (t o).choose (t o/2) := by
  let q' : M.toRepresentation.Coinvariants →ₗ[k] W :=
    Representation.Coinvariants.lift M.toRepresentation q (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro w
    obtain ⟨m,hm⟩ := hq w
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m,hm⟩
  have hdim := LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans
    (twoGroup_permutationSubrepresentationHead_le_orbit_widths hG t hcard M)

/-- The uniform-orbit specialization used by a character-kernel joint
budget: 2^j original orbits of length 2^a contribute 2^j B_a. Orbit
cardinalities remain exact structural hypotheses, not dimension bounds. -/
theorem twoGroup_permutation_trivial_quotient_finrank_le_uniform_orbits
    [Finite G] [Finite X] (hG : IsPGroup 2 G) (a j : ℕ)
    (horbits : Nat.card (MulAction.orbitRel.Quotient G X)=2^j)
    (hcard : ∀ o : MulAction.orbitRel.Quotient G X, Nat.card o.orbit=2^a)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m)=q m) :
    Module.finrank k W ≤ 2^j*a.choose (a/2) := by
  have hb := twoGroup_permutation_trivial_quotient_finrank_le_orbit_widths hG
    (fun _ => a) hcard M q hq htrivial
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_eq_nat_card,horbits] using hb

end SymmetricSubgroupAsymptotics
