import SymmetricSubgroupAsymptotics.NormalPSubgroupSimpleFixed
import SymmetricSubgroupAsymptotics.RepresentationNormalCoinvariantSchurHead

/-! Rigidity from an irreducible normal-p fixed space.
If the actual fixed space is a simple subrepresentation, it is contained
in every nonzero subrepresentation. Consequently a subrepresentation is
either fixed by P, or its P-commutator contains that same fixed space.
Every map to a P-trivial target then kills the fixed space in the latter
case. This is a module-theoretic statement; it assumes no finite action
catalogue, subgroup splitting or numerical head bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.NormalPMonolithicCommutator

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod p) V]
    (rho : Representation (ZMod p) G V) (P : Subgroup G) [P.Normal]

def fixed : Subrepresentation rho :=
  ⟨Representation.invariants (rho.comp P.subtype),
    Representation.le_comap_invariants rho P⟩

/-- The literal image in V of [E,P], formed before any quotient. -/
def commutator (E : Subrepresentation rho) : Subrepresentation rho where
  toSubmodule :=
    (Representation.Coinvariants.ker (E.toRepresentation.comp P.subtype)).map
      E.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := by
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    apply Submodule.mem_map.mpr
    refine ⟨E.toRepresentation g u,
      Representation.Coinvariants.le_comap_ker E.toRepresentation P g hu, ?_⟩
    rfl

theorem commutator_le (E : Subrepresentation rho) : commutator rho P E ≤ E := by
  intro v hv
  obtain ⟨u, _hu, rfl⟩ := Submodule.mem_map.mp hv
  exact u.2

theorem difference_mem_commutator (E : Subrepresentation rho) (g : P)
    (v : E.toSubmodule) : rho (g : G) v.1 - v.1 ∈ commutator rho P E := by
  apply Submodule.mem_map.mpr
  exact ⟨E.toRepresentation (g : G) v - v,
    Representation.Coinvariants.sub_mem_ker (ρ := E.toRepresentation.comp P.subtype) g v,
    rfl⟩

theorem commutator_eq_bot_iff (E : Subrepresentation rho) :
    commutator rho P E = ⊥ ↔ E ≤ fixed rho P := by
  constructor
  · intro h v hv g
    have hd := difference_mem_commutator rho P E g ⟨v, hv⟩
    rw [h] at hd
    exact sub_eq_zero.mp (show rho (g : G) v - v = 0 from hd)
  · intro h
    have hker : Representation.Coinvariants.ker
        (E.toRepresentation.comp P.subtype) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, v⟩, rfl⟩
      change E.toRepresentation (g : G) v - v = 0
      apply sub_eq_zero.mpr
      apply Subtype.ext
      exact h v.2 g
    apply Subrepresentation.toSubmodule_injective
    change (Representation.Coinvariants.ker
      (E.toRepresentation.comp P.subtype)).map E.toSubmodule.subtype = ⊥
    rw [hker, Submodule.map_bot]

/-- Normality makes the intersection of E with the P-fixed space a
subrepresentation; the p-group fixed-point theorem makes it nonzero. -/
theorem fixed_le_of_ne_bot [Finite V] (hP : IsPGroup p P)
    (hatom : IsAtom (fixed rho P)) (E : Subrepresentation rho) (hE : E ≠ ⊥) :
    fixed rho P ≤ E := by
  have hEsub : E.toSubmodule ≠ ⊥ := by
    intro h
    apply hE
    exact Subrepresentation.toSubmodule_injective h
  obtain ⟨v, hv, hvne⟩ := E.toSubmodule.ne_bot_iff.mp hEsub
  letI : Finite E.toSubmodule := Finite.of_injective
    E.toSubmodule.subtype E.toSubmodule.subtype_injective
  letI : Nontrivial E.toSubmodule := ⟨⟨⟨v, hv⟩, 0, by
    intro h
    exact hvne (congrArg (fun u : E.toSubmodule => (u : V)) h)⟩⟩
  obtain ⟨u, hune, hu⟩ := pGroup_representation_nonzero_fixed hP
    (E.toRepresentation.comp P.subtype)
  have hmeet : E ⊓ fixed rho P ≠ ⊥ := by
    intro h
    have humem : (u : V) ∈ E ⊓ fixed rho P := by
      refine ⟨u.2, ?_⟩
      intro g
      exact congrArg (fun v : E.toSubmodule => (v : V)) (hu g)
    rw [h] at humem
    apply hune
    apply Subtype.ext
    exact humem
  have heq : E ⊓ fixed rho P = fixed rho P :=
    (hatom.le_iff_eq hmeet).mp inf_le_right
  rw [← heq]
  exact inf_le_left

/-- An actual submodule either lies in the simple fixed space, or the
fixed space vanishes in its P-coinvariants. -/
theorem fixed_le_commutator_of_not_le_fixed [Finite V] (hP : IsPGroup p P)
    (hatom : IsAtom (fixed rho P)) (E : Subrepresentation rho)
    (hE : ¬ E ≤ fixed rho P) : fixed rho P ≤ commutator rho P E :=
  fixed_le_of_ne_bot rho P hP hatom (commutator rho P E)
    (fun h => hE ((commutator_eq_bot_iff rho P E).mp h))

/-- This is the precise vanishing used in a middle-layer Hom estimate.
Both the source E and the target action remain the original ones. -/
theorem intertwiner_kills_fixed [Finite V] (hP : IsPGroup p P)
    (hatom : IsAtom (fixed rho P)) (E : Subrepresentation rho)
    (hE : ¬ E ≤ fixed rho P)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (sigma : Representation (ZMod p) G W)
    (hfix : ∀ (g : P) (w : W), sigma g w = w)
    (f : E.toRepresentation.IntertwiningMap sigma)
    (v : V) (hv : v ∈ fixed rho P) :
    f ⟨v, commutator_le rho P E
      (fixed_le_commutator_of_not_le_fixed rho P hP hatom E hE hv)⟩ = 0 := by
  have hc := fixed_le_commutator_of_not_le_fixed rho P hP hatom E hE hv
  obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp hc
  let descended := intertwiningNormalCoinvariantsEquiv
    E.toRepresentation sigma P hfix f
  have hu0 : f u = 0 := by
    change descended
      (Representation.Coinvariants.mk (E.toRepresentation.comp P.subtype) u) = 0
    rw [(Representation.Coinvariants.mk_eq_zero _).mpr hu]
    exact map_zero descended
  have hueq : u = ⟨v, commutator_le rho P E hc⟩ := Subtype.ext heq
  exact hueq ▸ hu0

end SymmetricSubgroupAsymptotics.NormalPMonolithicCommutator

end
