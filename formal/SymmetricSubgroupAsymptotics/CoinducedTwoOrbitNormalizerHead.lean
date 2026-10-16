import SymmetricSubgroupAsymptotics.OddNormalizerSubrepresentationHead
import Mathlib.RepresentationTheory.Coinduced

/-! A small double-orbit certificate for an actual coinduced frame.
An odd inducing subgroup H kills the identity fibre. If H and one
normalizing element cover all other right cosets from one representative,
evaluation at that representative injects their simultaneous fixed space
into the original local representation. No invariant-submodule census or
replacement of the inducing subgroup is involved. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CoinducedTwoOrbitNormalizerHead

variable {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (H : Subgroup G) (rho : Representation k H V) (g c : G)

/-- Four displayed double-coset shapes suffice. The two occurrences of H
are the original inducing subgroup. -/
def Cover : Prop := ∀ x : G, ∃ (h a : H) (i j : Fin 2),
  x = (h : G) * (if i = 0 then 1 else c) * (a : G) * (if j = 0 then 1 else g)

abbrev Sigma := Representation.coind H.subtype rho

def evaluation : oddNormalizerFixedSpace (Sigma H rho) H g →ₗ[k] V where
  toFun v := v.1.1 c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fixed_value_identity_eq_zero (hz : Representation.invariants rho = ⊥)
    (v : oddNormalizerFixedSpace (Sigma H rho) H g) : v.1.1 1 = 0 := by
  have hv : v.1.1 1 ∈ Representation.invariants rho := by
    intro a
    have hleft := v.1.2 a 1
    have hright := congrArg
      (fun w : Representation.coindV H.subtype rho => w.1 1) (v.2.1 a)
    change v.1.1 (1 * (a : G)) = v.1.1 1 at hright
    change v.1.1 ((a : G) * 1) = rho a (v.1.1 1) at hleft
    simp only [mul_one] at hleft
    simp only [one_mul] at hright
    exact hleft.symm.trans hright
  rw [hz] at hv
  exact hv

include c in
theorem evaluation_injective (hz : Representation.invariants rho = ⊥)
    (hcover : Cover H g c) : Function.Injective (evaluation H rho g c) := by
  have hk : LinearMap.ker (evaluation H rho g c) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hc : v.1.1 c = 0 := hv
    have hidentity := fixed_value_identity_eq_zero H rho g hz v
    have hright (z : G) (a : H) : v.1.1 (z * (a : G)) = v.1.1 z := by
      exact congrArg (fun w : Representation.coindV H.subtype rho => w.1 z) (v.2.1 a)
    have hrightg (z : G) : v.1.1 (z * g) = v.1.1 z := by
      exact congrArg (fun w : Representation.coindV H.subtype rho => w.1 z)
        ((mem_representationElementFixedSpace _ _ _).mp v.2.2)
    have hleft0 (h : H) : v.1.1 (h : G) = 0 := by
      have hh := v.1.2 h 1
      change v.1.1 ((h : G) * 1) = rho h (v.1.1 1) at hh
      simpa only [mul_one, hidentity, map_zero] using hh
    have hleftc (h : H) : v.1.1 ((h : G) * c) = 0 := by
      have hh := v.1.2 h c
      change v.1.1 ((h : G) * c) = rho h (v.1.1 c) at hh
      simpa only [hc, map_zero] using hh
    apply Subtype.ext
    apply Subtype.ext
    funext x
    obtain ⟨h, a, i, j, rfl⟩ := hcover x
    fin_cases i <;> fin_cases j <;>
      simp [hrightg, hright, hleft0, hleftc]
  intro v w hvw
  have hsub : v - w ∈ LinearMap.ker (evaluation H rho g c) := by
    change evaluation H rho g c (v - w) = 0
    calc
      evaluation H rho g c (v - w) =
          evaluation H rho g c v - evaluation H rho g c w :=
        (evaluation H rho g c).map_sub v w
      _ = 0 := sub_eq_zero.mpr hvw
  rw [hk] at hsub
  exact sub_eq_zero.mp (show v - w = 0 from hsub)

private theorem head_le_normalizer_fixed
    {W : Type} [AddCommGroup W] [Module k W]
    [Finite G] [FiniteDimensional k W]
    (sigma : Representation k G W)
    (hodd : IsUnit (Nat.card H : k))
    (hg : g ∈ Subgroup.normalizer (H : Set G))
    (B : Subrepresentation sigma) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (oddNormalizerFixedSpace sigma H g) :=
  (representationHead_finrank_eq_coinvariants B.toRepresentation).le.trans
    (subrepresentation_coinvariants_le_oddNormalizerFixedSpace
      (ρ := sigma) hodd hg B)

set_option maxHeartbeats 800000 in
theorem subrepresentation_head_le_local_dimension [Finite G] [FiniteDimensional k V]
    (hodd : IsUnit (Nat.card H : k))
    (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hz : Representation.invariants rho = ⊥) (hcover : Cover H g c)
    (B : Subrepresentation (Sigma H rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional k (Representation.coindV H.subtype rho) :=
    FiniteDimensional.of_injective
      (Representation.coindV H.subtype rho).subtype
      (Representation.coindV H.subtype rho).subtype_injective
  exact (head_le_normalizer_fixed H g (Sigma H rho) hodd hg B).trans
      ((evaluation H rho g c).finrank_le_finrank_of_injective
        (evaluation_injective H rho g c hz hcover))

end SymmetricSubgroupAsymptotics.CoinducedTwoOrbitNormalizerHead

end
