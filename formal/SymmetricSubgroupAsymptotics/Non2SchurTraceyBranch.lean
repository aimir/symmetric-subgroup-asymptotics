import SymmetricSubgroupAsymptotics.Non2SchurPermutationBranch
import SymmetricSubgroupAsymptotics.TraceyBinaryOrbitInput
import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection

/-!
# Installing the binary transitive-module input in a Schur row

For a faithful transitive original action, a nontrivial normal row kernel has
no singleton orbit.  The visible binary Tracey input and the arbitrary orbit
filtration therefore prove the entire nonfaithful half-capacity branch.  In
the degree-two scalar row, only the concrete lower bound eight on the same
kernel orbits remains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {B X A : Type} [Group B] [Finite B] [Finite X] [MulAction B X]
    [FaithfulSMul B X] [MulAction.IsPretransitive B X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- After installing the visible transitive-module input, the four-way row
assignment needs only the global fixed bound, the scalar orbit lower bound,
and the two faithful-image facts. -/
theorem Non2SchurStructuralBranch.of_Tracey_orbit_caps
    (hTracey : TraceyBinaryOrbitInput)
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : M.toRepresentation.IntertwiningMap sigma)
    (hqmap : Function.Surjective qmap)
    (ht : 32 * Module.finrank (ZMod 2) sigma.invariants ≤
      11 * Nat.card X)
    (hscalarOrbit : schurSimpleActionKernel sigma S ≠ ⊥ →
      schurSimpleProductDegree sigma S = 2 →
      ∀ o : MulAction.orbitRel.Quotient
        (schurSimpleActionKernel sigma S) X,
        8 ≤ Nat.card o.orbit)
    (hfaithfulClass : schurSimpleActionKernel sigma S = ⊥ →
      schurSimpleProductDegree sigma S = 8 ∨
        9 ≤ schurSimpleProductDegree sigma S)
    (hfaithfulSmallFixed : schurSimpleActionKernel sigma S = ⊥ →
      schurSimpleProductDegree sigma S = 8 →
      5 * Module.finrank (ZMod 2) sigma.invariants ≤ Nat.card X) :
    Non2SchurStructuralBranch sigma S (Nat.card X)
      (Module.finrank (ZMod 2) sigma.invariants) := by
  let K := schurSimpleActionKernel sigma S
  let cap : MulAction.orbitRel.Quotient K X → ℕ :=
    fun o => traceyBinaryOrbitCap (Nat.card o.orbit)
  apply Non2SchurStructuralBranch.of_permutationSection_orbit_caps
    sigma S hnonfixed M qmap hqmap ht cap
  · intro o T
    exact traceyBinaryOrbit_head_le hTracey K X o T
  · intro hK o
    have hne1 : Nat.card o.orbit ≠ 1 := by
      rw [normal_orbit_card_eq K x o]
      exact normal_orbit_card_ne_one_of_ne_bot K hK x
    letI : Nonempty o.orbit :=
      ⟨⟨o.nonempty_orbit.choose, o.nonempty_orbit.choose_spec⟩⟩
    have hpos : 0 < Nat.card o.orbit := Nat.card_pos
    exact traceyBinaryOrbitCap_twice_le _ (by omega)
  · intro hK hq o
    exact traceyBinaryOrbitCap_eight_le_three_mul _
      (hscalarOrbit hK hq o)
  · exact hfaithfulClass
  · exact hfaithfulSmallFixed

end SymmetricSubgroupAsymptotics

end
