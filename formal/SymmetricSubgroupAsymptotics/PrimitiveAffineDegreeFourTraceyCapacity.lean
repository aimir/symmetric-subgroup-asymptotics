import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTraceyLocalImage
import SymmetricSubgroupAsymptotics.OrbitSizeIncidence

/-!
# Exact Tracey capacity for the nonzero degree-four ternary core

This file applies Tracey's literal Theorem 4.24(ii)(b) formula to the
actual soluble subgroup constructed in the preceding modules.  Every one
of its block orbits has size at least two, the actual odd Hall subgroup has
local dual-orbit coefficient one, and the defining `E_sol` inequalities
therefore give `2 e_i <= s_i`.  Summing over the disjoint actual orbits
gives the required half-block generator bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The sum of the literal `E_sol` entries over the actual Tracey-subgroup
orbits costs at most half the displayed block degree. -/
theorem degreeFourTracey_esol_sum_le_half
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points)
    (e : MulAction.orbitRel.Quotient
        (degreeFourTraceySubgroup block P hTraceyPerm hs)
        block.Points → ℕ)
    (he : ∀ o, TraceyBinarySolubleFormulaBounds
      (Nat.card o.orbit) (e o)) :
    (∑ o, e o) ≤ Nat.card block.Points / 2 := by
  have hpoint : ∀ o : MulAction.orbitRel.Quotient
      (degreeFourTraceySubgroup block P hTraceyPerm hs) block.Points,
      2 * e o ≤ Nat.card o.orbit := by
    intro o
    exact traceyBinarySolubleFormulaBounds_two_le
      (degreeFourTracey_orbit_card_two_le block P hTraceyPerm hs o) (he o)
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  calc
    (∑ o, e o) * 2 = ∑ o, 2 * e o := by
      simp only [mul_comm, Finset.mul_sum]
    _ ≤ ∑ o, Nat.card o.orbit :=
      Finset.sum_le_sum (fun o _ ↦ hpoint o)
    _ ≤ Nat.card block.Points := by
      let point :
          (Σ o : MulAction.orbitRel.Quotient
            (degreeFourTraceySubgroup block P hTraceyPerm hs)
            block.Points, o.orbit) → block.Points := fun z ↦ z.2.val
      have hpointInjective : Function.Injective point := by
        rintro ⟨o, x⟩ ⟨p, y⟩ h
        have hxy : (x : block.Points) = (y : block.Points) := h
        have hq := congrArg
          (Quotient.mk (MulAction.orbitRel
            (degreeFourTraceySubgroup block P hTraceyPerm hs)
            block.Points)) hxy
        have hop : o = p :=
          (MulAction.orbitRel.Quotient.mem_orbit.mp x.property).symm.trans
            (hq.trans
              (MulAction.orbitRel.Quotient.mem_orbit.mp y.property))
        subst p
        have hxy' : x = y := Subtype.ext hxy
        subst y
        rfl
      have hcard := Nat.card_le_card_of_injective point hpointInjective
      simpa only [Nat.card_sigma] using hcard

/-- Prime-indexed form of Tracey's binary soluble-orbit statement.  The
index is useful when a concrete elementary chart retains its prime as a
dependent field even after that prime has been proved equal to two. -/
def PrimeTraceySolubleOrbitInducedModuleInput
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G I : Type) [Group G] [Finite G] [Finite I]
    [MulAction G I] [MulAction.IsPretransitive G I]
    (i : I)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V]
    (rho : Representation (ZMod p) (MulAction.stabilizer G i) V)
    (N : Subgroup G) [IsSolvable N]
    (P : Subgroup N), IsTwoComplement P →
    ∀ M : Subrepresentation
      (Representation.ind (MulAction.stabilizer G i).subtype rho),
      ∃ e : MulAction.orbitRel.Quotient N I → ℕ,
        (∀ o : MulAction.orbitRel.Quotient N I,
          TraceyBinarySolubleFormulaBounds (Nat.card o.orbit) (e o)) ∧
        RepresentationGeneratedBy M.toRepresentation
          (min (Module.finrank (ZMod p) V)
              (primeTraceyLocalDualOrbitCount i rho N P) *
            ∑ o : MulAction.orbitRel.Quotient N I, e o)

/-- The prime-indexed statement is exactly the published binary statement
when the retained chart prime is two. -/
theorem primeTraceySolubleOrbitInducedModuleInput_of_eq_two
    {p : ℕ} [Fact p.Prime]
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hp : p = 2) :
    PrimeTraceySolubleOrbitInducedModuleInput p := by
  subst p
  simpa only [PrimeTraceySolubleOrbitInducedModuleInput,
    TraceySolubleOrbitInducedModuleInput,
    primeTraceyLocalDualOrbitCount, traceyLocalDualOrbitCount] using hTracey

/-- Rewrite the published binary Tracey theorem only while the prime is an
explicit binder.  This avoids transporting the actual chart representation
and its dependent scalar-field instances in the degree-four theorem. -/
theorem primeTraceySolubleOrbitInduced_uniform_half
    {p : ℕ} [Fact p.Prime]
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hp : p = 2)
    {G I V : Type} [Group G] [Finite G] [Finite I]
    [MulAction G I] [MulAction.IsPretransitive G I]
    (i : I)
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : Representation (ZMod p) (MulAction.stabilizer G i) V)
    (N : Subgroup G) [IsSolvable N]
    (P₂ : Subgroup N) (hP₂ : IsTwoComplement P₂)
    (hchi : primeTraceyLocalDualOrbitCount i rho N P₂ = 1)
    (hdim : Module.finrank (ZMod p) V = 2)
    (orbitSum_le_half :
      ∀ e : MulAction.orbitRel.Quotient N I → ℕ,
        (∀ o, TraceyBinarySolubleFormulaBounds
          (Nat.card o.orbit) (e o)) →
        (∑ o, e o) ≤ Nat.card I / 2) :
    UniformSubrepresentationGeneratorBound
      (Representation.ind (MulAction.stabilizer G i).subtype rho)
      (Nat.card I / 2) := by
  subst p
  intro M
  obtain ⟨e, he, hgen⟩ := hTracey G I i V rho N P₂ hP₂ M
  have hehalf : (∑ o, e o) ≤ Nat.card I / 2 :=
    orbitSum_le_half e he
  have hchi' : traceyLocalDualOrbitCount i rho N P₂ = 1 := by
    simpa only [primeTraceyLocalDualOrbitCount,
      traceyLocalDualOrbitCount] using hchi
  have hcoefficient :
      min (Module.finrank (ZMod 2) V)
          (traceyLocalDualOrbitCount i rho N P₂) *
          ∑ o, e o = ∑ o, e o := by
    rw [hchi', hdim]
    norm_num
  rw [hcoefficient] at hgen
  exact representationGeneratedBy_mono M.toRepresentation hehalf hgen

/-- Apply the prime-explicit Tracey bound to one concrete subrepresentation
after an injective intertwining transport.  Keeping the transport generic
prevents a consumer from repeatedly elaborating a dependent affine state. -/
theorem primeTraceySolubleOrbitInduced_concrete_generated
    {p : ℕ} [Fact p.Prime]
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hp : p = 2)
    {G I V W : Type} [Group G] [Finite G] [Finite I]
    [MulAction G I] [MulAction.IsPretransitive G I]
    (i : I)
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : Representation (ZMod p) (MulAction.stabilizer G i) V)
    (N : Subgroup G) [IsSolvable N]
    (P₂ : Subgroup N) (hP₂ : IsTwoComplement P₂)
    (hchi : primeTraceyLocalDualOrbitCount i rho N P₂ = 1)
    (hdim : Module.finrank (ZMod p) V = 2)
    (orbitSum_le_half :
      ∀ e : MulAction.orbitRel.Quotient N I → ℕ,
        (∀ o, TraceyBinarySolubleFormulaBounds
          (Nat.card o.orbit) (e o)) →
        (∑ o, e o) ≤ Nat.card I / 2)
    [AddCommGroup W] [Module (ZMod p) W]
    (sigma : Representation (ZMod p) G W)
    (f : sigma.IntertwiningMap
      (Representation.ind (MulAction.stabilizer G i).subtype rho))
    (hf : Function.Injective f)
    (M : Subrepresentation sigma) :
    RepresentationGeneratedBy M.toRepresentation (Nat.card I / 2) := by
  exact (primeTraceySolubleOrbitInduced_uniform_half
    hTracey hp i rho N P₂ hP₂ hchi hdim orbitSum_le_half).of_injective
      f hf M


end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
