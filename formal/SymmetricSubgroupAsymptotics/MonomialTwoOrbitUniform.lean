import SymmetricSubgroupAsymptotics.MonomialCoordinateRestriction
import SymmetricSubgroupAsymptotics.RepresentationUniformJointCoordinates

/-! Two actual nontrivial monomial orbits contribute their separate
cyclic capacities through jointly injective restrictions. The original
invariant subspace need not be a product of its coordinate images. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MonomialTwoOrbitUniform

variable {k G I : Type} [Field k] [Finite k] [Group G] [Finite G]
    [Fintype I] [DecidableEq I] [MulAction G I]
    (rho : Representation k G (I → k))
    (hdelta : ∀ g : G, ∀ i : I, ∃ u : kˣ,
      rho g (Pi.single i 1) = (u : k) • (Pi.single (g • i) 1 : I → k))

include hdelta in
/-- The displayed actual orbits cover the carrier; their coordinate
images may have arbitrary correlations. -/
theorem uniform_of_orbit_cover
    (o₀ o₁ : MulAction.orbitRel.Quotient G I)
    [Nontrivial o₀.orbit] [Nontrivial o₁.orbit]
    (hcover : ∀ i : I, i ∈ o₀.orbit ∨ i ∈ o₁.orbit) :
    UniformSubrepresentationGeneratorBound rho
      (Nat.card o₀.orbit / 2 + Nat.card o₁.orbit / 2) := by
  let j₀ : o₀.orbit → I := Subtype.val
  let j₁ : o₁.orbit → I := Subtype.val
  have hj₀ : ∀ g : G, ∀ y : o₀.orbit, j₀ (g • y) = g • j₀ y :=
    fun _ _ => rfl
  have hj₁ : ∀ g : G, ∀ y : o₁.orbit, j₁ (g • y) = g • j₁ y :=
    fun _ _ => rfl
  let f := MonomialCoordinateRestriction.restriction rho hdelta j₀ hj₀
  let g := MonomialCoordinateRestriction.restriction rho hdelta j₁ hj₁
  apply RepresentationUniformJointCoordinates.uniform_of_jointly_injective f g
  · intro v w h₀ h₁
    funext i
    rcases hcover i with hi | hi
    · exact congrFun h₀ (⟨i,hi⟩ : o₀.orbit)
    · exact congrFun h₁ (⟨i,hi⟩ : o₁.orbit)
  · exact MonomialCoordinateRestriction.uniform rho hdelta j₀ hj₀
  · exact MonomialCoordinateRestriction.uniform rho hdelta j₁ hj₁

include hdelta in
/-- Two equal actual orbits of size at least two suffice for the
half-degree bound. The two-singleton case is deliberately not included. -/
theorem uniform_of_two_equal_orbits
    (htwo : Nat.card (MulAction.orbitRel.Quotient G I) = 2)
    (hsize : ∀ o : MulAction.orbitRel.Quotient G I,
      2 * Nat.card o.orbit = Nat.card I)
    (hdegree : 4 ≤ Nat.card I) :
    UniformSubrepresentationGeneratorBound rho (Nat.card I / 2) := by
  obtain ⟨o₀,o₁,_,hpair⟩ := Nat.card_eq_two_iff.mp htwo
  have hs₀ := hsize o₀
  have hs₁ := hsize o₁
  letI : Nontrivial o₀.orbit := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial o₁.orbit := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hcover : ∀ i : I, i ∈ o₀.orbit ∨ i ∈ o₁.orbit := by
    intro i
    have hi : (Quotient.mk'' i : MulAction.orbitRel.Quotient G I) ∈
        ({o₀,o₁} : Set (MulAction.orbitRel.Quotient G I)) := by
      rw [hpair]
      trivial
    rcases hi with hi | hi
    · exact Or.inl (MulAction.orbitRel.Quotient.mem_orbit.mpr hi)
    · exact Or.inr (MulAction.orbitRel.Quotient.mem_orbit.mpr hi)
  have hu := uniform_of_orbit_cover rho hdelta o₀ o₁ hcover
  have hcost : Nat.card o₀.orbit / 2 + Nat.card o₁.orbit / 2 ≤ Nat.card I / 2 := by
    omega
  intro M
  exact representationGeneratedBy_mono M.toRepresentation hcost (hu M)

end SymmetricSubgroupAsymptotics.MonomialTwoOrbitUniform
