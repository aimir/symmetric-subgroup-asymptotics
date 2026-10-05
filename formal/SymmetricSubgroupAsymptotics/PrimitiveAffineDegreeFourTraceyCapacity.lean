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
      have hsum :
          (∑ o : OrbitSizeIncidence.Selected
            (G := degreeFourTraceySubgroup block P hTraceyPerm hs)
            (X := block.Points) (fun _ ↦ True),
              Nat.card o.val.orbit) ≤ Nat.card block.Points :=
        OrbitSizeIncidence.sum_orbit_card_le
        (G := degreeFourTraceySubgroup block P hTraceyPerm hs)
        (X := block.Points) (fun _ ↦ True)
      simpa [OrbitSizeIncidence.Selected] using hsum

/-- Rewrite the published binary Tracey theorem only while the prime is an
explicit binder.  This avoids transporting the actual chart representation
and its dependent scalar-field instances in the degree-four theorem. -/
private theorem primeTraceySolubleOrbitInduced_uniform_half
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

set_option maxHeartbeats 800000 in
/-- Tracey's exact soluble-orbit formula gives the sharp uniform generator
bound for the actual induced binary-plane representation. -/
theorem degreeFourTranslationInduced_uniform_half
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.inducedRepresentation
        S (localMap block P) C i)
      (Nat.card block.Points / 2) := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  letI : IsSolvable N :=
    degreeFourTraceySubgroup_isSolvable block P hTraceyPerm hr hs
  obtain ⟨P₂, hP₂, hHall⟩ :=
    exists_degreeFourTraceyTwoComplement block P hTraceyPerm hr hs
  have hp : C.p = 2 := by
    simpa only [C, localTranslationChart] using
      degreeFour_profilePrime_eq_two block P hr
  have hdim : Module.finrank (ZMod C.p) C.V = 2 := by
    let C0 := chart block P
    letI : Finite C0.V := Finite.of_injective
      (fun v : C0.V ↦ C0.equiv.symm (Multiplicative.ofAdd v))
      C0.equiv.symm.injective
    have hdegree : 4 = P.p ^ C0.d := by
      rw [← hr]
      simpa [PrimitiveAffineProfile.ElementaryChart.d] using
        P.degree_eq_prime_pow_finrank C0.equiv (origin block)
    have hd0 : C0.d = 2 :=
      (prime_pow_positive_injective (d := C0.d) (e := 2)
        P.p_prime Nat.prime_two C0.d_pos (by norm_num)
        (hdegree.symm.trans (by norm_num))).2
    simpa only [C, C0, localTranslationChart,
      PrimitiveAffineProfile.ElementaryChart.d] using hd0
  have hchi : primeTraceyLocalDualOrbitCount i
      (ActualWreathAffineCapacity.localRepresentation
        S (localMap block P) C i) N P₂ = 1 :=
    degreeFourTraceyLocalDualOrbitCount_eq_one
      block P hTraceyPerm hr hs hD P₂ hP₂ hHall i
  exact primeTraceySolubleOrbitInduced_uniform_half
    hTracey hp i
    (ActualWreathAffineCapacity.localRepresentation
      S (localMap block P) C i) N P₂ hP₂ hchi hdim
    (degreeFourTracey_esol_sum_le_half block P hTraceyPerm hs)

/-- Transport through the actual injective orbit-evaluation intertwiner
places the same half-block bound on the correlated ambient translation
module. -/
theorem degreeFourTranslationAmbient_uniform_half
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) :
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation
        (initialState hTraceyPerm block) (localMap block P)
        (localTranslationChart block P))
      (Nat.card block.Points / 2) := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  have hinduced := degreeFourTranslationInduced_uniform_half
    block P hTracey hTraceyPerm hr hs hD i
  exact hinduced.of_injective
    (ActualWreathAffineCapacity.inducedIntertwiner S
      (localMap block P) C i)
    (ActualWreathAffineCapacity.inducedIntertwiner_injective S
      (localMap block P) C i)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
