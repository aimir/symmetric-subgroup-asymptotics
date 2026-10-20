import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFamilies
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesCutoff
import SymmetricSubgroupAsymptotics.MarkedC4LargeOrbitOrdinaryGeneration

/-! The large-orbit ordinary generator interface follows from the retained
primitive normal-generator, primitive composition-length, and refined
Tracey induced-module inputs.  Every orbit is the original point orbit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
open MarkedC4

abbrev OrbitIndex (G X : Type) [Group G] [MulAction G X] :=
  MulAction.orbitRel.Quotient G X

variable {G X : Type} [Group G] [MulAction G X]

def orbitHom : G →* ∀ o : OrbitIndex G X, Equiv.Perm o.orbit where
  toFun g o := MulAction.toPermHom G o.orbit g
  map_one' := by funext o; exact map_one (MulAction.toPermHom G o.orbit)
  map_mul' g h := by funext o; exact map_mul (MulAction.toPermHom G o.orbit) g h

theorem orbitHom_injective [FaithfulSMul G X] :
    Function.Injective (orbitHom (G := G) (X := X)) := by
  intro g h he
  apply eq_of_smul_eq_smul (α := X)
  intro x
  let o : OrbitIndex G X := Quotient.mk'' x
  let v : o.orbit := ⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩
  exact congrArg
    (fun z : ∀ o : OrbitIndex G X, Equiv.Perm o.orbit => (z o v).val) he

/-- The weighted theorem on the original orbit quotient of an arbitrary
faithful finite soluble point action. -/
theorem original_orbit_generator_bound
    (hgen : PrimitiveNormalGeneratorInput)
    (hTracey : TraceyRefinedInducedModuleInput)
    (hcomp : PrimitiveCompositionLengthInput)
    [Finite G] [Finite X] [FaithfulSMul G X] [IsSolvable G]
    [Fintype (OrbitIndex G X)] :
    (genRank G : ℝ) ≤
      128 * ∑ o : OrbitIndex G X, orbitWeight (Nat.card o.orbit) := by
  let O := OrbitIndex G X
  let e : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  let Y : Fin (Fintype.card O) → Type := fun i => (e i).orbit
  letI (o : O) : Nonempty o.orbit :=
    ⟨⟨o.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)⟩⟩
  let a : G →* ∀ i, Equiv.Perm (Y i) :=
    { toFun := fun g i => MulAction.toPermHom G (Y i) g
      map_one' := by funext i; exact map_one (MulAction.toPermHom G (Y i))
      map_mul' := by intro g h; funext i; exact map_mul (MulAction.toPermHom G (Y i)) g h }
  have ha : Function.Injective a := by
    intro g h hgh
    apply orbitHom_injective (G := G) (X := X)
    funext o
    obtain ⟨i, rfl⟩ := e.surjective o
    change (MulAction.toPermHom G (Y i)) g = (MulAction.toPermHom G (Y i)) h
    exact congrFun hgh i
  have ht : ∀ i, letI : MulAction G (Y i) :=
      MulAction.compHom (Y i) ((Pi.evalMonoidHom _ i).comp a)
      MulAction.IsPretransitive G (Y i) := by
    intro i
    exact (inferInstance : MulAction.IsPretransitive G ((e i).orbit))
  have hb := family_generator_bound hgen hTracey hcomp G
    (Fintype.card O) Y a ha ht
  have hsum : (∑ i : Fin (Fintype.card O), orbitWeight (Fintype.card (Y i))) =
      ∑ o : O, orbitWeight (Nat.card o.orbit) := by
    apply Fintype.sum_equiv e
    intro i
    simp only [Y, Nat.card_eq_fintype_card]
  rwa [hsum] at hb

/-- The exact RDT Proposition 6.2 interface, proved from stronger published
inputs already retained at the final boundary. -/
theorem publishedProposition62_of_retained_inputs
    (hgen : PrimitiveNormalGeneratorInput)
    (hTracey : TraceyRefinedInducedModuleInput)
    (hcomp : PrimitiveCompositionLengthInput) :
    MarkedC4.LargeOrbitOrdinaryGeneration.PublishedProposition62 := by
  intro rate hrate
  obtain ⟨C, hC, hcutoff⟩ := exists_orbitWeight_cutoff rate hrate
  refine ⟨C, hC, ?_⟩
  intro X _ H _ hlarge
  let O := OrbitIndex H X
  letI : Fintype O := Fintype.ofFinite O
  letI (o : O) : Nonempty o.orbit :=
    ⟨⟨o.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)⟩⟩
  have hb := original_orbit_generator_bound (G := H) (X := X) hgen hTracey hcomp
  have hweight (o : O) : 128 * orbitWeight (Nat.card o.orbit) ≤
      rate * Nat.card o.orbit := by
    have hn : 0 < Nat.card o.orbit := Nat.card_pos
    by_cases hsingle : Nat.card o.orbit = 1
    · simp only [hsingle, orbitWeight_one, mul_zero, Nat.cast_one, mul_one]
      exact le_of_lt hrate
    · have hc : Nat.card o.orbit = Nat.card (MulAction.orbit H o.out) :=
        congrArg (fun s : Set X => Nat.card s)
          (MulAction.orbitRel.Quotient.orbit_eq_orbit_out o Quotient.out_eq')
      have hnontrivial : 1 < Nat.card (MulAction.orbit H o.out) := by rw [← hc]; omega
      have hbound := hlarge o.out hnontrivial
      rw [← hc] at hbound
      exact hcutoff _ hbound
  have hcard : (∑ o : O, Nat.card o.orbit) = Fintype.card X := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' H X)).symm
  have hcardR : (∑ o : O, (Nat.card o.orbit : ℝ)) = Fintype.card X := by
    exact_mod_cast hcard
  calc
    (genRank H : ℝ) ≤ 128 * ∑ o : O, orbitWeight (Nat.card o.orbit) := hb
    _ = ∑ o : O, 128 * orbitWeight (Nat.card o.orbit) := by rw [Finset.mul_sum]
    _ ≤ ∑ o : O, rate * (Nat.card o.orbit : ℝ) :=
      Finset.sum_le_sum (fun o _ => hweight o)
    _ = rate * Fintype.card X := by rw [← Finset.mul_sum, hcardR]

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
