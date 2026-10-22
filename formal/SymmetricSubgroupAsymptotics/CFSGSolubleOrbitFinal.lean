import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitFamilies
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFinal
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! Large-orbit soluble ordinary generation from the proved induced-module
bound, without a primitive composition or normal-generation hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
open MarkedC4 LargeOrbitGeneratorConsequences

theorem exists_orbitWeight_cutoff (rate : ℝ) (hrate : 0 < rate) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ n : ℕ, C ≤ n →
      1280 * orbitWeight n ≤ rate * n := by
  obtain ⟨C, hC, hc⟩ := LargeOrbitGeneratorConsequences.exists_orbitWeight_cutoff
    (rate/10) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro n hn
  have h := hc n hn
  change 128 * orbitWeight n ≤ (rate/10)*n at h
  nlinarith

variable {G X : Type} [Group G] [MulAction G X]

/-- The weighted theorem on the original orbit quotient of an arbitrary
faithful finite soluble point action. -/
theorem original_orbit_generator_bound
    (hTracey : TraceyRefinedInducedModuleInput)
    [Finite G] [Finite X] [FaithfulSMul G X] [IsSolvable G]
    [Fintype (OrbitIndex G X)] :
    (genRank G : ℝ) ≤
      1280 * ∑ o : OrbitIndex G X, orbitWeight (Nat.card o.orbit) := by
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
  have hb := family_generator_bound hTracey G
    (Fintype.card O) Y a ha ht
  have hsum : (∑ i : Fin (Fintype.card O), orbitWeight (Fintype.card (Y i))) =
      ∑ o : O, orbitWeight (Nat.card o.orbit) := by
    apply Fintype.sum_equiv e
    intro i
    simp only [Y, Nat.card_eq_fintype_card]
  rwa [hsum] at hb

/-- The exact RDT Proposition 6.2 interface, proved without the sharp primitive
composition or primitive normal-generation inputs. -/
theorem publishedProposition62_of_refined_induced
    (hTracey : TraceyRefinedInducedModuleInput) :
    MarkedC4.LargeOrbitOrdinaryGeneration.PublishedProposition62 := by
  intro rate hrate
  obtain ⟨C, hC, hcutoff⟩ := exists_orbitWeight_cutoff rate hrate
  refine ⟨C, hC, ?_⟩
  intro X _ H _ hlarge
  let O := OrbitIndex H X
  letI : Fintype O := Fintype.ofFinite O
  letI (o : O) : Nonempty o.orbit :=
    ⟨⟨o.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)⟩⟩
  have hb := original_orbit_generator_bound (G := H) (X := X) hTracey
  have hweight (o : O) : 1280 * orbitWeight (Nat.card o.orbit) ≤
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
    (genRank H : ℝ) ≤ 1280 * ∑ o : O, orbitWeight (Nat.card o.orbit) := hb
    _ = ∑ o : O, 1280 * orbitWeight (Nat.card o.orbit) := by rw [Finset.mul_sum]
    _ ≤ ∑ o : O, rate * (Nat.card o.orbit : ℝ) :=
      Finset.sum_le_sum (fun o _ => hweight o)
    _ = rate * Fintype.card X := by rw [← Finset.mul_sum, hcardR]

/-- Unconditional Proposition 6.2: the refined induced-module bound has
already been proved in the project. -/
theorem publishedProposition62_proved :
    MarkedC4.LargeOrbitOrdinaryGeneration.PublishedProposition62 :=
  publishedProposition62_of_refined_induced traceyRefinedInducedModuleInput_proved

end SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
