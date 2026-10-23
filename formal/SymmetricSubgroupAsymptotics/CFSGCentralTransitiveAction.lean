import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! Exact orbit counts for a central subgroup on a transitive ACTUAL
group action. Central elements fix either the whole orbit or no point;
all their point stabilizers agree as literal subgroups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGCentralTransitiveAction
open MulAction
variable {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]

theorem central_stabilizer_eq (C : Subgroup G) (hC : C ≤ Subgroup.center G) (x y : X) :
    stabilizer C x = stabilizer C y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  ext c
  have hcomm : g * (c : G) = (c : G) * g :=
    Subgroup.mem_center_iff.mp (hC c.property) g
  have hswap : (c : G) • (g • x) = g • ((c : G) • x) := by
    rw [← mul_smul, ← hcomm, mul_smul]
  change (c : G) • x = x ↔ (c : G) • (g • x) = g • x
  rw [hswap]
  constructor
  · exact congrArg (fun z : X => g • z)
  · intro he
    have hh := congrArg (fun z : X => g⁻¹ • z) he
    simpa only [inv_smul_smul] using hh

theorem central_fixedBy_eq_univ_or_empty (C : Subgroup G)
    (hC : C ≤ Subgroup.center G) (c : C) :
    fixedBy X c = Set.univ ∨ fixedBy X c = ∅ := by
  by_cases hx : ∃ x : X, c • x = x
  · obtain ⟨x, hx⟩ := hx
    left
    apply Set.eq_univ_of_forall
    intro y
    have hc : c ∈ stabilizer C x := hx
    rw [central_stabilizer_eq C hC x y] at hc
    exact hc
  · right
    ext x
    constructor
    · intro hx'
      exact (hx ⟨x, hx'⟩).elim
    · intro hx'
      exact hx'.elim

theorem transitive_card_eq_index [Finite X] (x : X) :
    Nat.card X = (stabilizer G x).index := by
  calc
    Nat.card X = Nat.card (orbit G x) :=
      (Nat.card_congr ((Equiv.setCongr (orbit_eq_univ G x)).trans (Equiv.Set.univ X))).symm
    _ = Nat.card (G ⧸ stabilizer G x) :=
      Nat.card_congr (orbitEquivQuotientStabilizer G x)
    _ = _ := rfl

theorem card_eq_central_orbits_mul_relIndex [Finite G] [Finite X]
    (C : Subgroup G) (hC : C ≤ Subgroup.center G) (x : X) :
    Nat.card X = Nat.card (Quotient (orbitRel C X)) * (stabilizer G x).relIndex C := by
  letI : Fintype (Quotient (orbitRel C X)) := Fintype.ofFinite _
  calc
    Nat.card X = Nat.card (Σ o : Quotient (orbitRel C X), C ⧸ stabilizer C o.out) :=
      Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer C X)
    _ = ∑ o : Quotient (orbitRel C X), Nat.card (C ⧸ stabilizer C o.out) := Nat.card_sigma
    _ = ∑ _o : Quotient (orbitRel C X), (stabilizer C x).index := by
      apply Finset.sum_congr rfl
      intro o _
      rw [central_stabilizer_eq C hC o.out x]
      rfl
    _ = Nat.card (Quotient (orbitRel C X)) * (stabilizer C x).index := by
      simp [Nat.card_eq_fintype_card]
    _ = _ := rfl

end SymmetricSubgroupAsymptotics.CFSGCentralTransitiveAction
