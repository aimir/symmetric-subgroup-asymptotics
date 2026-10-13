import SymmetricSubgroupAsymptotics.FiniteNormalRegistryQuotientSocle

/-!
# Uniform quotient-socle certificates from finite normal-state tables

The state registry supplies completeness. Small Boolean tables identify
relative atoms and their least upper bound, and test a padded generator
tuple in each state. The same proof then constructs the socle certificate
for every quotient. In particular, no multiplication table for a quotient
or separate group-theoretic proof for each quotient is required.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
open Non2UnipotentPrefixFiniteMenu

/-- Reducible relative-atom predicate, so finite instances synthesize a
computable decision procedure rather than a classical fallback. -/
abbrev finiteNormalTableMinimal {I : Type} (leTest : I → I → Bool) (i j : I) : Prop :=
  leTest i j = true ∧ leTest j i ≠ true ∧
    ∀ k, (leTest i k = true ∧ leTest k i ≠ true) →
      leTest k j = true → k = j

structure FiniteNormalStateSocleTable {G : Type} [Group G] [Finite G]
    (R : FiniteNormalStateRegistry G) (t : ℕ) where
  leTest : R.State → R.State → Bool
  le_iff : ∀ i j, R.state i ≤ R.state j ↔ leTest i j = true
  carrier : R.State → R.State
  carrier_upper : ∀ i, leTest i (carrier i) = true ∧
    ∀ j, finiteNormalTableMinimal leTest i j → leTest j (carrier i) = true
  carrier_least : ∀ i k, leTest i k = true →
    (∀ j, finiteNormalTableMinimal leTest i j → leTest j k = true) →
      leTest (carrier i) k = true
  generator : R.State → Fin t → G
  generatorIn : R.State → R.State → Bool
  generatorIn_iff : ∀ i k, generatorIn i k = true ↔
    ∀ j, generator i j ∈ R.state k
  generator_mem : ∀ i, generatorIn i (carrier i) = true
  generator_generates : ∀ i k, leTest i k = true → generatorIn i k = true →
    leTest (carrier i) k = true

namespace FiniteNormalStateSocleTable

variable {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
  {R : FiniteNormalStateRegistry G} {t : ℕ} (D : FiniteNormalStateSocleTable R t)

theorem minimal_iff (i j : R.State) :
    R.IsMinimalStateAbove i j ↔ finiteNormalTableMinimal D.leTest i j := by
  constructor
  · rintro ⟨hstrict, hminimal⟩
    refine ⟨(D.le_iff i j).mp hstrict.1, ?_, ?_⟩
    · intro h
      exact hstrict.2 ((D.le_iff j i).mpr h)
    · intro k hk hkj
      apply R.state_injective
      exact hminimal k
        ⟨(D.le_iff i k).mpr hk.1, fun h ↦ hk.2 ((D.le_iff k i).mp h)⟩
        ((D.le_iff k j).mpr hkj)
  · rintro ⟨hforward, hback, hminimal⟩
    refine ⟨⟨(D.le_iff i j).mpr hforward,
      fun h ↦ hback ((D.le_iff j i).mp h)⟩, ?_⟩
    intro k hk hkj
    exact congrArg R.state (hminimal k
      ⟨(D.le_iff i k).mp hk.1, fun h ↦ hk.2 ((D.le_iff k i).mpr h)⟩
      ((D.le_iff k j).mp hkj))

theorem carrier_eq (i : R.State) :
    R.state (D.carrier i) = R.state i ⊔
      ⨆ j : {j : R.State // R.IsMinimalStateAbove i j}, R.state j.1 := by
  let K := R.state i ⊔
    ⨆ j : {j : R.State // R.IsMinimalStateAbove i j}, R.state j.1
  letI : (R.state i).Normal := R.state_normal i
  letI (j : {j : R.State // R.IsMinimalStateAbove i j}) :
      (R.state j.1).Normal := R.state_normal j.1
  letI : (⨆ j : {j : R.State // R.IsMinimalStateAbove i j}, R.state j.1).Normal :=
    ⟨by
      intro x hx g
      refine Subgroup.iSup_induction
        (fun j : {j : R.State // R.IsMinimalStateAbove i j} ↦ R.state j.1)
        (C := fun x ↦ g * x * g⁻¹ ∈
          ⨆ j : {j : R.State // R.IsMinimalStateAbove i j}, R.state j.1) hx ?_ ?_ ?_
      · intro j x hx
        exact Subgroup.mem_iSup_of_mem j ((R.state_normal j.1).conj_mem x hx g)
      · simp
      · intro x y hx hy
        simpa [mul_assoc] using mul_mem hx hy⟩
  letI : K.Normal := by dsimp [K]; infer_instance
  obtain ⟨k, hk⟩ := R.complete K
  change R.state (D.carrier i) = K
  apply le_antisymm
  · rw [← hk]
    apply (D.le_iff _ _).mpr
    apply D.carrier_least
    · apply (D.le_iff _ _).mp
      rw [hk]
      exact le_sup_left
    · intro j hj
      apply (D.le_iff _ _).mp
      rw [hk]
      exact le_sup_of_le_right (le_iSup
        (fun z : {z : R.State // R.IsMinimalStateAbove i z} ↦ R.state z.1)
        ⟨j, (D.minimal_iff i j).mpr hj⟩)
  · apply sup_le
    · exact (D.le_iff _ _).mpr (D.carrier_upper i).1
    · apply iSup_le
      rintro ⟨j, hj⟩
      exact (D.le_iff _ _).mpr ((D.carrier_upper i).2 j ((D.minimal_iff i j).mp hj))

theorem generated (i : R.State) :
    Subgroup.normalClosure (Set.range (D.generator i)) ⊔ R.state i =
      R.state (D.carrier i) := by
  let L := Subgroup.normalClosure (Set.range (D.generator i)) ⊔ R.state i
  letI : (R.state i).Normal := R.state_normal i
  letI : L.Normal := by dsimp [L]; infer_instance
  obtain ⟨k, hk⟩ := R.complete L
  change L = R.state (D.carrier i)
  apply le_antisymm
  · apply sup_le
    · letI := R.state_normal (D.carrier i)
      apply Subgroup.normalClosure_le_normal
      rintro x ⟨j, rfl⟩
      exact (D.generatorIn_iff _ _).mp (D.generator_mem i) j
    · exact (D.le_iff _ _).mpr (D.carrier_upper i).1
  · rw [← hk]
    apply (D.le_iff _ _).mpr
    apply D.generator_generates
    · apply (D.le_iff _ _).mp
      rw [hk]
      exact le_sup_right
    · apply (D.generatorIn_iff _ _).mpr
      intro j
      rw [hk]
      exact Subgroup.mem_sup_left (Subgroup.subset_normalClosure (Set.mem_range_self j))

/-- One construction handles every base state of the complete registry. -/
noncomputable def data (i : R.State) : FiniteRelativeSocleGeneratorData G (R.state i) t :=
  R.relativeSocleGeneratorDataOfStates i (D.carrier i) t
    {j : R.State // R.IsMinimalStateAbove i j} Subtype.val
    (fun j ↦ j.property) (fun j hj ↦ ⟨⟨j, hj⟩, rfl⟩)
    (D.carrier_eq i) (D.generator i) (D.generated i)

noncomputable def family : R.QuotientSocleGeneratorFamily t where
  data := D.data

/-- Transport to a literal action once, then dispatch all its quotient axes. -/
noncomputable def mapFamily (e : G ≃* H) :
    (R.mapEquiv e).QuotientSocleGeneratorFamily t where
  data i := (D.data i).mapEquiv e

end FiniteNormalStateSocleTable
end SymmetricSubgroupAsymptotics

end
