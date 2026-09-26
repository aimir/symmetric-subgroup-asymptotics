import SymmetricSubgroupAsymptotics.PermutationCharacterRankGap
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-! A full local action on an embedded original block supplies a rank gap
for the complete correlated permutation subgroup. The restriction image is
constructed on that block itself; all other points remain in its original
complement. No independent product decomposition of the subgroup is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A literal local block: both local containment and fullness concern
the same embedding and the same complete original subgroup. -/
structure FullPermutationBlock {X Ω : Type}
    (J : Subgroup (Equiv.Perm X)) (U : Subgroup (Equiv.Perm Ω)) where
  embedding : Ω ↪ X
  maps : ∀ j : J, ∃ u : U, ∀ x,
    (j : Equiv.Perm X) (embedding x) = embedding ((u : Equiv.Perm Ω) x)
  full : ∀ u : U, ∃ j : J, ∀ x,
    (j : Equiv.Perm X) (embedding x) = embedding ((u : Equiv.Perm Ω) x)

namespace FullPermutationBlock

open PermutationCharacterRankSplit

variable {X Ω : Type} {J : Subgroup (Equiv.Perm X)}
  {U : Subgroup (Equiv.Perm Ω)} (B : FullPermutationBlock J U)

def originalBlock : SubMulAction J X where
  carrier := Set.range B.embedding
  smul_mem' j _ hx := by
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨u, hu⟩ := B.maps j
    exact ⟨(u : Equiv.Perm Ω) x, (hu x).symm⟩

def chart : Ω ≃ B.originalBlock := Equiv.ofInjective B.embedding B.embedding.injective

@[simp] theorem chart_original (x : Ω) : (B.chart x : X) = B.embedding x := rfl

def localAction : U →* Equiv.Perm B.originalBlock :=
  B.chart.permCongrHom.toMonoidHom.comp U.subtype

theorem localAction_eq_restriction (j : J) (u : U)
    (hu : ∀ x, (j : Equiv.Perm X) (B.embedding x) =
      B.embedding ((u : Equiv.Perm Ω) x)) :
    B.localAction u = restrictionHom B.originalBlock j := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := B.chart.surjective y
  have he : B.localAction u (B.chart x) = B.chart ((u : Equiv.Perm Ω) x) := by
    change B.chart ((u : Equiv.Perm Ω) (B.chart.symm (B.chart x))) = _
    rw [B.chart.symm_apply_apply]
  rw [he]
  apply Subtype.ext
  exact (hu x).symm

/-- The codomain is the image of the original group's restriction,
not an independently chosen copy of the local permutation group. -/
def toRestrictionImage : U →* Image B.originalBlock :=
  B.localAction.codRestrict (Image B.originalBlock) (by
    intro u
    obtain ⟨j, hj⟩ := B.full u
    exact ⟨j, (B.localAction_eq_restriction j u hj).symm⟩)

theorem toRestrictionImage_surjective : Function.Surjective B.toRestrictionImage := by
  intro y
  obtain ⟨j, hj⟩ := y.2
  obtain ⟨u, hu⟩ := B.maps j
  refine ⟨u, Subtype.ext ?_⟩
  exact (B.localAction_eq_restriction j u hu).trans hj

include B in
/-- The local rank loss transfers through an actual onto restriction map
and the faithful original complement. Floors cover both parity cases. -/
theorem rank_add_one_le_half [Finite X] [Finite Ω]
    (hJ : IsPGroup 2 J)
    (hU : Module.finrank (ZMod 2) (PrimeCharacters 2 U) + 1 ≤ Nat.card Ω / 2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 J) + 1 ≤ Nat.card X / 2 := by
  have hi := (primeCharacterInflation 2 B.toRestrictionImage).finrank_le_finrank_of_injective
    (primeCharacterInflation_injective 2 B.toRestrictionImage B.toRestrictionImage_surjective)
  have hc : Nat.card B.originalBlock = Nat.card Ω := (Nat.card_congr B.chart).symm
  apply binary_rank_add_gap_le_half B.originalBlock hJ 1
  rw [hc]
  exact (Nat.add_le_add_right hi 1).trans hU

end FullPermutationBlock

/-- A specified original occurrence in a full physical profile is a full
embedded block. Correlations with every other occurrence remain in J. -/
def OrbitProfileFullOn.fullBlock {ι X : Type} {Ω : ι → Type} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {e : OrbitProfilePoints Ω m ≃ X}
    {J : Subgroup (Equiv.Perm X)} (hJ : OrbitProfileFullOn U e J)
    (i : ι) (j : Fin (m i)) : FullPermutationBlock J (U i) where
  embedding := ⟨fun x => e ⟨i, j, x⟩, by
    intro x y h
    simpa using e.injective h⟩
  maps := fun g => hJ.maps g i j
  full := fun u => hJ.full i j u

end SymmetricSubgroupAsymptotics
