import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitGenerators
import SymmetricSubgroupAsymptotics.SplitAffineLiteralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages

/-! A four-cycle carrying the nontrivial scalar sign still generates the
ternary permutation coordinates from one delta. The cyclic complement
therefore gives bound one on every quotient of a split literal subgroup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockSignedCyclicSocles

open SemidirectProduct
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)

def blockAction : Block →* Equiv.Perm Block :=
  (TernaryFourBlockMetacyclicModel.blockAction false).comp inl

def scalar : Block →* (ZMod 3)ˣ where
  toFun c := (-1) ^ c.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def linearAction : Block →* (Vector ≃ₗ[ZMod 3] Vector) :=
  TernaryMonomialSemidirect.linearAction blockAction scalar

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model linearAction

theorem representation_generated : RepresentationGeneratedBy
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation linearAction) 1 := by
  apply TernaryMonomialOrbitGenerators.generatedBy_orbitCover blockAction scalar
    (fun _ : Fin 1 ↦ 1)
  intro c
  refine ⟨0, c, ?_⟩
  change c * TernaryFourBlockMetacyclicModel.bitAction false 1 1 = c
  simp

theorem complement_coprime : Nat.Coprime 3 (Nat.card Block) := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem complement_normalGen (K : Subgroup Block) (hK : K.Normal) :
    MarkedC4.normalGen K ≤ 1 := by
  letI := hK
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic K

def lifted (v : Vector) : Fin 3 → Model :=
  ![inl (Multiplicative.ofAdd v),
    inr (Multiplicative.ofAdd (2 : ZMod 4)),
    inr (Multiplicative.ofAdd (1 : ZMod 4))]

theorem complement_mem (v : Vector) (c : Block) :
    (inr c : Model) ∈ Subgroup.closure (Set.range (lifted v)) := by
  have hc : (Multiplicative.ofAdd (1 : ZMod 4)) ^ c.toAdd.val = c := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul]
  rw [← hc, map_pow]
  exact (Subgroup.closure (Set.range (lifted v))).pow_mem
    (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))) _

def literalAction : Model →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action blockAction scalar)

theorem quotientSocle (v : Vector) (target : Fin 3 → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, literalAction (lifted v i) = target i)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 1 :=
  SplitAffineLiteralSocles.quotientSocle linearAction literalAction (lifted v) target
    (Equiv.refl _) hbinding (complement_mem v) complement_coprime 1 1
    representation_generated complement_normalGen N

end TernaryFourBlockSignedCyclicSocles
end SymmetricSubgroupAsymptotics

end
