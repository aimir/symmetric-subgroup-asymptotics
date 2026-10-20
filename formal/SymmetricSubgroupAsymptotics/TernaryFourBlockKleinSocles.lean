import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitGenerators
import SymmetricSubgroupAsymptotics.SplitAffineLiteralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages
import SymmetricSubgroupAsymptotics.DirectProductNormalGenerators
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles

/-! The regular Klein-four action on four ternary blocks, with an optional
sign on its first involution. The two cyclic factors bound every normal
subgroup of the complement, including coupled subgroups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockKleinSocles

open SemidirectProduct
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)

abbrev Bit := TernaryFourBlockMetacyclicModel.Bit
abbrev Complement := Bit × Bit

def blockAction : Complement →* Equiv.Perm Block where
  toFun h :=
    Equiv.mulLeft (Multiplicative.ofAdd
      ((h.1.toAdd.val : ZMod 4) + 2 * (h.2.toAdd.val : ZMod 4))) *
        (TernaryFourBlockMetacyclicModel.bitAction true h.1).toEquiv
  map_one' := by apply Equiv.ext; intro i; revert i; decide +kernel
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro i
    revert g h i
    decide +kernel

def scalar (negate : Bool) : Complement →* (ZMod 3)ˣ :=
  (TernaryFourBlockMetacyclicModel.bitScalar negate).comp (MonoidHom.fst Bit Bit)

def linearAction (negate : Bool) : Complement →* (Vector ≃ₗ[ZMod 3] Vector) :=
  TernaryMonomialSemidirect.linearAction blockAction (scalar negate)

abbrev Model (negate : Bool) := LinearSemidirectCoprimeSocleBounds.Model (linearAction negate)

def orbitElement (i : Block) : Complement :=
  ![(1, 1), (Multiplicative.ofAdd 1, 1),
    (1, Multiplicative.ofAdd 1), (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)] i.toAdd

theorem orbitElement_apply (i : Block) : blockAction (orbitElement i) 1 = i := by
  revert i
  decide +kernel

theorem representation_generated (negate : Bool) : RepresentationGeneratedBy
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction negate)) 1 := by
  apply TernaryMonomialOrbitGenerators.generatedBy_orbitCover blockAction (scalar negate)
    (fun _ : Fin 1 ↦ 1)
  intro i
  exact ⟨0, orbitElement i, orbitElement_apply i⟩

theorem complement_coprime : Nat.Coprime 3 (Nat.card Complement) := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem complement_normalGen (K : Subgroup Complement) (hK : K.Normal) :
    MarkedC4.normalGen K ≤ 2 := by
  letI := hK
  obtain ⟨x, hx⟩ := normal_generating_tuples_prod
    (normal_generating_singletons_of_isCyclic (G := Bit))
    (normal_generating_singletons_of_isCyclic (G := Bit)) K hK
  exact normalGen_le_of_fin_tuple x hx

def lifted (negate : Bool) (v : Vector) : Fin 3 → Model negate :=
  ![inl (Multiplicative.ofAdd v),
    inr (Multiplicative.ofAdd 1, 1), inr (1, Multiplicative.ofAdd 1)]

theorem complement_mem (negate : Bool) (v : Vector) (h : Complement) :
    (inr h : Model negate) ∈ Subgroup.closure (Set.range (lifted negate v)) := by
  let K := Subgroup.closure (Set.range (lifted negate v))
  have hfirst (c : Bit) : (inr (c, 1) : Model negate) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    change ((inr : Complement →* Model negate).comp (MonoidHom.inl Bit Bit)) c ∈ K
    rw [← hc, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 3))) _
  have hsecond (c : Bit) : (inr (1, c) : Model negate) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    change ((inr : Complement →* Model negate).comp (MonoidHom.inr Bit Bit)) c ∈ K
    rw [← hc, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))) _
  have hm := K.mul_mem (hfirst h.1) (hsecond h.2)
  simpa only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using hm

def literalAction (negate : Bool) : Model negate →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action blockAction (scalar negate))

theorem quotientSocle (negate : Bool) (v : Vector)
    (target : Fin 3 → Equiv.Perm (Fin 12)) (index : Equiv.Perm (Fin 3))
    (hbinding : ∀ i, literalAction negate (lifted negate v i) = target (index i))
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 2 :=
  SplitAffineLiteralSocles.quotientSocle (linearAction negate) (literalAction negate)
    (lifted negate v) target index hbinding (complement_mem negate v)
    complement_coprime 1 2 (representation_generated negate) complement_normalGen N

end TernaryFourBlockKleinSocles
end SymmetricSubgroupAsymptotics

end
