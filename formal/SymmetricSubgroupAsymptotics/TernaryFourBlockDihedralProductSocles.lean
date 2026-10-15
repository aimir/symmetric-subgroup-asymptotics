import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitGenerators
import SymmetricSubgroupAsymptotics.SplitAffineLiteralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages
import SymmetricSubgroupAsymptotics.DirectProductNormalGenerators
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles

/-! The dihedral four-block action with an independent global scalar sign.
The complement D8 × C2 has uniform normal-generator bound three; the
ternary translation module is cyclic. Coprime retraction therefore keeps
bound three on every original quotient of a split literal subgroup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockDihedralProductSocles

open SemidirectProduct
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)

abbrev Bit := TernaryFourBlockMetacyclicModel.Bit
abbrev Dihedral := TernaryFourBlockMetacyclicModel.Complement true
abbrev Complement := Dihedral × Bit

def blockAction : Complement →* Equiv.Perm Block :=
  (TernaryFourBlockMetacyclicModel.blockAction true).comp (MonoidHom.fst Dihedral Bit)

def scalar : Complement →* (ZMod 3)ˣ :=
  (TernaryFourBlockMetacyclicModel.bitScalar true).comp (MonoidHom.snd Dihedral Bit)

def linearAction : Complement →* (Vector ≃ₗ[ZMod 3] Vector) :=
  TernaryMonomialSemidirect.linearAction blockAction scalar

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model linearAction

theorem representation_generated : RepresentationGeneratedBy
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation linearAction) 1 := by
  apply TernaryMonomialOrbitGenerators.generatedBy_orbitCover blockAction scalar
    (fun _ : Fin 1 ↦ 1)
  intro c
  refine ⟨0, (inl c, 1), ?_⟩
  change c * TernaryFourBlockMetacyclicModel.bitAction true 1 1 = c
  simp

theorem complement_coprime : Nat.Coprime 3 (Nat.card Complement) := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem complement_normalGen (K : Subgroup Complement) (hK : K.Normal) :
    MarkedC4.normalGen K ≤ 3 := by
  letI := hK
  have hD : ∀ L : Subgroup Dihedral, L.Normal →
      ∃ x : Fin 2 → Dihedral, Subgroup.normalClosure (Set.range x) = L := by
    intro L hL
    letI := hL
    exact exists_normal_generating_tuple_of_normalGen_le L
      (TernaryFourBlockMetacyclicModel.complement_normalGen true L hL)
  obtain ⟨x, hx⟩ := normal_generating_tuples_prod hD
    (normal_generating_singletons_of_isCyclic (G := Bit)) K hK
  exact normalGen_le_of_fin_tuple x hx

def lifted (v : Vector) : Fin 4 → Model :=
  ![inl (Multiplicative.ofAdd v),
    inr (inl (Multiplicative.ofAdd (1 : ZMod 4)), 1),
    inr (inr (Multiplicative.ofAdd (1 : ZMod 2)), 1),
    inr (1, Multiplicative.ofAdd (1 : ZMod 2))]

theorem complement_mem (v : Vector) (h : Complement) :
    (inr h : Model) ∈ Subgroup.closure (Set.range (lifted v)) := by
  let K := Subgroup.closure (Set.range (lifted v))
  let f : Dihedral →* Model := (inr : Complement →* Model).comp (MonoidHom.inl Dihedral Bit)
  have hblock (c : Block) : f (inl c) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 4)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    change (f.comp (inl : Block →* Dihedral)) c ∈ K
    rw [← hc, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4))) _
  have hreflection (c : Bit) : f (inr c) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    change (f.comp (inr : Bit →* Dihedral)) c ∈ K
    rw [← hc, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))) _
  have hdihedral (d : Dihedral) : (inr (d, 1) : Model) ∈ K := by
    change f d ∈ K
    rw [← inl_left_mul_inr_right d, map_mul]
    exact K.mul_mem (hblock d.left) (hreflection d.right)
  have hsign (c : Bit) : (inr (1, c) : Model) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    change ((inr : Complement →* Model).comp (MonoidHom.inr Dihedral Bit)) c ∈ K
    rw [← hc, map_pow]
    exact K.pow_mem (Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))) _
  have hm := K.mul_mem (hdihedral h.1) (hsign h.2)
  simpa only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using hm

def literalAction : Model →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action blockAction scalar)

theorem quotientSocle (v : Vector) (target : Fin 4 → Equiv.Perm (Fin 12))
    (index : Equiv.Perm (Fin 4))
    (hbinding : ∀ i, literalAction (lifted v i) = target (index i))
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 3 :=
  SplitAffineLiteralSocles.quotientSocle linearAction literalAction (lifted v)
    target index hbinding (complement_mem v) complement_coprime 1 3
    representation_generated complement_normalGen N

end TernaryFourBlockDihedralProductSocles
end SymmetricSubgroupAsymptotics

end
