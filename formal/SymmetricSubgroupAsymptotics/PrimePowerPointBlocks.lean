import SymmetricSubgroupAsymptotics.BinaryEightPointBlocks

/-! Arbitrary prime-power block sizes on an original faithful transitive
p-group action. This specializes to the16,32,64 binary blocks and the9-point
ternary blocks used by the class-count recurrence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω] (ω₀ : Ω)
variable (p e : ℕ)

/-- An original stabilizer overgroup whose fibre has exactly the specified prime-power number of points.
It need not be normal in the whole group. -/
structure PrimePowerPointBlock where
  subgroup : Subgroup A
  contains : MulAction.stabilizer A ω₀ ≤ subgroup
  relative_index : (MulAction.stabilizer A ω₀).relIndex subgroup = p ^ e

theorem primePowerPointBlock_nonempty [Fact p.Prime] [Finite A] [Finite Ω]
    (hA : IsPGroup p A) (hdegree : p ^ e < Nat.card Ω) :
    Nonempty (PrimePowerPointBlock (A := A) ω₀ p e) := by
  obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hA
    (MulAction.stabilizer A ω₀) ⊤ le_top
  have hwhole : Nat.card Ω = p ^ s.length := by
    simpa only [Subgroup.relIndex_top_right,
      MulAction.index_stabilizer_of_transitive A ω₀] using s.relIndex
  have he : e ≤ s.length := by
    by_contra h
    have hpow := Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (show s.length ≤ e by omega)
    have hsmall : Nat.card Ω ≤ p ^ e := by simpa only [← hwhole] using hpow
    omega
  exact ⟨{
    subgroup := s.subgroup e
    contains := s.le_at e he
    relative_index := by simpa using s.relIndex_at e he }⟩

namespace PrimePowerPointBlock

variable {ω₀ p e} (D : PrimePowerPointBlock (A := A) ω₀ p e)

abbrev Points : Type := A ⧸ D.subgroup
abbrev base : D.Points := ((1 : A) : A ⧸ D.subgroup)

def map : Ω → D.Points := originalTransitiveBlockMap ω₀ D.subgroup

theorem map_equivariant (a : A) (ω : Ω) : D.map (a • ω) = a • D.map ω :=
  originalTransitiveBlockMap_equivariant ω₀ D.subgroup D.contains a ω

theorem map_surjective : Function.Surjective D.map :=
  originalTransitiveBlockMap_surjective ω₀ D.subgroup D.contains

abbrev Fibre (x : D.Points) : Type := originalBlockFibre D.map x

def fibreTransport (a : A) (x : D.Points) : D.Fibre x ≃ D.Fibre (a • x) where
  toFun ω := ⟨a • ω.1, by rw [D.map_equivariant, ω.2]⟩
  invFun ω := ⟨a⁻¹ • ω.1, by rw [D.map_equivariant, ω.2, inv_smul_smul]⟩
  left_inv ω := Subtype.ext (inv_smul_smul a ω.1)
  right_inv ω := Subtype.ext (smul_inv_smul a ω.1)

theorem base_fibre_card : Nat.card (D.Fibre D.base) = p ^ e := by
  change Nat.card {ω : Ω // originalTransitiveBlockMap ω₀ D.subgroup ω =
    ((1 : A) : A ⧸ D.subgroup)} = p ^ e
  rw [originalTransitiveBlockFibre_card ω₀ D.subgroup D.contains, D.relative_index]

theorem fibre_card (x : D.Points) : Nat.card (D.Fibre x) = p ^ e := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A D.base x
  rw [← ha, ← Nat.card_congr (D.fibreTransport a D.base)]
  exact D.base_fibre_card

theorem degree_product : p ^ e * Nat.card D.Points = Nat.card Ω := by
  have h := originalTransitiveBlock_degree_product ω₀ D.subgroup D.contains
  change Nat.card (D.Fibre D.base) * Nat.card D.Points = Nat.card Ω at h
  rwa [D.base_fibre_card] at h

theorem points_card_lt [Fact p.Prime] [Finite A] (he : 0 < e) : Nat.card D.Points < Nat.card Ω := by
  have hpos := Nat.card_pos (α := D.Points)
  have hdegree := D.degree_product
  have hpe : 1 < p ^ e := one_lt_pow₀ (Fact.out : p.Prime).one_lt he.ne'
  nlinarith

abbrev topMap : A →* Equiv.Perm D.Points := MulAction.toPermHom A D.Points
abbrev Top : Subgroup (Equiv.Perm D.Points) := D.topMap.range

theorem class_card_le_local_mul_top [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (hA : IsPGroup p A) (c : ℕ)
    (hc : ∀ x (L : Subgroup (Equiv.Perm (D.Fibre x))),
      IsPGroup p L → Nat.card (ConjClasses L) ≤ c) :
    Nat.card (ConjClasses A) ≤ c ^ Nat.card D.Points * Nat.card (ConjClasses D.Top) :=
  OriginalBlockClassBound.class_card_le_power_mul_top D.map D.map_equivariant p hA c hc

theorem top_isPGroup (hA : IsPGroup p A) : IsPGroup p D.Top :=
  hA.of_surjective D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective

end PrimePowerPointBlock
end SymmetricSubgroupAsymptotics
