import SymmetricSubgroupAsymptotics.PGroupPrimeIndexChain
import SymmetricSubgroupAsymptotics.TransitiveBlockQuotient
import SymmetricSubgroupAsymptotics.BlockKernelClassBound

/-! Eight-point blocks on the original transitive binary action.
A prefix of the actual stabilizer-to-whole-group chain gives relative
index eight. Every literal fibre has eight points and the actual quotient
point set has strictly smaller degree. No catalogue input is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace PrimeIndexSubgroupChain

variable {A : Type*} [Group A] {p : ℕ} [Fact p.Prime]
variable {H L : Subgroup A} (s : PrimeIndexSubgroupChain p H L)

theorem le_at (m : ℕ) (hm : m ≤ s.length) : H ≤ s.subgroup m := by
  revert hm
  induction m with
  | zero => intro _; rw [s.first]
  | succ m ih =>
    intro hm
    exact (ih (by omega)).trans (s.step_le m (by omega))

theorem relIndex_at (m : ℕ) (hm : m ≤ s.length) :
    H.relIndex (s.subgroup m) = p ^ m := by
  revert hm
  induction m with
  | zero => intro _; rw [s.first, Subgroup.relIndex_self, pow_zero]
  | succ m ih =>
    intro hm
    rw [← Subgroup.relIndex_mul_relIndex H (s.subgroup m) (s.subgroup (m + 1))
      (s.le_at m (by omega)) (s.step_le m (by omega)), ih (by omega),
      s.step_index m (by omega), pow_succ]

end PrimeIndexSubgroupChain

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω] (ω₀ : Ω)

/-- An original stabilizer overgroup whose fibre has exactly eight points.
It need not be normal in the whole group. -/
structure BinaryEightPointBlock where
  subgroup : Subgroup A
  contains : MulAction.stabilizer A ω₀ ≤ subgroup
  relative_index : (MulAction.stabilizer A ω₀).relIndex subgroup = 8

theorem binaryEightPointBlock_nonempty [Finite A] [Finite Ω]
    (hA : IsPGroup 2 A) (hdegree : 8 < Nat.card Ω) :
    Nonempty (BinaryEightPointBlock (A := A) ω₀) := by
  obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hA
    (MulAction.stabilizer A ω₀) ⊤ le_top
  have hwhole : Nat.card Ω = 2 ^ s.length := by
    simpa only [Subgroup.relIndex_top_right,
      MulAction.index_stabilizer_of_transitive A ω₀] using s.relIndex
  have hthree : 3 ≤ s.length := by
    by_contra h
    have hpow := Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show s.length ≤ 3 by omega)
    have hsmall : Nat.card Ω ≤ 8 := by simpa only [← hwhole] using hpow
    omega
  exact ⟨{
    subgroup := s.subgroup 3
    contains := s.le_at 3 hthree
    relative_index := by simpa using s.relIndex_at 3 hthree }⟩

namespace BinaryEightPointBlock

variable {ω₀} (D : BinaryEightPointBlock (A := A) ω₀)

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

theorem base_fibre_card : Nat.card (D.Fibre D.base) = 8 := by
  change Nat.card {ω : Ω // originalTransitiveBlockMap ω₀ D.subgroup ω =
    ((1 : A) : A ⧸ D.subgroup)} = 8
  rw [originalTransitiveBlockFibre_card ω₀ D.subgroup D.contains, D.relative_index]

theorem fibre_card (x : D.Points) : Nat.card (D.Fibre x) = 8 := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A D.base x
  rw [← ha, ← Nat.card_congr (D.fibreTransport a D.base)]
  exact D.base_fibre_card

theorem degree_product : 8 * Nat.card D.Points = Nat.card Ω := by
  have h := originalTransitiveBlock_degree_product ω₀ D.subgroup D.contains
  change Nat.card (D.Fibre D.base) * Nat.card D.Points = Nat.card Ω at h
  rwa [D.base_fibre_card] at h

theorem points_card_lt [Finite A] : Nat.card D.Points < Nat.card Ω := by
  have hpos := Nat.card_pos (α := D.Points)
  have hdegree := D.degree_product
  omega

abbrev topMap : A →* Equiv.Perm D.Points := MulAction.toPermHom A D.Points
abbrev Top : Subgroup (Equiv.Perm D.Points) := D.topMap.range

theorem top_isPGroup (hA : IsPGroup 2 A) : IsPGroup 2 D.Top :=
  hA.of_surjective D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective

end BinaryEightPointBlock
end SymmetricSubgroupAsymptotics

end
