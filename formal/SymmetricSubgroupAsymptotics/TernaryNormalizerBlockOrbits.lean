import SymmetricSubgroupAsymptotics.EquivariantOrbitFibreCard
import SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount
import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices

/-! If a ternary subgroup fixes the block set and an additional element
moves every block, each orbit that contains a moving ternary point costs
at least six original points. This uses the actual block map and subgroup
orbits, without assuming that the block kernel is a full direct product. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryNormalizerBlockOrbits

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G X I : Type} [Group G] [MulAction G X] [Finite X]
    [MulAction G I] [Finite I]

theorem six_le_orbit (b : X → I)
    (hb : ∀ (a : G) (x : X), b (a • x) = a • b x)
    (P A : Subgroup G) (hP : IsPGroup 3 P) (hPA : P ≤ A)
    (hfix : ∀ (p : P) (i : I), (p : G) • i = i)
    (g : A) (hmove : ∀ i : I, (g : G) • i ≠ i)
    (x : X) (hx : x ∉ MulAction.fixedPoints P X) :
    6 ≤ Nat.card (MulAction.orbit A x) := by
  let K : Subgroup A := P.subgroupOf A
  have hK : IsPGroup 3 K := hP.comap_subtype
  have hnot : ∃ p : P, p • x ≠ x := by
    by_contra h
    push Not at h
    exact hx h
  obtain ⟨p, hp⟩ := hnot
  let k : K := ⟨⟨p, hPA p.2⟩, p.2⟩
  letI : Nontrivial (MulAction.orbit K x) := ⟨⟨
    ⟨k • x, MulAction.mem_orbit x k⟩,
    ⟨x, MulAction.mem_orbit_self x⟩,
    fun he => hp (congrArg Subtype.val he)⟩⟩
  have hthree : 3 ≤ Nat.card (MulAction.orbit K x) := by
    have hgt : 1 < Nat.card (MulAction.orbit K x) :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    obtain ⟨n, hn⟩ := hK.card_orbit x
    have hnpos : 1 ≤ n := by
      by_contra h
      have hnzero : n = 0 := by omega
      rw [hn, hnzero, pow_zero] at hgt
      omega
    rw [hn]
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hnpos
  letI : Nontrivial (MulAction.orbit A (b x)) := ⟨⟨
    ⟨g • b x, MulAction.mem_orbit (b x) g⟩,
    ⟨b x, MulAction.mem_orbit_self (b x)⟩,
    fun he => hmove (b x) (congrArg Subtype.val he)⟩⟩
  have htwo : 2 ≤ Nat.card (MulAction.orbit A (b x)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  exact (Nat.mul_le_mul htwo hthree).trans
    (orbit_card_ge_block_mul_fibre b (fun (a : A) y => hb a y) K x
      (fun k => hfix ⟨(k.1 : G), k.2⟩ (b x)))

variable [Finite G]

def active (H P A : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G))] :
    Finset (DoubleCoset.Quotient (H : Set G) (A : Set G)) :=
  Finset.univ.filter (fun q => inducedOrbitStabilizer H P q.out ≠ ⊤)

/-- Six points are charged for each active combined orbit. Fixed ternary
orbits need no charge and will have zero local fibre in the frame consumer. -/
theorem six_mul_active_le_index (H P A : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G))]
    (b : G ⧸ H → I)
    (hb : ∀ (a : G) (x : G ⧸ H), b (a • x) = a • b x)
    (hP : IsPGroup 3 P) (hPA : P ≤ A)
    (hfix : ∀ (p : P) (i : I), (p : G) • i = i)
    (g : A) (hmove : ∀ i : I, (g : G) • i ≠ i) :
    6 * (active H P A).card ≤ H.index := by
  have hlarge (q : DoubleCoset.Quotient (H : Set G) (A : Set G))
      (hq : q ∈ active H P A) : 6 ≤ (inducedOrbitStabilizer H A q.out).index := by
    have hnot : inducedOrbitStabilizer H P q.out ≠ ⊤ :=
      (Finset.mem_filter.mp hq).2
    have hx : ((q.out⁻¹ : G) : G ⧸ H) ∉ MulAction.fixedPoints P (G ⧸ H) := by
      intro hf
      apply hnot
      rw [inducedOrbitStabilizer_eq]
      apply top_unique
      intro p _
      exact hf p
    rw [inducedOrbitStabilizer_index, ← Nat.card_coe_set_eq]
    exact six_le_orbit b hb P A hP hPA hfix g hmove _ hx
  calc
    _ = ∑ _q ∈ active H P A, 6 := by simp [Nat.mul_comm]
    _ ≤ ∑ q ∈ active H P A, (inducedOrbitStabilizer H A q.out).index :=
      Finset.sum_le_sum hlarge
    _ ≤ ∑ q : DoubleCoset.Quotient (H : Set G) (A : Set G),
        (inducedOrbitStabilizer H A q.out).index := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    _ = H.index := inducedMackey_index_sum H A

end SymmetricSubgroupAsymptotics.TernaryNormalizerBlockOrbits

end
