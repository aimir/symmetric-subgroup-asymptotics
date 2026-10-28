import SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnActionBound
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The literal subgroup/normalizer version of the half-turn action
bound. In particular, the input is satisfied by the prime-five local
packages with m = 2; no actual normalizer order or Heisenberg recognition
is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnAmbientAction
open MulAction

variable {G X : Type*} [Group G] [Finite G] [Finite X]
  [MulAction G X] [FaithfulSMul G X] {p : ℕ}

theorem card_ge_two_prime_square (hp : p.Prime) (R : Subgroup G)
    (hR : Nat.card R = p ^ 3)
    (hZ : Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set G)) = p)
    (hcomm : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set G))
    (t : G) (ht : t ∈ Subgroup.normalizer (R : Set G))
    (hline : ∀ F : Subgroup G,
      R ⊓ Subgroup.centralizer (R : Set G) ≤ F → F ≤ R → F.relIndex R = p →
      t ∉ Subgroup.normalizer (F : Set G)) :
    2 * p ^ 2 ≤ Nat.card X := by
  let α : MulAut R := R.normalizerMonoidHom ⟨t, ht⟩
  let τ : Equiv.Perm X := MulAction.toPerm t
  have hderived : (commutator R).map R.subtype =
      R ⊓ Subgroup.centralizer (R : Set G) :=
    R.map_subtype_commutator.trans hcomm
  have hDcard : Nat.card (commutator R) = p := by
    calc
      Nat.card (commutator R) = Nat.card ((commutator R).map R.subtype) :=
        (Subgroup.card_map_of_injective R.subtype_injective).symm
      _ = p := by rw [hderived, hZ]
  have hcompat (r : R) (x : X) : τ (r • x) = α r • τ x := by
    change t • ((r : G) • x) = (t * (r : G) * t⁻¹) • (t • x)
    simp only [mul_smul, inv_smul_smul]
  have hlines (F : Subgroup R) (hDF : commutator R ≤ F) (hFi : F.index = p) :
      F.map α.toMonoidHom ≠ F := by
    intro heq
    have hZF : R ⊓ Subgroup.centralizer (R : Set G) ≤ F.map R.subtype := by
      rw [← hderived]
      exact Subgroup.map_mono hDF
    have hFR : F.map R.subtype ≤ R := Subgroup.map_subtype_le F
    have htop : (⊤ : Subgroup R).map R.subtype = R := by
      rw [← MonoidHom.range_eq_map, R.range_subtype]
    have hrel : (F.map R.subtype).relIndex R = p := by
      calc
        (F.map R.subtype).relIndex R =
            (F.map R.subtype).relIndex ((⊤ : Subgroup R).map R.subtype) := by rw [htop]
        _ = F.relIndex ⊤ :=
          Subgroup.relIndex_map_map_of_injective F ⊤ R.subtype_injective
        _ = F.index := Subgroup.relIndex_top_right F
        _ = p := hFi
    apply hline _ hZF hFR hrel
    apply Subgroup.mem_normalizer_fintype
    rintro g ⟨u, hu, rfl⟩
    refine ⟨α u, ?_, ?_⟩
    · have hm : α u ∈ F.map α.toMonoidHom := ⟨u, hu, rfl⟩
      rwa [heq] at hm
    · rfl
  letI : Nontrivial (commutator R) := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [hDcard]; exact hp.one_lt)
  obtain ⟨z, hz⟩ := exists_ne (1 : commutator R)
  have hzn : ((z : R) : G) ≠ 1 := by
    intro he
    apply hz
    apply Subtype.ext
    exact Subtype.ext he
  obtain ⟨x, hx⟩ : ∃ x : X, ((z : R) : G) • x ≠ x := by
    by_contra! hfix
    apply hzn
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    simpa only [one_smul] using hfix x
  have hmove : ¬ commutator R ≤ stabilizer R x := by
    intro hle
    exact hx (hle z.property)
  exact PrimeCubeHalfTurnActionBound.card_ge_two_prime_square
    hp hR hDcard α τ hcompat hlines x hmove

end SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnAmbientAction
