import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Atoms.Finite

/-! A block quotient is constructed on the original transitive point set
from an actual overgroup of its point stabilizer. No classification,
numerical head bound, or replacement permutation action is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω : Type*} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω] (ω₀ : Ω)

def originalPointTransporter (ω : Ω) : A :=
  Classical.choose (MulAction.exists_smul_eq A ω₀ ω)

theorem originalPointTransporter_spec (ω : Ω) :
    originalPointTransporter (A := A) ω₀ ω • ω₀ = ω :=
  Classical.choose_spec (MulAction.exists_smul_eq A ω₀ ω)

/-- The literal quotient of the chosen point transporter by H. -/
def originalTransitiveBlockMap (H : Subgroup A) (ω : Ω) : A ⧸ H :=
  (originalPointTransporter (A := A) ω₀ ω : A)

theorem originalTransitiveBlockMap_smul_base (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) (a : A) :
    originalTransitiveBlockMap ω₀ H (a • ω₀) = (a : A ⧸ H) := by
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  apply hH
  change ((originalPointTransporter (A := A) ω₀ (a • ω₀))⁻¹ * a) • ω₀ = ω₀
  rw [mul_smul]
  calc
    (originalPointTransporter (A := A) ω₀ (a • ω₀))⁻¹ • (a • ω₀) =
        (originalPointTransporter (A := A) ω₀ (a • ω₀))⁻¹ •
          (originalPointTransporter (A := A) ω₀ (a • ω₀) • ω₀) :=
      congrArg (fun x => (originalPointTransporter (A := A) ω₀ (a • ω₀))⁻¹ • x)
        (originalPointTransporter_spec (A := A) ω₀ (a • ω₀)).symm
    _ = ω₀ := inv_smul_smul _ _

theorem originalTransitiveBlockMap_equivariant (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) (a : A) (ω : Ω) :
    originalTransitiveBlockMap ω₀ H (a • ω) =
      a • originalTransitiveBlockMap ω₀ H ω := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq A ω₀ ω
  rw [← mul_smul, originalTransitiveBlockMap_smul_base ω₀ H hH,
    originalTransitiveBlockMap_smul_base ω₀ H hH]
  rfl

theorem originalTransitiveBlockMap_surjective (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) :
    Function.Surjective (originalTransitiveBlockMap ω₀ H) := by
  intro x
  induction x using Quotient.inductionOn with
  | h a => exact ⟨a • ω₀, originalTransitiveBlockMap_smul_base ω₀ H hH a⟩

theorem originalTransitiveBlockMap_base (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) :
    originalTransitiveBlockMap ω₀ H ω₀ = ((1 : A) : A ⧸ H) := by
  simpa only [one_smul] using originalTransitiveBlockMap_smul_base ω₀ H hH 1

theorem originalTransitiveBlockMap_fibre_iff (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) (ω : Ω) :
    originalTransitiveBlockMap ω₀ H ω = ((1 : A) : A ⧸ H) ↔
      ω ∈ MulAction.orbit H ω₀ := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A ω₀ ω
  rw [originalTransitiveBlockMap_smul_base ω₀ H hH]
  constructor
  · intro ha
    have haH : a ∈ H := by
      simpa only [QuotientGroup.eq, mul_one, inv_mem_iff] using ha
    exact ⟨⟨a, haH⟩, rfl⟩
  · rintro ⟨h, hh⟩
    have he : originalTransitiveBlockMap ω₀ H ((h : A) • ω₀) =
        originalTransitiveBlockMap ω₀ H (a • ω₀) := congrArg _ hh
    rw [originalTransitiveBlockMap_smul_base ω₀ H hH,
      originalTransitiveBlockMap_smul_base ω₀ H hH] at he
    rw [← he]
    simpa only [QuotientGroup.eq, mul_one, inv_mem_iff] using h.2

def originalTransitiveBlockFibreEquivOrbit (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) :
    {ω : Ω // originalTransitiveBlockMap ω₀ H ω = ((1 : A) : A ⧸ H)} ≃
      MulAction.orbit H ω₀ where
  toFun ω := ⟨ω.1, (originalTransitiveBlockMap_fibre_iff ω₀ H hH ω.1).mp ω.2⟩
  invFun ω := ⟨ω.1, (originalTransitiveBlockMap_fibre_iff ω₀ H hH ω.1).mpr ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem originalTransitiveBlockFibre_card (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) :
    Nat.card {ω : Ω // originalTransitiveBlockMap ω₀ H ω = ((1 : A) : A ⧸ H)} =
      (MulAction.stabilizer A ω₀).relIndex H := by
  rw [Nat.card_congr (originalTransitiveBlockFibreEquivOrbit ω₀ H hH),
    Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  rfl

theorem originalTransitiveBlock_degree_product (H : Subgroup A)
    (hH : MulAction.stabilizer A ω₀ ≤ H) :
    Nat.card {ω : Ω // originalTransitiveBlockMap ω₀ H ω = ((1 : A) : A ⧸ H)} *
        Nat.card (A ⧸ H) = Nat.card Ω := by
  rw [originalTransitiveBlockFibre_card ω₀ H hH]
  change (MulAction.stabilizer A ω₀).relIndex H * H.index = Nat.card Ω
  rw [Subgroup.relIndex_mul_index hH, MulAction.index_stabilizer_of_transitive]

/-- A nonprimitive original transitive action supplies a proper overgroup
covering the actual point stabilizer. This is finite subgroup order theory. -/
theorem originalPointStabilizer_exists_proper_cover [Finite A] [Finite Ω]
    [Nontrivial Ω] (hn : ¬MulAction.IsPreprimitive A Ω) :
    ∃ H : Subgroup A, MulAction.stabilizer A ω₀ ⋖ H ∧ H < ⊤ := by
  classical
  letI : Finite (Subgroup A) :=
    Finite.of_injective (fun H : Subgroup A => (H : Set A)) SetLike.coe_injective
  letI : Fintype (Subgroup A) := Fintype.ofFinite _
  letI : LocallyFiniteOrder (Subgroup A) := Fintype.toLocallyFiniteOrder
  have hne : MulAction.stabilizer A ω₀ ≠ ⊤ := by
    intro he
    have hc := MulAction.index_stabilizer_of_transitive A ω₀
    rw [he, Subgroup.index_top] at hc
    have hsub : Subsingleton Ω := (Nat.card_eq_one_iff_unique.mp hc.symm).1
    obtain ⟨ω, hω⟩ := exists_ne ω₀
    exact hω (hsub.elim ω ω₀)
  have hnot : ¬MulAction.stabilizer A ω₀ ⋖ ⊤ := by
    intro h
    exact hn ((MulAction.isCoatom_stabilizer_iff_preprimitive A ω₀).mp h.isCoatom)
  obtain ⟨K, hSK, hKt⟩ := exists_lt_lt_of_not_covBy (lt_top_iff_ne_top.mpr hne) hnot
  obtain ⟨H, hSH, hHK⟩ := exists_covBy_le_of_lt hSK
  exact ⟨H, hSH, hHK.trans_lt hKt⟩

theorem originalTransitiveBlock_factors_ge_two [Finite A]
    (H : Subgroup A) (hH : MulAction.stabilizer A ω₀ < H) (hHt : H < ⊤) :
    2 ≤ Nat.card {ω : Ω // originalTransitiveBlockMap ω₀ H ω = ((1 : A) : A ⧸ H)} ∧
      2 ≤ Nat.card (A ⧸ H) := by
  rw [originalTransitiveBlockFibre_card ω₀ H hH.le]
  have hr : 1 < (MulAction.stabilizer A ω₀).relIndex H :=
    Subgroup.one_lt_index_of_ne_top (by
      intro he
      exact (not_le_of_gt hH) (Subgroup.subgroupOf_eq_top.mp he))
  have hs : 1 < H.index := Subgroup.one_lt_index_of_ne_top hHt.ne
  exact ⟨hr, hs⟩

end SymmetricSubgroupAsymptotics
