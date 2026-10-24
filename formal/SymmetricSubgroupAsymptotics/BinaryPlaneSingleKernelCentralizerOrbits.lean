import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarAction
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex

/-! The actual cubic centralizer has one or two actual block orbits,
and the latter are of equal size. This does not replace them by a
transitive action on the original block set. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCentralizerOrbits
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryPlaneSingleKernelScalarAction

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I]
    (C : Subgroup (W (R := R) (I := I))) (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hO : oddKernel C ≠ ⊥)
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)

abbrev blockAction : MulAction C I := MulAction.compHom I
  ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype)

include hsingle hO htrans in
/-- Orbit classes are those of the literal centralizer on the original blocks. -/
theorem orbit_count_le_two :
    letI := blockAction C
    Nat.card (MulAction.orbitRel.Quotient (centralizer C) I) ≤ 2 := by
  letI := blockAction C
  letI : MulAction.IsPretransitive C I := ⟨htrans⟩
  rw [normal_orbit_classes_card_eq_index (centralizer C) i₀]
  exact (Subgroup.index_antitone (show centralizer C ≤
    centralizer C ⊔ MulAction.stabilizer C i₀ from le_sup_left)).trans
      (centralizer_index_le_two C i₀ hsingle hO)

include hsingle hO htrans in
theorem orbit_count_one_or_two :
    letI := blockAction C
    Nat.card (MulAction.orbitRel.Quotient (centralizer C) I) = 1 ∨
      Nat.card (MulAction.orbitRel.Quotient (centralizer C) I) = 2 := by
  letI := blockAction C
  have hle := orbit_count_le_two C i₀ hsingle hO htrans
  have hpos : 0 < Nat.card (MulAction.orbitRel.Quotient (centralizer C) I) :=
    Finite.card_pos_iff.mpr ⟨Quotient.mk'' i₀⟩
  omega

include hsingle hO htrans in
/-- The one-orbit branch gives actual H transporters. In the other
branch every actual H orbit has exactly half the original carrier. -/
theorem orbit_alternative :
    letI := blockAction C
    (∀ i j : I, ∃ h : centralizer C,
      ((((h : centralizer C) : C) : W (R := R) (I := I)).right • i) = j) ∨
    (Nat.card (MulAction.orbitRel.Quotient (centralizer C) I) = 2 ∧
      ∀ o : MulAction.orbitRel.Quotient (centralizer C) I,
        2 * Nat.card o.orbit = Nat.card I) := by
  letI := blockAction C
  letI : MulAction.IsPretransitive C I := ⟨htrans⟩
  rcases orbit_count_one_or_two C i₀ hsingle hO htrans with hone | htwo
  · left
    letI : Subsingleton (MulAction.orbitRel.Quotient (centralizer C) I) :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    letI : MulAction.IsPretransitive (centralizer C) I :=
      (MulAction.pretransitive_iff_subsingleton_quotient (centralizer C) I).mpr inferInstance
    exact fun i j => MulAction.exists_smul_eq (centralizer C) i j
  · right
    refine ⟨htwo,?_⟩
    intro o
    have hp := normal_orbit_card_mul_classes (centralizer C) i₀
    rw [htwo] at hp
    have he := normal_orbit_card_eq (centralizer C) i₀ o
    omega

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCentralizerOrbits
