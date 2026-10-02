import SymmetricSubgroupAsymptotics.Non2PreE7SaprimExceptionalOdd

/-!
# The degree-nine central-product comparison

The projective quotient of a soluble subgroup of `GL₂(3)` has a central
binary lift.  The counting step needed by the degree-nine primitive-affine
owner is completely generic: binary twists which do not factor through a
fixed epimorphism enlarge its target to `A × C₂`, while the factoring twists
are indexed by the binary characters of `A` itself.

This file first proves that injection without any condition on the binary
characters of `A`.  The subsequent sections apply it simultaneously to all
normal quotients of a fixed central extension.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C2 := Multiplicative (ZMod 2)

/-- Binary twists of epimorphisms to an arbitrary finite target.  A twist
which is nontrivial on the kernel produces an epimorphism to `A × C₂`; a
twist which vanishes on the kernel factors uniquely through `A`. -/
theorem epi_mul_hom_two_le_general
    {J A : Type*} [Group J] [Group A] [Finite J] [Finite A] :
    Nat.card (GroupEpimorphism J A) * Nat.card (J →* C2) ≤
      Nat.card (GroupEpimorphism J (A × C2)) +
        Nat.card (GroupEpimorphism J A) * Nat.card (A →* C2) := by
  letI : Finite (J →* A × C2) :=
    Finite.of_injective (fun f : J →* A × C2 => (f : J → A × C2))
      DFunLike.coe_injective
  letI : Finite (J →* A) :=
    Finite.of_injective (fun f : J →* A => (f : J → A)) DFunLike.coe_injective
  letI : Finite (J →* C2) :=
    Finite.of_injective (fun f : J →* C2 => (f : J → C2)) DFunLike.coe_injective
  letI : Finite (A →* C2) :=
    Finite.of_injective (fun f : A →* C2 => (f : A → C2)) DFunLike.coe_injective
  have honto : ∀ (f : GroupEpimorphism J A) (χ : J →* C2),
      (¬ ∃ χ' : A →* C2, χ'.comp f.1 = χ) →
      Function.Surjective (f.1.prod χ) := by
    intro f χ hfac
    have hk : ∃ k ∈ f.1.ker, χ k ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hfac (character_factors f.1 f.2 χ hall)
    obtain ⟨k, hkf, hkχ⟩ := hk
    rintro ⟨a, c⟩
    obtain ⟨x, hx⟩ := f.2 a
    by_cases hc : χ x = c
    · exact ⟨x, Prod.ext hx hc⟩
    · refine ⟨x * k, Prod.ext ?_ ?_⟩
      · show f.1 (x * k) = a
        rw [map_mul, (MonoidHom.mem_ker).mp hkf, mul_one, hx]
      · show χ (x * k) = c
        have h1 : χ (x * k) ≠ χ x := by
          rw [map_mul]
          intro h
          apply hkχ
          exact mul_eq_left.mp h
        have hall : ∀ u v w : C2, u ≠ v → w ≠ v → u = w := by decide
        exact hall _ _ _ h1 (fun h => hc h.symm)
  let g : GroupEpimorphism J A × (J →* C2) →
      GroupEpimorphism J (A × C2) ⊕ (GroupEpimorphism J A × (A →* C2)) :=
    fun p => if hfac : ∃ χ' : A →* C2, χ'.comp p.1.1 = p.2 then
      Sum.inr (p.1, Classical.choose hfac)
    else Sum.inl ⟨p.1.1.prod p.2, honto p.1 p.2 hfac⟩
  have hchoose : ∀ (f : GroupEpimorphism J A) (χ : J →* C2)
      (hfac : ∃ χ' : A →* C2, χ'.comp f.1 = χ),
      (Classical.choose hfac).comp f.1 = χ := by
    intro f χ hfac
    exact Classical.choose_spec hfac
  have hg : Function.Injective g := by
    rintro ⟨f, χ⟩ ⟨f', χ'⟩ he
    by_cases hf : ∃ ψ : A →* C2, ψ.comp f.1 = χ <;>
      by_cases hf' : ∃ ψ : A →* C2, ψ.comp f'.1 = χ'
    · simp only [g, hf, hf', dite_true, Sum.inr.injEq, Prod.mk.injEq] at he
      rcases he with ⟨hff, hψ⟩
      subst f'
      apply Prod.ext
      · rfl
      · rw [← hchoose f χ hf, ← hchoose f χ' hf', hψ]
    · simp only [g, hf, hf', dite_true, dite_false, reduceCtorEq] at he
    · simp only [g, hf, hf', dite_true, dite_false, reduceCtorEq] at he
    · simp only [g, hf, hf', dite_false, Sum.inl.injEq] at he
      have hval := congrArg Subtype.val he
      apply Prod.ext
      · apply Subtype.ext
        ext x
        exact congrArg Prod.fst (DFunLike.congr_fun hval x)
      · ext x
        exact congrArg Prod.snd (DFunLike.congr_fun hval x)
  calc
    Nat.card (GroupEpimorphism J A) * Nat.card (J →* C2) =
        Nat.card (GroupEpimorphism J A × (J →* C2)) :=
      (Nat.card_prod _ _).symm
    _ ≤ Nat.card (GroupEpimorphism J (A × C2) ⊕
          (GroupEpimorphism J A × (A →* C2))) :=
      Nat.card_le_card_of_injective g hg
    _ = _ := by rw [Nat.card_sum, Nat.card_prod]

/-! ## A structural model for every quotient -/

/-- Structural data on one quotient `X` of the binary central extension.
The target `A` is its projective image.  The two displayed normal axes say
that both `A × C₂` and `A` occur as literal quotients of the single faithful
six-point comparator `Q`.  No epimorphism estimate is a field of this
structure. -/
structure CentralBinaryQuotientDatum
    (Q X : Type*) [Group Q] [Finite Q] [Group X] [Finite X] where
  A : Type
  [groupA : Group A]
  [finiteA : Finite A]
  projection : X →* A
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : X, z * x = x * z
  kernelCharacter : projection.ker →* C2
  kernelCharacter_injective : Function.Injective kernelCharacter
  productAxis : {N : Subgroup Q // N.Normal}
  baseAxis : {N : Subgroup Q // N.Normal}
  axes_ne : productAxis ≠ baseAxis
  productEquiv : A × C2 ≃* Q ⧸ productAxis.1
  baseEquiv : A ≃* Q ⧸ baseAxis.1

attribute [instance] CentralBinaryQuotientDatum.groupA
  CentralBinaryQuotientDatum.finiteA

namespace CentralBinaryQuotientDatum

variable {Q X : Type*} [Group Q] [Finite Q] [Group X] [Finite X]
  (D : CentralBinaryQuotientDatum Q X)

/-- Homomorphisms into the central kernel inject into binary characters of
the source through the retained faithful kernel character. -/
theorem kernel_hom_card_le {J : Type*} [Group J] [Finite J] :
    Nat.card (J →* D.projection.ker) ≤ Nat.card (J →* C2) := by
  letI : Finite (J →* D.projection.ker) :=
    Finite.of_injective (fun f : J →* D.projection.ker => (f : J → D.projection.ker))
      DFunLike.coe_injective
  letI : Finite (J →* C2) :=
    Finite.of_injective (fun f : J →* C2 => (f : J → C2)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective
    (fun f : J →* D.projection.ker => D.kernelCharacter.comp f)
    (fun f g h => MonoidHom.ext fun x => D.kernelCharacter_injective
      (DFunLike.congr_fun h x))

/-- Both projective twist targets are paid by literal axes of the one
comparator. -/
theorem twist_axes_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J (D.A × C2)) +
        Nat.card (GroupEpimorphism J D.A) ≤
      completeQuotientCount (R := Q) J :=
  two_axes_le_completeQuotientCount J D.productAxis D.baseAxis D.axes_ne
    D.productEquiv D.baseEquiv

/-- One quotient of the central extension is controlled by the common
comparator.  The coefficient is the fixed number of binary characters of
its projective image (with `1` inserted for the product axis). -/
theorem epi_card_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J X) ≤
      max 1 (Nat.card (D.A →* C2)) * completeQuotientCount (R := Q) J := by
  have hlift := epi_card_le_centralLift (J := J) D.projection
    D.projection_surjective D.central_kernel
  have hker := D.kernel_hom_card_le (J := J)
  have htwist := epi_mul_hom_two_le_general (J := J) (A := D.A)
  have haxes := D.twist_axes_le J
  let x := Nat.card (GroupEpimorphism J (D.A × C2))
  let y := Nat.card (GroupEpimorphism J D.A)
  let c := Nat.card (D.A →* C2)
  let m := max 1 c
  have hscale : x + y * c ≤ m * (x + y) := by
    have hx : x ≤ m * x := by
      calc x = 1 * x := by omega
        _ ≤ m * x := Nat.mul_le_mul_right x (Nat.le_max_left 1 c)
    have hy : y * c ≤ m * y := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right y (Nat.le_max_right 1 c)
    calc x + y * c ≤ m * x + m * y := Nat.add_le_add hx hy
      _ = m * (x + y) := (Nat.mul_add _ _ _).symm
  calc
    Nat.card (GroupEpimorphism J X) ≤
        Nat.card (GroupEpimorphism J D.A) *
          Nat.card (J →* D.projection.ker) := hlift
    _ ≤ Nat.card (GroupEpimorphism J D.A) * Nat.card (J →* C2) :=
      Nat.mul_le_mul_left _ hker
    _ ≤ Nat.card (GroupEpimorphism J (D.A × C2)) +
          Nat.card (GroupEpimorphism J D.A) * Nat.card (D.A →* C2) := htwist
    _ ≤ max 1 (Nat.card (D.A →* C2)) *
          (Nat.card (GroupEpimorphism J (D.A × C2)) +
            Nat.card (GroupEpimorphism J D.A)) := hscale
    _ ≤ max 1 (Nat.card (D.A →* C2)) * completeQuotientCount (R := Q) J :=
      Nat.mul_le_mul_left _ haxes

end CentralBinaryQuotientDatum

/-! ## Simultaneous complete-quotient comparison -/

/-- A fixed binary central extension, described on every literal normal
quotient.  For the small groups in degree nine this datum is read directly
from the published subgroup tables of `GL₂(3)`: the projective images act on
four points and their products with `C₂` act faithfully on six. -/
structure DegreeNineCentralProductModel
    (R : Type*) [Group R] [Finite R] where
  Q : Subgroup (Equiv.Perm (Fin 6))
  quotient : ∀ M : {M : Subgroup R // M.Normal},
    CentralBinaryQuotientDatum Q (R ⧸ M.1)

namespace DegreeNineCentralProductModel

variable {R : Type*} [Group R] [Finite R]
  (D : DegreeNineCentralProductModel R)

/-- The finite coefficient that pays every literal quotient and every
factoring projective binary character. -/
def coefficient : ℕ :=
  ∑ M : {M : Subgroup R // M.Normal},
    max 1 (Nat.card ((D.quotient M).A →* C2))

theorem completeQuotientCount_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientCount (R := R) J ≤
      D.coefficient * completeQuotientCount (R := D.Q) J := by
  unfold completeQuotientCount coefficient
  calc
    (∑ M : {M : Subgroup R // M.Normal},
        Nat.card (GroupEpimorphism J (R ⧸ M.1))) ≤
      ∑ M : {M : Subgroup R // M.Normal},
        max 1 (Nat.card ((D.quotient M).A →* C2)) *
          completeQuotientCount (R := D.Q) J := by
      apply Finset.sum_le_sum
      intro M _
      exact (D.quotient M).epi_card_le J
    _ = (∑ M : {M : Subgroup R // M.Normal},
          max 1 (Nat.card ((D.quotient M).A →* C2))) *
          completeQuotientCount (R := D.Q) J := by
      rw [Finset.sum_mul]

/-- The former degree-nine counting input is constructed from structural
quotient data; its complete-weight inequality is a theorem. -/
noncomputable def toComparator :
    Non2UnipotentPrefixFiniteMenu.PreE7DegreeNineCentralProductComparator R where
  Q := D.Q
  coefficient := D.coefficient
  coefficient_nonneg := Nat.cast_nonneg _
  complete_bound := by
    intro b J
    unfold completeQuotientWeight
    exact_mod_cast D.completeQuotientCount_le J

end DegreeNineCentralProductModel

end SymmetricSubgroupAsymptotics

end
