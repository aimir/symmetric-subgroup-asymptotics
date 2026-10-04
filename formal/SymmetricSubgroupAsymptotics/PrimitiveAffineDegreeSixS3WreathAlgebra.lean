import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource

/-!
# Finite algebra for the degree-six `S₃ ≀ C₂` cell

This file supplies the two algebraic facts requested by the source module.
All elements and maps are literal in

`(S₃ × S₃) ⋊ C₂`.

The only finite checks below concern explicit permutations and explicit
words.  The normal-subgroup statements are then proved from those checked
words: the sign kernel is minimal and self-centralizing, its second derived
term is literal, and its first ternary coordinate separates under conjugacy.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

open Equiv C2Wreath SemidirectProduct

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev C3 := Multiplicative (ZMod 3)

/-- A fixed ternary rotation in the first natural `S₃`. -/
private def rotation : S3 :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- A fixed transposition. -/
private def transposition : S3 := Equiv.swap (0 : Fin 3) 1

/-- Rotation in the first base factor. -/
private def firstRotation : G := inl (rotation, 1)

/-- Rotation in the second base factor. -/
private def secondRotation : G := inl (1, rotation)

/-- A sign change in the first base factor. -/
private def firstFlip : G := inl (transposition, 1)

/-- The diagonal sign change. -/
private def diagonalFlip : G := inl (transposition, transposition)

/-- The block exchange. -/
private def blockSwap : G := inr C2Wreath.gen

/-- Concrete membership in the kernel of coordinatewise sign. -/
private theorem mem_projection_ker_iff (x : G) :
    x ∈ projection.ker ↔
      x.right = 1 ∧ oddMarkerSign x.left.1 = 1 ∧
        oddMarkerSign x.left.2 = 1 := by
  revert x
  native_decide

private theorem firstRotation_mem : firstRotation ∈ projection.ker := by
  rw [mem_projection_ker_iff]
  native_decide

private theorem secondRotation_mem : secondRotation ∈ projection.ker := by
  rw [mem_projection_ker_iff]
  native_decide

/-- Every element of the sign kernel has literal two-coordinate ternary
normal form. -/
private theorem kernel_normal_form : ∀ x : G, x ∈ projection.ker →
    ∃ i j : Fin 3,
      x = firstRotation ^ (i : ℕ) * secondRotation ^ (j : ℕ) := by
  native_decide

/-- The displayed sign kernel is abelian. -/
private theorem kernel_elements_commute : ∀ x y : G,
    x ∈ projection.ker → y ∈ projection.ker → x * y = y * x := by
  intro x y hx hy
  rw [mem_projection_ker_iff] at hx hy
  revert x y
  native_decide

/-- Commuting with the two displayed rotations forces membership in the
sign kernel. -/
private theorem centralizer_test : ∀ x : G,
    x * firstRotation = firstRotation * x →
    x * secondRotation = secondRotation * x →
    x ∈ projection.ker := by
  intro x hx hy
  rw [mem_projection_ker_iff]
  revert x
  native_decide

theorem projection_ker_selfCentralizing
    (x : G) (hx : ∀ v ∈ projection.ker, x * v = v * x) :
    x ∈ projection.ker :=
  centralizer_test x (hx firstRotation firstRotation_mem)
    (hx secondRotation secondRotation_mem)

/-! ## Derived series -/

private theorem mem_derivedSeries_succ {n : ℕ} {x y : G}
    (hx : x ∈ derivedSeries G n) (hy : y ∈ derivedSeries G n) :
    ⁅x, y⁆ ∈ derivedSeries G (n + 1) := by
  rw [derivedSeries_succ]
  exact Subgroup.commutator_mem_commutator hx hy

private theorem mem_derivedSeries_one (x y : G) :
    ⁅x, y⁆ ∈ derivedSeries G 1 :=
  mem_derivedSeries_succ (by simp [derivedSeries_zero])
    (by simp [derivedSeries_zero])

/-- The diagonal transposition is a literal first-derived word. -/
private theorem diagonalFlip_eq_commutator :
    diagonalFlip = ⁅firstFlip, blockSwap⁆ := by
  native_decide

private theorem diagonalFlip_mem_one :
    diagonalFlip ∈ derivedSeries G 1 := by
  rw [diagonalFlip_eq_commutator]
  exact mem_derivedSeries_one _ _

/-- The diagonal transposition commutator recovers every element of the
ternary sign kernel. -/
private theorem diagonal_commutator : ∀ x : G, x ∈ projection.ker →
    ⁅diagonalFlip, x⁆ = x := by
  native_decide

private theorem projection_ker_le_one :
    projection.ker ≤ derivedSeries G 1 := by
  intro x hx
  rw [← diagonal_commutator x hx]
  exact mem_derivedSeries_one _ _

private theorem projection_ker_le_two :
    projection.ker ≤ derivedSeries G 2 := by
  intro x hx
  rw [← diagonal_commutator x hx]
  exact mem_derivedSeries_succ diagonalFlip_mem_one
    (projection_ker_le_one hx)

/-- Commutators of two base elements have even coordinates. -/
private theorem right_one_commutator_mem : ∀ x y : G,
    x.right = 1 → y.right = 1 → ⁅x, y⁆ ∈ projection.ker := by
  native_decide

/-- The literal second derived subgroup is exactly `A₃²`. -/
theorem derivedSeries_two_eq_projection_ker :
    derivedSeries G 2 = projection.ker := by
  apply le_antisymm
  · have hright : derivedSeries G 1 ≤
        (SemidirectProduct.rightHom : G →* C2).ker := by
      rw [derivedSeries_one]
      exact Abelianization.commutator_subset_ker _
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono hright hright).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxr : x.right = 1 := hx
    have hyr : y.right = 1 := hy
    exact right_one_commutator_mem x y hxr hyr
  · exact projection_ker_le_two

/-! ## Absorption and minimality -/

private theorem diagonal_fixedPointFree : ∀ x : G,
    x ∈ projection.ker →
    diagonalFlip * x * diagonalFlip⁻¹ = x → x = 1 := by
  native_decide

theorem projection_ker_absorbing
    (W : Subgroup G) (hW : W.Normal) (hWV : W ≤ projection.ker) :
    W ≤ ⁅derivedSeries G 1, W⁆ := by
  apply DerivedHead.absorbing_of_fixedPointFree 1 diagonalFlip
  · exact diagonalFlip_mem_one
  · intro x hx y hy
    rw [derivedSeries_two_eq_projection_ker] at hx hy
    exact kernel_elements_commute x y hx hy
  · intro x hx hfix
    rw [derivedSeries_two_eq_projection_ker] at hx
    exact diagonal_fixedPointFree x hx hfix
  · exact hW
  · exact hWV.trans derivedSeries_two_eq_projection_ker.ge

private theorem comm_mem (W : Subgroup G) (hW : W.Normal)
    {x : G} (hx : x ∈ W) (g : G) : ⁅g, x⁆ ∈ W := by
  rw [commutatorElement_def]
  exact W.mul_mem (hW.conj_mem _ hx g) (W.inv_mem hx)

/-- A nontrivial first ternary coordinate yields the fixed first rotation by
one of two explicit commutator words. -/
private theorem isolate_first_rotation : ∀ x : G,
    x ∈ projection.ker → x.left.1 ≠ 1 →
    ⁅firstFlip, x⁆ = firstRotation ∨
      ⁅firstFlip, x⁆ ^ 2 = firstRotation := by
  intro x hx hne
  rw [mem_projection_ker_iff] at hx
  revert x
  native_decide

private theorem firstRotation_mem_of_first_ne
    (W : Subgroup G) (hW : W.Normal) {x : G}
    (hxW : x ∈ W) (hxV : x ∈ projection.ker)
    (hx1 : x.left.1 ≠ 1) : firstRotation ∈ W := by
  have hc := comm_mem W hW hxW firstFlip
  rcases isolate_first_rotation x hxV hx1 with h | h
  · rw [← h]
    exact hc
  · rw [← h]
    exact W.pow_mem hc 2

private theorem swap_conjugate_first (x : G) :
    (blockSwap * x * blockSwap⁻¹).left.1 = x.left.2 := by
  revert x
  native_decide

private theorem swap_firstRotation :
    blockSwap * firstRotation * blockSwap⁻¹ = secondRotation := by
  native_decide

private theorem second_ne_of_first_eq_one : ∀ x : G,
    x ∈ projection.ker → x ≠ 1 → x.left.1 = 1 → x.left.2 ≠ 1 := by
  native_decide

/-- `A₃²` is a minimal normal subgroup of the literal wreath product. -/
theorem projection_ker_minimal
    (W : Subgroup G) (hW : W.Normal) (hWV : W ≤ projection.ker) :
    W = ⊥ ∨ W = projection.ker := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hWV
  obtain ⟨⟨x, hxW⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxV : x ∈ projection.ker := hWV hxW
  have hr1 : firstRotation ∈ W := by
    by_cases hfirst : x.left.1 = 1
    · let y := blockSwap * x * blockSwap⁻¹
      have hyW : y ∈ W := hW.conj_mem x hxW blockSwap
      have hyV : y ∈ projection.ker :=
        (inferInstance : projection.ker.Normal).conj_mem x hxV blockSwap
      apply firstRotation_mem_of_first_ne W hW hyW hyV
      dsimp only [y]
      rw [swap_conjugate_first]
      exact second_ne_of_first_eq_one x hxV hx1' hfirst
    · exact firstRotation_mem_of_first_ne W hW hxW hxV hfirst
  have hr2 : secondRotation ∈ W := by
    have h := hW.conj_mem firstRotation hr1 blockSwap
    rwa [swap_firstRotation] at h
  intro v hv
  obtain ⟨i, j, hij⟩ := kernel_normal_form v hv
  rw [hij]
  exact W.mul_mem (W.pow_mem hr1 (i : ℕ)) (W.pow_mem hr2 (j : ℕ))

theorem projection_ker_normal_cover
    (N : Subgroup G) (hN : N.Normal) (hNb : N ≠ ⊥) :
    projection.ker ≤ N := by
  letI : N.Normal := hN
  exact le_of_minimal_selfCentralizing projection.ker
    projection_ker_minimal projection_ker_selfCentralizing N hNb

/-! ## The separating ternary character -/

/-- Explicit exponent coordinate on the three even permutations.  Its values
away from `A₃` are irrelevant, since `kernelCharacter` is restricted to the
literal sign kernel. -/
private def ternaryCoordinate (g : S3) : ZMod 3 :=
  if g = 1 then 0 else if g = rotation then 1 else 2

private theorem eq_one_of_even_ternaryCoordinate_one (g : S3)
    (heven : oddMarkerSign g = 1)
    (hcoord : Multiplicative.ofAdd (ternaryCoordinate g) = (1 : C3)) :
    g = 1 := by
  revert g
  native_decide

private theorem ternaryCoordinate_mul_of_even (g h : S3)
    (hg : oddMarkerSign g = 1) (hh : oddMarkerSign h = 1) :
    Multiplicative.ofAdd (ternaryCoordinate (g * h)) =
      Multiplicative.ofAdd (ternaryCoordinate g) *
        Multiplicative.ofAdd (ternaryCoordinate h) := by
  revert g h
  native_decide

/-- The first ternary coordinate of `A₃²`. -/
def kernelCharacter : projection.ker →* C3 where
  toFun x := Multiplicative.ofAdd (ternaryCoordinate x.1.left.1)
  map_one' := by native_decide
  map_mul' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [mem_projection_ker_iff] at hx hy
    change Multiplicative.ofAdd (ternaryCoordinate ((x * y).left.1)) =
      Multiplicative.ofAdd (ternaryCoordinate x.left.1) *
        Multiplicative.ofAdd (ternaryCoordinate y.left.1)
    simpa [hx.1, C2Wreath.swapAut_one] using
      ternaryCoordinate_mul_of_even x.left.1 y.left.1 hx.2.1 hy.2.1

private theorem kernelCharacter_separating :
    ∀ v : projection.ker,
      (∀ q : G, kernelCharacter (MulAut.conjNormal q v) = 1) → v = 1 := by
  intro v h
  have hv := v.2
  rw [mem_projection_ker_iff] at hv
  have hc1 := h 1
  change Multiplicative.ofAdd
    (ternaryCoordinate ((MulAut.conjNormal 1 v : projection.ker) : G).left.1) = 1 at hc1
  rw [MulAut.conjNormal_apply] at hc1
  simp only [one_mul, inv_one, mul_one] at hc1
  have hc2 := h blockSwap
  change Multiplicative.ofAdd
    (ternaryCoordinate
      ((MulAut.conjNormal blockSwap v : projection.ker) : G).left.1) = 1 at hc2
  rw [MulAut.conjNormal_apply] at hc2
  rw [swap_conjugate_first] at hc2
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact Prod.ext
      (eq_one_of_even_ternaryCoordinate_one _ hv.2.1 hc1)
      (eq_one_of_even_ternaryCoordinate_one _ hv.2.2 hc2)
  · exact hv.1

/-- The completed cyclic-dual target on the literal second derived subgroup. -/
def target : DerivedHead.DerivedCyclicTarget G projection.ker 1 3 where
  derived_eq := derivedSeries_two_eq_projection_ker
  character := kernelCharacter
  self_centralizing := projection_ker_selfCentralizing
  absorbing := projection_ker_absorbing
  separating := kernelCharacter_separating

/-- Concrete algebra consumed by `PreE7DegreeSixS3WreathSource.source`. -/
def algebra : Algebra where
  target := target
  normal_cover := projection_ker_normal_cover

end DegreeSixS3Wreath
end SymmetricSubgroupAsymptotics

end
