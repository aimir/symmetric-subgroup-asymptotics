import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-!
# Coupled heads in a binary permutation module

The paired-eight quartet kernel has three binary layers.  Their trivial
Schur demands are not bounded independently: the commutator of the first
two layers is their coordinatewise product and lies in the denominator of
the third.  This file packages the exact finite statement checked by the
pair-top `product_triples` table.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Span of all coordinatewise products of vectors in two binary coordinate
subspaces. -/
def binaryCoordinateProductSpan {w : ℕ}
    (K W : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Submodule (ZMod 2) (Fin w → ZMod 2) :=
  Submodule.span (ZMod 2)
    {z | ∃ x ∈ K, ∃ y ∈ W, z = x * y}

namespace binaryCoordinateProductSpan

variable {w : ℕ}
  (K W : Submodule (ZMod 2) (Fin w → ZMod 2))

theorem product_mem (x : Fin w → ZMod 2) (hx : x ∈ K)
    (y : Fin w → ZMod 2) (hy : y ∈ W) :
    x * y ∈ binaryCoordinateProductSpan K W :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

/-- Bilinearity reduces product-span containment to products of spanning
families. -/
theorem le_of_basis_products
    {a b : ℕ}
    (v : Fin a → Fin w → ZMod 2)
    (u : Fin b → Fin w → ZMod 2)
    (hK : K = Submodule.span (ZMod 2) (Set.range v))
    (hW : W = Submodule.span (ZMod 2) (Set.range u))
    (L : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hproduct : ∀ i j, v i * u j ∈ L) :
    binaryCoordinateProductSpan K W ≤ L := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  rw [hK] at hx
  rw [hW] at hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, rfl⟩ := hy
          exact hproduct i j
      | zero => simpa using L.zero_mem
      | add y z _ _ hy hz =>
          simpa only [mul_add] using L.add_mem hy hz
      | smul c y _ hy =>
          simpa only [mul_smul_comm] using L.smul_mem c hy
  | zero => simpa using L.zero_mem
  | add x z _ _ hx hz =>
      simpa only [add_mul] using L.add_mem hx hz
  | smul c x _ hx =>
      simpa only [smul_mul_assoc] using L.smul_mem c hx

end binaryCoordinateProductSpan

/-- Sparse coordinate proof that a displayed space is exactly the product
span of two displayed binary coordinate spaces. -/
structure BinaryCoordinateProductCertificate
    {w a b d : ℕ}
    (K : BinaryCoordinateSpace w a)
    (W : BinaryCoordinateSpace w b)
    (P : BinaryCoordinateSpace w d) : Type where
  products_mem : ∀ i j,
    K.inclusion (Pi.single i 1) * W.inclusion (Pi.single j 1) ∈ P.space
  termCount : Fin d → ℕ
  leftIndex : ∀ j, Fin (termCount j) → Fin a
  rightIndex : ∀ j, Fin (termCount j) → Fin b
  basis_eq : ∀ j,
    P.inclusion (Pi.single j 1) =
      ∑ t, K.inclusion (Pi.single (leftIndex j t) 1) *
        W.inclusion (Pi.single (rightIndex j t) 1)

namespace BinaryCoordinateProductCertificate

variable {w a b d : ℕ}
  {K : BinaryCoordinateSpace w a}
  {W : BinaryCoordinateSpace w b}
  {P : BinaryCoordinateSpace w d}
  (C : BinaryCoordinateProductCertificate K W P)

theorem span_eq :
    binaryCoordinateProductSpan K.space W.space = P.space := by
  apply le_antisymm
  · apply binaryCoordinateProductSpan.le_of_basis_products
      K.space W.space
      (fun i ↦ K.inclusion (Pi.single i 1))
      (fun j ↦ W.inclusion (Pi.single j 1))
    · rw [K.space_eq_span_basis]
    · rw [W.space_eq_span_basis]
    · exact C.products_mem
  · apply P.le_of_basis_mem
    intro j
    rw [C.basis_eq j]
    apply Submodule.sum_mem
    intro t _
    exact binaryCoordinateProductSpan.product_mem K.space W.space
      _ ⟨Pi.single (C.leftIndex j t) 1, rfl⟩
      _ ⟨Pi.single (C.rightIndex j t) 1, rfl⟩

end BinaryCoordinateProductCertificate

universe uG uJ

variable {G : Type uG} {J : Type uJ} [Group G]
  {w : ℕ}
  (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
  (generators : J → G)
  (L : Subrepresentation rho)

/-- The product/commutator denominator inside one invariant state.  The
product span is supplied with its actual containment in `L`; the second
summand consists of literal retained-generator displacements. -/
def binaryCoupledDenominator
    (P : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hPL : P ≤ L.toSubmodule) : Submodule (ZMod 2) L.toSubmodule :=
  P.comap L.toSubmodule.subtype ⊔
    representationGeneratorDisplacementSpan rho generators L

/-- A sparse coordinate chart inside the product-plus-displacement
denominator.  A term is either a basis vector of the product space or one
literal retained-generator displacement in the upper state. -/
structure BinaryCoordinateCoupledDenominatorCertificate
    {p d : ℕ}
    (P : BinaryCoordinateSpace w p)
    (hPL : P.space ≤ L.toSubmodule)
    (D : BinaryCoordinateSpace w d) : Type (max 1 uJ) where
  space_le_state : D.space ≤ L.toSubmodule
  termCount : Fin d → ℕ
  term : ∀ j, Fin (termCount j) →
    Fin p ⊕ (J × L.toSubmodule)
  basis_eq : ∀ j,
    (⟨D.inclusion (Pi.single j 1),
      space_le_state ⟨Pi.single j 1, rfl⟩⟩ : L.toSubmodule) =
      ∑ t, match term j t with
        | Sum.inl i =>
            (⟨P.inclusion (Pi.single i 1),
              hPL ⟨Pi.single i 1, rfl⟩⟩ : L.toSubmodule)
        | Sum.inr iv =>
            (⟨rho (generators iv.1) iv.2.1 - iv.2.1,
              L.toSubmodule.sub_mem
                (L.apply_mem_toSubmodule (generators iv.1) iv.2.2)
                iv.2.2⟩ : L.toSubmodule)

namespace BinaryCoordinateCoupledDenominatorCertificate

variable {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  {generators : J → G} {L : Subrepresentation rho}
  {p d : ℕ} {P : BinaryCoordinateSpace w p}
  {hPL : P.space ≤ L.toSubmodule}
  {D : BinaryCoordinateSpace w d}
  (C : BinaryCoordinateCoupledDenominatorCertificate
    rho generators L P hPL D)

/-- The checked coordinate denominator lies in the semantic coupled
denominator. -/
theorem submoduleOf_le_denominator :
    D.submoduleOf L.toSubmodule C.space_le_state ≤
      binaryCoupledDenominator rho generators L P.space hPL := by
  apply D.submoduleOf_le_of_basis_mem L.toSubmodule C.space_le_state
  intro j
  rw [C.basis_eq j]
  apply Submodule.sum_mem
  intro t _
  cases hterm : C.term j t with
  | inl i =>
      apply (show P.space.comap L.toSubmodule.subtype ≤
          binaryCoupledDenominator rho generators L P.space hPL from
        le_sup_left)
      change P.inclusion (Pi.single i 1) ∈ P.space
      exact ⟨Pi.single i 1, rfl⟩
  | inr iv =>
      apply (show representationGeneratorDisplacementSpan rho generators L ≤
          binaryCoupledDenominator rho generators L P.space hPL from
        le_sup_right)
      exact Submodule.subset_span ⟨iv, rfl⟩

end BinaryCoordinateCoupledDenominatorCertificate

/-- A reversible coordinate subspace of `L` which is contained in the
literal product/commutator denominator gives an upper bound on the coupled
quotient dimension. -/
theorem binaryCoupledQuotient_finrank_le_of_coordinateSubspace
    [FiniteDimensional (ZMod 2) (Fin w → ZMod 2)]
    (P : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hPL : P ≤ L.toSubmodule)
    {d q : ℕ}
    (C : BinaryCoordinateSpace w d)
    (hCL : C.space ≤ L.toSubmodule)
    (hC : C.submoduleOf L.toSubmodule hCL ≤
      binaryCoupledDenominator rho generators L P hPL)
    (hcodim : Module.finrank (ZMod 2) L.toSubmodule ≤ d + q) :
    Module.finrank (ZMod 2)
        (L.toSubmodule ⟸ binaryCoupledDenominator rho generators L P hPL) ≤ q := by
  let D := binaryCoupledDenominator rho generators L P hPL
  have hdimC : Module.finrank (ZMod 2)
      (C.submoduleOf L.toSubmodule hCL) = d :=
    C.submoduleOf_finrank L.toSubmodule hCL
  have hdimD : d ≤ Module.finrank (ZMod 2) D := by
    rw [← hdimC]
    exact Submodule.finrank_mono hC
  have hquot := D.finrank_quotient_add_finrank
  omega

/-- A sparse displacement certificate gives the state-specific head bound
used in a coupled registry. -/
theorem representationCoinvariants_finrank_le_of_binaryCertificate
    [FiniteDimensional (ZMod 2) (Fin w → ZMod 2)]
    {d q : ℕ}
    (D : BinaryCoordinateSpace w d)
    (C : BinaryCoordinateDisplacementCertificate rho generators L D)
    (hcodim : Module.finrank (ZMod 2) L.toSubmodule ≤ d + q) :
    Module.finrank (ZMod 2) L.toRepresentation.Coinvariants ≤ q := by
  apply representationCoinvariants_finrank_le_of_displacementSubspace
    rho generators L C.submodule q C.le_generatorDisplacementSpan
  rw [C.finrank]
  exact hcodim

/-- A sparse coupled-denominator certificate gives the quotient-head
bound needed by the direct quartet-kernel estimate. -/
theorem binaryCoupledQuotient_finrank_le_of_binaryCertificate
    [FiniteDimensional (ZMod 2) (Fin w → ZMod 2)]
    {p d q : ℕ}
    (P : BinaryCoordinateSpace w p)
    (hPL : P.space ≤ L.toSubmodule)
    (D : BinaryCoordinateSpace w d)
    (C : BinaryCoordinateCoupledDenominatorCertificate
      rho generators L P hPL D)
    (hcodim : Module.finrank (ZMod 2) L.toSubmodule ≤ d + q) :
    Module.finrank (ZMod 2)
        (L.toSubmodule ⫽ binaryCoupledDenominator
          rho generators L P.space hPL) ≤ q :=
  binaryCoupledQuotient_finrank_le_of_coordinateSubspace
    rho generators L P.space hPL D C.space_le_state
    C.submoduleOf_le_denominator hcodim

/-- Complete finite coupled-head certificate on an invariant-state
registry.  It is the semantic target of the paired-eight product table. -/
structure BinaryInvariantCoupledHeadRegistry
    {I : Type*}
    (state : I → Subrepresentation rho)
    (cap : ℕ) : Type 1 where
  head : I → ℕ
  head_le : ∀ i,
    Module.finrank (ZMod 2) (state i).toRepresentation.Coinvariants ≤ head i
  productState : I → I → I
  product_eq : ∀ i j,
    binaryCoordinateProductSpan (state i).toSubmodule (state j).toSubmodule =
      (state (productState i j)).toSubmodule
  quotientHead : I → I → ℕ
  quotient_le : ∀ p ell
    (h : (state p).toSubmodule ≤ (state ell).toSubmodule),
    Module.finrank (ZMod 2)
      ((state ell).toSubmodule ⟸
        binaryCoupledDenominator rho generators (state ell)
          (state p).toSubmodule h) ≤ quotientHead p ell
  coupled_le : ∀ i j ell,
    (state (productState i j)).toSubmodule ≤ (state ell).toSubmodule →
    head i + head j + quotientHead (productState i j) ell ≤ cap

end SymmetricSubgroupAsymptotics

end
