import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

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

/-- Coordinatewise product spans of invariant subspaces remain invariant
under a permutation action. -/
theorem apply_mem
    {G : Type*} [Group G] [MulAction G (Fin w)]
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w))) (g : G)
    (z : Fin w → ZMod 2)
    (hz : z ∈ binaryCoordinateProductSpan A.toSubmodule B.toSubmodule) :
    permutationFunctionRepresentation (ZMod 2) G (Fin w) g z ∈
      binaryCoordinateProductSpan A.toSubmodule B.toSubmodule := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hmul :
          permutationFunctionRepresentation (ZMod 2) G (Fin w) g (x * y) =
            permutationFunctionRepresentation (ZMod 2) G (Fin w) g x *
              permutationFunctionRepresentation (ZMod 2) G (Fin w) g y := rfl
      rw [hmul]
      exact product_mem A.toSubmodule B.toSubmodule
        _ (A.apply_mem_toSubmodule g hx)
        _ (B.apply_mem_toSubmodule g hy)
  | zero => simpa only [map_zero] using
      (binaryCoordinateProductSpan A.toSubmodule B.toSubmodule).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using
      (binaryCoordinateProductSpan A.toSubmodule B.toSubmodule).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using
      (binaryCoordinateProductSpan A.toSubmodule B.toSubmodule).smul_mem a hx

/-- The product span as an actual subrepresentation of the natural
permutation module. -/
def subrepresentation
    {G : Type*} [Group G] [MulAction G (Fin w)]
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w))) :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin w)) where
  toSubmodule := binaryCoordinateProductSpan A.toSubmodule B.toSubmodule
  apply_mem_toSubmodule g _ hz :=
    apply_mem A B g _ hz

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

include C

theorem span_eq :
    binaryCoordinateProductSpan K.space W.space = P.space := by
  apply le_antisymm
  · apply binaryCoordinateProductSpan.le_of_basis_products
      K.space W.space
      (fun i ↦ K.inclusion (Pi.single i 1))
      (fun j ↦ W.inclusion (Pi.single j 1))
    · rw [K.space_eq_span_basis]
    · rw [W.space_eq_span_basis]
    · exact BinaryCoordinateProductCertificate.products_mem C
  · apply P.le_of_basis_mem
    intro j
    rw [BinaryCoordinateProductCertificate.basis_eq C j]
    apply Submodule.sum_mem
    intro t _
    exact binaryCoordinateProductSpan.product_mem K.space W.space
      _ ⟨Pi.single (C.leftIndex j t) 1, rfl⟩
      _ ⟨Pi.single (C.rightIndex j t) 1, rfl⟩

end BinaryCoordinateProductCertificate

universe uG uJ uI

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

/-- For a generating tuple, the coupled denominator is literally the
product subspace plus the full coinvariant-relation subspace of `L`. -/
theorem binaryCoupledDenominator_eq_sup_coinvariantsKer
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (P : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hPL : P ≤ L.toSubmodule) :
    binaryCoupledDenominator rho generators L P hPL =
      P.comap L.toSubmodule.subtype ⊔
        Representation.Coinvariants.ker L.toRepresentation := by
  rw [binaryCoupledDenominator,
    representationGeneratorDisplacementSpan_eq_coinvariantsKer
      rho generators hgen L]

/-- For a permutation module, the intrinsic product-plus-coinvariant
denominator is an invariant subspace of the upper state. -/
def binaryIntrinsicCoupledDenominatorSubrepresentation
    [MulAction G (Fin w)]
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) : Subrepresentation L.toRepresentation := by
  let P : Subrepresentation L.toRepresentation := {
    toSubmodule :=
      (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule).comap
        L.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g z hz
      change permutationFunctionRepresentation (ZMod 2) G (Fin w) g z.1 ∈
        binaryCoordinateProductSpan
        K.toSubmodule W.toSubmodule
      apply binaryCoordinateProductSpan.apply_mem K W g z.1
      exact hz }
  let C : Subrepresentation L.toRepresentation := {
    toSubmodule := Representation.Coinvariants.ker L.toRepresentation
    apply_mem_toSubmodule := by
      intro g z hz
      exact representationCoinvariantsKer_apply_mem
        L.toRepresentation g z hz }
  exact P ⊔ C

@[simp] theorem binaryIntrinsicCoupledDenominatorSubrepresentation_toSubmodule
    [MulAction G (Fin w)]
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) :
    (binaryIntrinsicCoupledDenominatorSubrepresentation
      K W L hproduct).toSubmodule =
      (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule).comap
          L.toSubmodule.subtype ⊔
        Representation.Coinvariants.ker L.toRepresentation :=
  rfl

/-- Once the recorded tuple generates the action group, the literal
product-plus-recorded-displacement denominator is itself an invariant
subrepresentation. -/
def binaryCoupledDenominatorSubrepresentation
    [MulAction G (Fin w)]
    (generators : J → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) : Subrepresentation L.toRepresentation where
  toSubmodule := binaryCoupledDenominator
    (permutationFunctionRepresentation (ZMod 2) G (Fin w)) generators L
    (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule) hproduct
  apply_mem_toSubmodule g _ hz := by
    rw [binaryCoupledDenominator_eq_sup_coinvariantsKer
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)) generators L hgen
      (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule) hproduct]
      at hz ⊢
    exact (binaryIntrinsicCoupledDenominatorSubrepresentation
      K W L hproduct).apply_mem_toSubmodule g hz

theorem binaryCoupledDenominatorSubrepresentation_eq_intrinsic
    [MulAction G (Fin w)]
    (generators : J → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) :
    binaryCoupledDenominatorSubrepresentation
        generators hgen K W L hproduct =
      binaryIntrinsicCoupledDenominatorSubrepresentation
        K W L hproduct := by
  apply Subrepresentation.toSubmodule_injective
  exact binaryCoupledDenominator_eq_sup_coinvariantsKer
    (permutationFunctionRepresentation (ZMod 2) G (Fin w)) generators L hgen
      (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule) hproduct

/-- The quotient representation whose denominator is the literal finite
table expression `KW +` recorded-generator displacements. -/
def binaryCoupledQuotientRepresentation
    [MulAction G (Fin w)]
    (generators : J → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) :
    Representation (ZMod 2) G
      (L.toSubmodule ⧸
        (binaryCoupledDenominatorSubrepresentation
          generators hgen K W L hproduct).toSubmodule) :=
  let D := binaryCoupledDenominatorSubrepresentation
    generators hgen K W L hproduct
  L.toRepresentation.quotient D.toSubmodule
    (fun g ↦ D.apply_mem_toSubmodule g)

/-- The literal table quotient is pointwise fixed by the original action. -/
@[simp] theorem binaryCoupledQuotientRepresentation_apply
    [MulAction G (Fin w)]
    (generators : J → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule)
    (g : G)
    (z : (binaryCoupledQuotientRepresentation
      generators hgen K W L hproduct).asModule) :
    binaryCoupledQuotientRepresentation
        generators hgen K W L hproduct g z = z := by
  let D := binaryCoupledDenominatorSubrepresentation
    generators hgen K W L hproduct
  change (L.toRepresentation.quotient D.toSubmodule
      (fun h ↦ D.apply_mem_toSubmodule h)) g z = z
  refine Submodule.Quotient.induction_on D.toSubmodule z ?_
  intro v
  change D.toSubmodule.mkQ (L.toRepresentation g v) =
    D.toSubmodule.mkQ v
  apply (Submodule.Quotient.eq D.toSubmodule).mpr
  change L.toRepresentation g v - v ∈
    binaryCoupledDenominator
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)) generators L
      (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule) hproduct
  rw [binaryCoupledDenominator_eq_sup_coinvariantsKer
    (permutationFunctionRepresentation (ZMod 2) G (Fin w)) generators L hgen
    (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule) hproduct]
  exact Submodule.mem_sup_right
    (Representation.Coinvariants.sub_mem_ker
      (ρ := L.toRepresentation) g v)

/-- The residual upper-layer representation after dividing by both the
cross-layer product and every intrinsic coinvariant relation. -/
def binaryIntrinsicCoupledQuotientRepresentation
    [MulAction G (Fin w)]
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) :
    Representation (ZMod 2) G
      (L.toSubmodule ⧸
        (binaryIntrinsicCoupledDenominatorSubrepresentation
          K W L hproduct).toSubmodule) :=
  let D := binaryIntrinsicCoupledDenominatorSubrepresentation
    K W L hproduct
  L.toRepresentation.quotient D.toSubmodule
    (fun g ↦ D.apply_mem_toSubmodule g)

/-- The residual coupled quotient is an actual trivial representation: its
denominator contains every displacement of the upper state. -/
@[simp] theorem binaryIntrinsicCoupledQuotientRepresentation_apply
    [MulAction G (Fin w)]
    (K W L : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G (Fin w)))
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule)
    (g : G)
    (z : L.toSubmodule ⧸
      (binaryIntrinsicCoupledDenominatorSubrepresentation
        K W L hproduct).toSubmodule) :
    binaryIntrinsicCoupledQuotientRepresentation
        K W L hproduct g z = z := by
  let D := binaryIntrinsicCoupledDenominatorSubrepresentation
    K W L hproduct
  change (L.toRepresentation.quotient D.toSubmodule
      (fun h ↦ D.apply_mem_toSubmodule h)) g z = z
  refine Submodule.Quotient.induction_on D.toSubmodule z ?_
  intro v
  change D.toSubmodule.mkQ (L.toRepresentation g v) =
    D.toSubmodule.mkQ v
  apply (Submodule.Quotient.eq D.toSubmodule).mpr
  change L.toRepresentation g v - v ∈
    (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule).comap
        L.toSubmodule.subtype ⊔
      Representation.Coinvariants.ker L.toRepresentation
  exact Submodule.mem_sup_right
    (Representation.Coinvariants.sub_mem_ker
      (ρ := L.toRepresentation) g v)

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
        (L.toSubmodule ⧸ binaryCoupledDenominator rho generators L P hPL) ≤ q := by
  let D := binaryCoupledDenominator rho generators L P hPL
  have hdimC : Module.finrank (ZMod 2)
      (C.submoduleOf L.toSubmodule hCL) = d :=
    C.submoduleOf_finrank L.toSubmodule hCL
  have hdimD : d ≤ Module.finrank (ZMod 2) D := by
    rw [← hdimC]
    exact Submodule.finrank_mono hC
  have hquot := D.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (L.toSubmodule ⧸ D) ≤ q
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
        (L.toSubmodule ⧸ binaryCoupledDenominator
          rho generators L P.space hPL) ≤ q :=
  binaryCoupledQuotient_finrank_le_of_coordinateSubspace
    rho generators L P.space hPL D C.space_le_state
    C.submoduleOf_le_denominator hcodim

/-- Complete finite coupled-head certificate on an invariant-state
registry.  It is the semantic target of the paired-eight product table. -/
structure BinaryInvariantCoupledHeadRegistry
    {I : Type uI}
    (state : I → Subrepresentation rho)
    (cap : ℕ) : Type (max 1 uI) where
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
      ((state ell).toSubmodule ⧸
        binaryCoupledDenominator rho generators (state ell)
          (state p).toSubmodule h) ≤ quotientHead p ell
  coupled_le : ∀ i j ell,
    (state (productState i j)).toSubmodule ≤ (state ell).toSubmodule →
    head i + head j + quotientHead (productState i j) ell ≤ cap

namespace BinaryInvariantCoupledHeadRegistry

variable {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  {generators : J → G} {I : Type*}
  {state : I → Subrepresentation rho} {cap : ℕ}
  (C : BinaryInvariantCoupledHeadRegistry rho generators state cap)

include C

/-- A complete coupled registry proves the paper's three-head inequality
for arbitrary actual invariant submodules, after the semantic objects have
been located in the finite registry. -/
theorem finrank_add_finrank_add_quotient_le
    (complete : ∀ W : Subrepresentation rho, ∃ i, state i = W)
    (K W L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) :
    Module.finrank (ZMod 2) K.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2) W.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          (L.toSubmodule ⧸
            binaryCoupledDenominator rho generators L
              (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule)
              hproduct) ≤ cap := by
  obtain ⟨i, rfl⟩ := complete K
  obtain ⟨j, rfl⟩ := complete W
  obtain ⟨ell, rfl⟩ := complete L
  let p := C.productState i j
  have hP : (state p).toSubmodule ≤ (state ell).toSubmodule := by
    rw [← C.product_eq i j]
    exact hproduct
  have hK := C.head_le i
  have hW := C.head_le j
  have hL := C.quotient_le p ell hP
  have hsum := C.coupled_le i j ell hP
  have hdenom :
      binaryCoupledDenominator rho generators (state ell)
          (binaryCoordinateProductSpan (state i).toSubmodule
            (state j).toSubmodule) hproduct =
        binaryCoupledDenominator rho generators (state ell)
          (state p).toSubmodule hP := by
    simp only [binaryCoupledDenominator]
    rw [C.product_eq i j]
  rw [hdenom]
  exact (Nat.add_le_add (Nat.add_le_add hK hW) hL).trans hsum

end BinaryInvariantCoupledHeadRegistry

/-- A coupled head table together with semantic completeness of its state
registry. -/
structure BinaryInvariantCompleteCoupledHeadRegistry
    {I : Type uI}
    (state : I → Subrepresentation rho)
    (cap : ℕ) : Type (max 1 uI) where
  coupled : BinaryInvariantCoupledHeadRegistry rho generators state cap
  complete : ∀ W : Subrepresentation rho, ∃ i, state i = W

namespace BinaryInvariantCompleteCoupledHeadRegistry

variable {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  {generators : J → G} {I : Type*}
  {state : I → Subrepresentation rho} {cap : ℕ}
  (C : BinaryInvariantCompleteCoupledHeadRegistry
    rho generators state cap)

include C

theorem finrank_add_finrank_add_quotient_le
    (K W L : Subrepresentation rho)
    (hproduct : binaryCoordinateProductSpan K.toSubmodule W.toSubmodule ≤
      L.toSubmodule) :
    Module.finrank (ZMod 2) K.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2) W.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          (L.toSubmodule ⧸
            binaryCoupledDenominator rho generators L
              (binaryCoordinateProductSpan K.toSubmodule W.toSubmodule)
              hproduct) ≤ cap :=
  C.coupled.finrank_add_finrank_add_quotient_le C.complete K W L hproduct

end BinaryInvariantCompleteCoupledHeadRegistry

end SymmetricSubgroupAsymptotics

end
