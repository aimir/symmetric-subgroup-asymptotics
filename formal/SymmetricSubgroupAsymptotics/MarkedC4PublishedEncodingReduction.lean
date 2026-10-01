import SymmetricSubgroupAsymptotics.MarkedC4ProductEncoding

/-!
# Marked transport from the literal RDT encodings

The Roney--Dougal--Tracey reductions are unmarked injections.  Two numerical
features of those injections matter here: the number of unmarked code words
is `2^o(b^2)`, and the number of generators adjoined to a retained subgroup
is `o(b)`.  This file proves that these two published, one-variable facts
transport the complete `C4^r` weight with `o((b+r)^2)` loss, uniformly when
`r/b` is bounded.

In particular, no marked moment estimate is an input to either theorem below.
The factor `2^(2*r*l)` is proved by
`PermutationRelativeGeneratorEncoding.homMoment_sum_le`; the remaining work
is the uniform two-variable epsilon calculation.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- A nonnegative one-variable exponent is subquadratic. -/
def OneVariableSubquadratic (q : ℕ → ℝ) : Prop :=
  (∀ b, 0 ≤ q b) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℕ in atTop,
      q b ≤ ε * (b : ℝ) ^ 2

/-- A natural-valued generator budget is sublinear. -/
def OneVariableSublinear (l : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℕ in atTop,
    (l b : ℝ) ≤ ε * b

/-- The exact error contributed by an unmarked code of exponent `q` and at
most `l` retained relative generators. -/
def relativeGeneratorEncodingError
    (q : ℕ → ℝ) (l : ℕ → ℕ) (b r : ℕ) : ℝ :=
  q b + 2 * r * l b

theorem relativeGeneratorEncodingError_nonneg
    {q : ℕ → ℝ} {l : ℕ → ℕ}
    (hq : ∀ b, 0 ≤ q b) (b r : ℕ) :
    0 ≤ relativeGeneratorEncodingError q l b r := by
  unfold relativeGeneratorEncodingError
  exact add_nonneg (hq b) (by positivity)

/-- Subquadratic unmarked code size and sublinear relative generation give a
uniformly negligible marked error. -/
theorem relativeGeneratorEncodingError_negligible
    {q : ℕ → ℝ} {l : ℕ → ℕ}
    (hq : OneVariableSubquadratic q)
    (hl : OneVariableSublinear l) :
    UniformQuadraticNegligible (relativeGeneratorEncodingError q l) := by
  intro ε hε K
  have hquarter : 0 < ε / 4 := by positivity
  have hdenom : 0 < 4 * (|K| + 1) := by positivity
  filter_upwards [hq.2 (ε / 2) (by positivity),
      hl (ε / (4 * (|K| + 1))) (by positivity)] with b hqb hlb
  intro r hr
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hKr : (r : ℝ) ≤ |K| * b := by
    calc
      (r : ℝ) ≤ K * b := hr
      _ ≤ |K| * b := by
        exact mul_le_mul_of_nonneg_right (le_abs_self K) hb0
  have hlb' : (l b : ℝ) ≤ (ε / (4 * (|K| + 1))) * b := hlb
  have hmark : (2 : ℝ) * r * l b ≤ (ε / 2) * (b : ℝ) ^ 2 := by
    have hright : 0 ≤ (ε / (4 * (|K| + 1))) * (b : ℝ) := by positivity
    have hmul₁ : (r : ℝ) * l b ≤
        r * ((ε / (4 * (|K| + 1))) * b) :=
      mul_le_mul_of_nonneg_left hlb' hr0
    have hmul₂ : (r : ℝ) *
        ((ε / (4 * (|K| + 1))) * b) ≤
        (|K| * b) * ((ε / (4 * (|K| + 1))) * b) :=
      mul_le_mul_of_nonneg_right hKr hright
    have hmul : (r : ℝ) * l b ≤
        (|K| * b) * ((ε / (4 * (|K| + 1))) * b) :=
      hmul₁.trans hmul₂
    have hratio : |K| / (|K| + 1) ≤ 1 := by
      have habs : 0 ≤ |K| := abs_nonneg K
      rw [div_le_one (by positivity : 0 < |K| + 1)]
      linarith
    have hεratio : (ε / 2) * (|K| / (|K| + 1)) ≤ ε / 2 := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ ε / 2))
    calc
      (2 : ℝ) * r * l b ≤
          2 * (|K| * b) * ((ε / (4 * (|K| + 1))) * b) := by
        nlinarith
      _ = ((ε / 2) * (|K| / (|K| + 1))) * (b : ℝ) ^ 2 := by
        field_simp
        <;> ring
      _ ≤ (ε / 2) * (b : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hεratio (sq_nonneg _)
  have hbbr : (b : ℝ) ^ 2 ≤ ((b : ℝ) + r) ^ 2 := by
    nlinarith
  unfold relativeGeneratorEncodingError
  calc
    q b + 2 * (r : ℝ) * l b ≤
        (ε / 2) * (b : ℝ) ^ 2 +
          (ε / 2) * (b : ℝ) ^ 2 := add_le_add hqb hmark
    _ = ε * (b : ℝ) ^ 2 := by ring
    _ ≤ ε * ((b : ℝ) + r) ^ 2 :=
      mul_le_mul_of_nonneg_left hbbr hε.le

/-- A pointwise literal relative-generator encoding, together with an
unmarked code-space estimate, gives the exact multiplicative marked bound.
The target moment is arbitrary. -/
theorem relativeGeneratorEncoding_moment_le
    {b r l : ℕ} {q : ℝ}
    {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    {source : A → Subgroup (PermutationGroup b)}
    {target : B → Subgroup (PermutationGroup b)}
    (E : PermutationRelativeGeneratorEncoding b l A B X source target)
    (hq : (Fintype.card X : ℝ) ^ l ≤ (2 : ℝ) ^ q) :
    (∑ a : A,
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r) ≤
      (2 : ℝ) ^ (q + 2 * r * l) *
        ∑ z : B,
          (Nat.card (target z →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
  calc
    _ ≤ (Fintype.card X : ℝ) ^ l * (2 : ℝ) ^ (2 * r * l) *
        ∑ z : B,
          (Nat.card (target z →* Multiplicative (ZMod 4)) : ℝ) ^ r :=
      E.homMoment_sum_le r
    _ ≤ (2 : ℝ) ^ q * (2 : ℝ) ^ (2 * r * l) *
        ∑ z : B,
          (Nat.card (target z →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
      gcongr
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      push_cast
      ring

/-- The analogous exact transport for the odd-order/product coordinate.
Only the unmarked auxiliary code space is charged. -/
theorem productEncoding_moment_le
    {r : ℕ} {q : ℝ}
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {source : A → Type*} {target : B → Type*}
    [∀ a, Group (source a)] [∀ a, Finite (source a)]
    [∀ z, Group (target z)] [∀ z, Finite (target z)]
    (E : ProductEncoding A B C source target)
    (hq : (Fintype.card C : ℝ) ≤ (2 : ℝ) ^ q) :
    (∑ a : A,
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r) ≤
      (2 : ℝ) ^ q *
        ∑ z : B,
          (Nat.card (target z →* Multiplicative (ZMod 4)) : ℝ) ^ r := by
  exact (E.homMoment_sum_le r).trans
    (mul_le_mul_of_nonneg_right hq (Finset.sum_nonneg fun _ _ ↦ by positivity))

/-! ## Families of literal published encodings

The structures below deliberately store the finite source and target sets,
the literal encoding, and the two exact moment identities.  Thus a value of
either structure is unmarked combinatorial data: it contains no asymptotic
marked inequality.  The constructors following the structures are the only
place where the `C4^r` weight is transported.
-/

/-- One degree of an RDT relative-generator encoding. -/
structure RelativeGeneratorEncodingRow
    (sourceCount targetCount : ℕ → ℕ → ℝ)
    (q : ℕ → ℝ) (l b : ℕ) where
  A : Type
  B : Type
  X : Type
  fintypeA : Fintype A
  fintypeB : Fintype B
  fintypeX : Fintype X
  source : A → Subgroup (PermutationGroup b)
  target : B → Subgroup (PermutationGroup b)
  encoding : @PermutationRelativeGeneratorEncoding b l A B X
    fintypeA fintypeB fintypeX source target
  source_identity : ∀ r,
    sourceCount b r =
      (@Finset.univ A fintypeA).sum (fun a ↦
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r)
  target_identity : ∀ r,
    targetCount b r =
      (@Finset.univ B fintypeB).sum (fun z ↦
        (Nat.card (target z →* Multiplicative (ZMod 4)) : ℝ) ^ r)
  alphabet_bound : (Fintype.card X : ℝ) ^ l ≤ (2 : ℝ) ^ (q b)

namespace RelativeGeneratorEncodingRow

variable {sourceCount targetCount : ℕ → ℕ → ℝ}
  {q : ℕ → ℝ} {l b : ℕ}

/-- The exact marked inequality furnished by one literal row. -/
theorem bound
    (E : RelativeGeneratorEncodingRow sourceCount targetCount q l b)
    (r : ℕ) :
    sourceCount b r ≤ (2 : ℝ) ^ (q b + 2 * r * l) * targetCount b r := by
  letI : Fintype E.A := E.fintypeA
  letI : Fintype E.B := E.fintypeB
  letI : Fintype E.X := E.fintypeX
  rw [E.source_identity r, E.target_identity r]
  exact relativeGeneratorEncoding_moment_le E.encoding E.alphabet_bound

end RelativeGeneratorEncodingRow

/-- A degree-uniform family of the literal relative-generator rows appearing
in RDT.  Its hypotheses say only that the unmarked code exponent is
subquadratic and the retained generator budget is sublinear. -/
structure PublishedRelativeGeneratorReduction
    (sourceCount targetCount : ℕ → ℕ → ℝ) where
  q : ℕ → ℝ
  l : ℕ → ℕ
  q_subquadratic : OneVariableSubquadratic q
  l_sublinear : OneVariableSublinear l
  row : ∀ b, RelativeGeneratorEncodingRow sourceCount targetCount q (l b) b

namespace PublishedRelativeGeneratorReduction

variable {sourceCount targetCount : ℕ → ℕ → ℝ}

/-- Published literal relative-generator encodings imply the marked moment
reduction used by the global proof. -/
noncomputable def toMarkedMomentReduction
    (E : PublishedRelativeGeneratorReduction sourceCount targetCount) :
    MarkedMomentReduction sourceCount targetCount where
  error := relativeGeneratorEncodingError E.q E.l
  error_nonneg := relativeGeneratorEncodingError_nonneg E.q_subquadratic.1
  negligible := relativeGeneratorEncodingError_negligible
    E.q_subquadratic E.l_sublinear
  bound := fun b r ↦ E.row b |>.bound r

end PublishedRelativeGeneratorReduction

/-- One degree of an RDT product encoding. -/
structure ProductEncodingRow
    (sourceCount targetCount : ℕ → ℕ → ℝ)
    (q : ℕ → ℝ) (b : ℕ) where
  A : Type
  B : Type
  C : Type
  fintypeA : Fintype A
  fintypeB : Fintype B
  fintypeC : Fintype C
  source : A → Type
  target : B → Type
  sourceGroup : ∀ a, Group (source a)
  sourceFinite : ∀ a, Finite (source a)
  targetGroup : ∀ z, Group (target z)
  targetFinite : ∀ z, Finite (target z)
  encoding : @ProductEncoding A B C fintypeA fintypeB fintypeC
    source target sourceGroup sourceFinite targetGroup targetFinite
  source_identity : ∀ r,
    sourceCount b r =
      (@Finset.univ A fintypeA).sum (fun a ↦
        (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ) ^ r)
  target_identity : ∀ r,
    targetCount b r =
      (@Finset.univ B fintypeB).sum (fun z ↦
        (Nat.card (target z →* Multiplicative (ZMod 4)) : ℝ) ^ r)
  auxiliary_bound : (Fintype.card C : ℝ) ≤ (2 : ℝ) ^ (q b)

namespace ProductEncodingRow

variable {sourceCount targetCount : ℕ → ℕ → ℝ}
  {q : ℕ → ℝ} {b : ℕ}

/-- The exact marked inequality furnished by one literal product row. -/
theorem bound (E : ProductEncodingRow sourceCount targetCount q b) (r : ℕ) :
    sourceCount b r ≤ (2 : ℝ) ^ (q b) * targetCount b r := by
  letI : Fintype E.A := E.fintypeA
  letI : Fintype E.B := E.fintypeB
  letI : Fintype E.C := E.fintypeC
  letI (a : E.A) : Group (E.source a) := E.sourceGroup a
  letI (a : E.A) : Finite (E.source a) := E.sourceFinite a
  letI (z : E.B) : Group (E.target z) := E.targetGroup z
  letI (z : E.B) : Finite (E.target z) := E.targetFinite z
  rw [E.source_identity r, E.target_identity r]
  exact productEncoding_moment_le E.encoding E.auxiliary_bound

end ProductEncodingRow

/-- A degree-uniform family of RDT product encodings. -/
structure PublishedProductReduction
    (sourceCount targetCount : ℕ → ℕ → ℝ) where
  q : ℕ → ℝ
  q_subquadratic : OneVariableSubquadratic q
  row : ∀ b, ProductEncodingRow sourceCount targetCount q b

namespace PublishedProductReduction

variable {sourceCount targetCount : ℕ → ℕ → ℝ}

/-- Published literal product encodings imply the marked moment reduction
used by the global proof. -/
noncomputable def toMarkedMomentReduction
    (E : PublishedProductReduction sourceCount targetCount) :
    MarkedMomentReduction sourceCount targetCount where
  error := fun b _r ↦ E.q b
  error_nonneg := fun b _r ↦ E.q_subquadratic.1 b
  negligible := by
    intro ε hε K
    filter_upwards [E.q_subquadratic.2 ε hε] with b hb
    intro r hr
    exact hb.trans (mul_le_mul_of_nonneg_left
      (by
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith)
      hε.le)
  bound := fun b r ↦ E.row b |>.bound r

end PublishedProductReduction

/-- The two literal encodings in RDT's fixed-cutoff step: first retain a
nilpotent core and a sublinear list of relative generators, then separate
the nilpotent core into its binary word and an unmarked odd-order code.
The intermediate count is exposed so that neither step is hidden in a
weighted hypothesis. -/
structure PublishedFixedCutoffReduction
    (sourceCount targetCount : ℕ → ℕ → ℝ) where
  middleCount : ℕ → ℕ → ℝ
  relative : PublishedRelativeGeneratorReduction sourceCount middleCount
  product : PublishedProductReduction middleCount targetCount

namespace PublishedFixedCutoffReduction

variable {sourceCount targetCount : ℕ → ℕ → ℝ}

/-- The fixed-cutoff encoding chain gives the required marked reduction. -/
noncomputable def toMarkedMomentReduction
    (E : PublishedFixedCutoffReduction sourceCount targetCount) :
    MarkedMomentReduction sourceCount targetCount :=
  E.relative.toMarkedMomentReduction.trans
    E.product.toMarkedMomentReduction

end PublishedFixedCutoffReduction

/-- Literal large-orbit encodings from RDT Proposition 6.2 and Theorem 6.4.

For a selected cutoff `C`, `q C b` is the logarithmic size of the unmarked
container/partition code and `l C b` is the number of displayed relative
generators.  The last field is precisely the numerical content of the
published generator and container estimates.  It does not mention a marked
moment: the factor `2*r*l` is inserted below by the generic transport
theorem. -/
structure PublishedLargeOrbitEncoding
    (smallSourceCount : ℕ → ℕ → ℕ → ℝ) where
  q : ℕ → ℕ → ℝ
  l : ℕ → ℕ → ℕ
  row : ∀ C b, RelativeGeneratorEncodingRow
    solubleMarkedC4Moment (smallSourceCount C) (q C) (l C b) b
  cutoff : ∀ δ : ℝ, 0 < δ → ∀ K : ℝ,
    ∃ C : ℕ, ∀ᶠ b : ℕ in atTop,
      q C b + 2 * |K| * b * l C b ≤ δ * (b : ℝ) ^ 2

namespace PublishedLargeOrbitEncoding

variable {smallSourceCount : ℕ → ℕ → ℕ → ℝ}

/-- The published unmarked large-orbit code transports the full `C4^r`
weight uniformly on every bounded `r/b` window. -/
theorem marked_bound (E : PublishedLargeOrbitEncoding smallSourceCount)
    (δ : ℝ) (hδ : 0 < δ) (K : ℝ) :
    ∃ C : ℕ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ K * b →
      solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) * smallSourceCount C b r := by
  obtain ⟨C, hC⟩ := E.cutoff δ hδ K
  refine ⟨C, ?_⟩
  filter_upwards [hC] with b hb
  intro r hr
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hKr : (r : ℝ) ≤ |K| * b := by
    exact hr.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hb0)
  have hl0 : (0 : ℝ) ≤ E.l C b := Nat.cast_nonneg _
  have hmark : (2 : ℝ) * r * E.l C b ≤ 2 * |K| * b * E.l C b := by
    nlinarith [mul_le_mul_of_nonneg_right hKr hl0]
  have herror : E.q C b + 2 * (r : ℝ) * E.l C b ≤
      δ * ((b : ℝ) + r) ^ 2 := by
    have hsquare : (b : ℝ) ^ 2 ≤ ((b : ℝ) + r) ^ 2 := by
      nlinarith
    calc
      E.q C b + 2 * (r : ℝ) * E.l C b ≤
          E.q C b + 2 * |K| * b * E.l C b :=
        by linarith
      _ ≤ δ * (b : ℝ) ^ 2 := hb
      _ ≤ δ * ((b : ℝ) + r) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hδ.le
  calc
    solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ (E.q C b + 2 * r * E.l C b) *
          smallSourceCount C b r := (E.row C b).bound r
    _ ≤ (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) *
          smallSourceCount C b r := by
      have htarget : 0 ≤ smallSourceCount C b r := by
        let R := E.row C b
        letI : Fintype R.B := R.fintypeB
        rw [R.target_identity r]
        exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) herror) htarget

end PublishedLargeOrbitEncoding

end MarkedC4
end SymmetricSubgroupAsymptotics

end
