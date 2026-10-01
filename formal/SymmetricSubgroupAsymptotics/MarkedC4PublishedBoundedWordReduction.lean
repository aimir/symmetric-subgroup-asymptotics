import SymmetricSubgroupAsymptotics.MarkedC4BoundedWordAssembly
import SymmetricSubgroupAsymptotics.MarkedC4CaseIComplete
import SymmetricSubgroupAsymptotics.MarkedC4CaseIIPeel
import SymmetricSubgroupAsymptotics.MarkedC4PublishedCaseIEncoding
import SymmetricSubgroupAsymptotics.MarkedC4PublishedCaseIIEncoding

/-!
# The published RDT bounded-word rows imply the marked recurrence

Proposition 7.4 of Roney-Dougal--Tracey partitions a bounded binary word into
two cases.  In Case I its proof retains a sorted lower-coordinate tableau and
the two source columns used by the final abelian Hall count.  In Case II it
retains the excessive factor, the two residual supports and the two generator
ranks used in Theorems 4.6 and 5.7.

The structures in this file record those *unoptimized* enumeration rows.
They contain neither `markedF` nor a marked-moment conclusion.  The auxiliary
integer `r` enters only because the already-proved Hall enumeration is applied
after adjoining the literal `C4^r` coordinates.  The numerical theorems
`caseI_entropy_add_compressedHall_le` and
`caseII_epimorphism_cost_le_markedF_reserve` prove the marked estimates here.

Thus the eventual RDT interface may cite the literal rows in the published
proof, while the new marked conclusion remains a theorem of this project.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- The unoptimized exponent appearing in one Case-I row. -/
def publishedCaseIExponent
    (c n d : ℕ → ℝ) (t : ℕ)
    (a r sourceFirst sourceSecond : ℝ) : ℝ :=
  (∑ m ∈ Finset.range t,
      ∑ j ∈ Finset.range m, (c m - c j) * n j * d m) +
    psi (a / 2 + r) sourceFirst + psi r sourceSecond

/-- One literal Case-I tableau row from the proof of RDT Proposition 7.4.
`enumeration` is the pre-optimization Goursat/Hall enumeration.  Its exponent
is displayed in `publishedCaseIExponent`, rather than bounded by `markedF`.
-/
structure PublishedBoundedWordCaseIRow
    (caseI : ℝ) (A : ℝ) (b r : ℕ) where
  c : ℕ → ℝ
  n : ℕ → ℝ
  d : ℕ → ℝ
  t : ℕ
  a : ℝ
  sourceFirst : ℝ
  sourceSecond : ℝ
  a_nonneg : 0 ≤ a
  sourceFirst_nonneg : 0 ≤ sourceFirst
  sourceSecond_nonneg : 0 ≤ sourceSecond
  sourceSecond_le_first : sourceSecond ≤ sourceFirst
  first_cap : sourceFirst ≤ ∑ m ∈ Finset.range t, d m
  joint_cap : sourceFirst + sourceSecond ≤
    ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m)
  n_nonneg : ∀ m < t, 0 ≤ n m
  c_nonneg : ∀ m < t, 0 ≤ c m
  c_le_one : ∀ m < t, c m ≤ 1
  c_mono : ∀ j m, j ≤ m → m < t → c j ≤ c m
  d_nonneg : ∀ m < t, 0 ≤ d m
  d_le_quarter : ∀ m < t, d m ≤ n m / 4
  d_le_density : ∀ m < t, d m ≤ c m * n m
  degree_eq : a + prefixWeight n t = (b : ℝ)
  enumeration : caseI ≤
    (2 : ℝ) ^ publishedCaseIExponent c n d t a r sourceFirst sourceSecond *
      (((b : ℝ) + r + 2) ^ A)

namespace PublishedBoundedWordCaseIRow

/-- The retained two-column tableau estimate turns the published Case-I row
into the exact marked main term. -/
theorem bound
    {caseI A : ℝ} {b r : ℕ}
    (D : PublishedBoundedWordCaseIRow caseI A b r) :
    caseI ≤ markedBase b r * (((b : ℝ) + r + 2) ^ A) := by
  have hexp : publishedCaseIExponent D.c D.n D.d D.t D.a r
      D.sourceFirst D.sourceSecond ≤ markedF b r := by
    have h := caseI_entropy_add_compressedHall_le
      D.c D.n D.d D.t D.a_nonneg (Nat.cast_nonneg r)
      D.sourceFirst_nonneg D.sourceSecond_nonneg D.sourceSecond_le_first
      D.first_cap D.joint_cap D.n_nonneg D.c_nonneg D.c_le_one D.c_mono
      D.d_nonneg D.d_le_quarter D.d_le_density
    rw [D.degree_eq] at h
    simpa only [publishedCaseIExponent] using h
  have hpow :
      (2 : ℝ) ^ publishedCaseIExponent D.c D.n D.d D.t D.a r
          D.sourceFirst D.sourceSecond ≤ markedBase b r := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  exact D.enumeration.trans
    (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _))

end PublishedBoundedWordCaseIRow

/-- The unoptimized epimorphism exponent in one excessive-factor peel. -/
def publishedCaseIIPeelExponent
    (z dSource g dNormal : ℝ) : ℝ :=
  z * dSource + g * dNormal

/-- One literal excessive-factor row from Case II of RDT Proposition 7.4.
The field `enumeration` is the output of the published epimorphism count
before completing the marked square. -/
structure PublishedBoundedWordCaseIIPeelRow
    (count : ℕ → ℕ → ℝ) (peel : ℝ) (A : ℝ) (b k r : ℕ) where
  e : ℝ
  z : ℝ
  g : ℝ
  w : ℝ
  bThree : ℝ
  bFour : ℝ
  dSource : ℝ
  dNormal : ℝ
  z_nonneg : 0 ≤ z
  g_nonneg : 0 ≤ g
  bThree_nonneg : 0 ≤ bThree
  bFour_nonneg : 0 ≤ bFour
  residual_width : bThree + bFour = (b : ℝ) - w
  remaining_degree : (k : ℝ) = (b : ℝ) - w
  excessive : e * z + g ≤ w / 2
  z_cap : z ≤ w / 4
  source_rank : dSource ≤ e * bThree / 4 + bFour / 2 + r
  normal_rank : dNormal ≤ bThree / 4
  enumeration : peel ≤
    (2 : ℝ) ^ publishedCaseIIPeelExponent z dSource g dNormal *
      (((b : ℝ) + r + 2) ^ A) * count k r

namespace PublishedBoundedWordCaseIIPeelRow

private theorem markedBase_eq_mul
    {b k r : ℕ} {w : ℝ} (hk : (k : ℝ) = (b : ℝ) - w) :
    markedBase b r =
      (2 : ℝ) ^ (markedF b r - markedF k r) * markedBase k r := by
  unfold markedBase
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  rw [hk]
  ring

/-- Square completion converts the published excessive-factor exponent into
one exact normalized peel of the marked recurrence. -/
theorem bound
    {count : ℕ → ℕ → ℝ} {peel A : ℝ} {b k r : ℕ}
    (D : PublishedBoundedWordCaseIIPeelRow count peel A b k r)
    (hcount : 0 ≤ count k r) :
    peel ≤ markedBase b r * (((b : ℝ) + r + 2) ^ A) *
      (count k r / markedBase k r) := by
  have hcost : publishedCaseIIPeelExponent D.z D.dSource D.g D.dNormal ≤
      markedF b r - markedF k r := by
    have h := caseII_epimorphism_cost_le_markedF_reserve
      D.z_nonneg D.g_nonneg D.bThree_nonneg D.bFour_nonneg
      (Nat.cast_nonneg r) D.residual_width D.excessive D.z_cap
      D.source_rank D.normal_rank
    rw [← D.remaining_degree] at h
    simpa only [publishedCaseIIPeelExponent] using h
  have hpow :
      (2 : ℝ) ^ publishedCaseIIPeelExponent D.z D.dSource D.g D.dNormal ≤
        (2 : ℝ) ^ (markedF b r - markedF k r) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hcost
  have hpoly : 0 ≤ (((b : ℝ) + r + 2) ^ A) :=
    Real.rpow_nonneg (by positivity) _
  have hstep := mul_le_mul_of_nonneg_right hpow (mul_nonneg hpoly hcount)
  calc
    peel ≤ (2 : ℝ) ^ publishedCaseIIPeelExponent D.z D.dSource D.g D.dNormal *
        (((b : ℝ) + r + 2) ^ A) * count k r := D.enumeration
    _ ≤ (2 : ℝ) ^ (markedF b r - markedF k r) *
        (((b : ℝ) + r + 2) ^ A) * count k r := by
      simpa only [mul_assoc] using hstep
    _ = markedBase b r * (((b : ℝ) + r + 2) ^ A) *
        (count k r / markedBase k r) := by
      rw [markedBase_eq_mul D.remaining_degree]
      have hkpos := markedBase_pos k r
      field_simp [hkpos.ne']

end PublishedBoundedWordCaseIIPeelRow

/-! ## The literal Case-I input -/

/-- All data for one physical degree in Case I.  Unlike
`PublishedBoundedWordCaseIRow`, this structure is independent of the mark
count `r`.  Its only counting datum is the finite injection into the actual
Hall fibres; `row` below derives the former `enumeration` field for every
`r`.
-/
structure PublishedBoundedWordLiteralCaseI
    (caseI : ℕ → ℝ) (A : ℝ) (b : ℕ) where
  c : ℕ → ℝ
  n : ℕ → ℝ
  d : ℕ → ℝ
  t : ℕ
  a : ℝ
  sourceFirst : ℝ
  sourceSecond : ℝ
  A₀ : ℝ
  A_eq : A = A₀ + 6
  A₀_nonneg : 0 ≤ A₀
  a_nonneg : 0 ≤ a
  a_le_degree : a ≤ b
  sourceFirst_nonneg : 0 ≤ sourceFirst
  sourceSecond_nonneg : 0 ≤ sourceSecond
  sourceSecond_le_first : sourceSecond ≤ sourceFirst
  first_cap : sourceFirst ≤ ∑ m ∈ Finset.range t, d m
  joint_cap : sourceFirst + sourceSecond ≤
    ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m)
  n_nonneg : ∀ m < t, 0 ≤ n m
  c_nonneg : ∀ m < t, 0 ≤ c m
  c_le_one : ∀ m < t, c m ≤ 1
  c_mono : ∀ j m, j ≤ m → m < t → c j ≤ c m
  d_nonneg : ∀ m < t, 0 ≤ d m
  d_le_quarter : ∀ m < t, d m ≤ n m / 4
  d_le_density : ∀ m < t, d m ≤ c m * n m
  degree_eq : a + prefixWeight n t = (b : ℝ)
  encoding : PublishedCaseIHallEncoding caseI a sourceFirst sourceSecond
    (∑ m ∈ Finset.range t,
      ∑ j ∈ Finset.range m, (c m - c j) * n j * d m)
    A₀ b

namespace PublishedBoundedWordLiteralCaseI

/-- The literal finite Hall encoding supplies the old row for every `r`.
The marked Hall exponent and all polynomial losses are conclusions. -/
noncomputable def row
    {caseI : ℕ → ℝ} {A : ℝ} {b : ℕ}
    (D : PublishedBoundedWordLiteralCaseI caseI A b) (r : ℕ) :
    PublishedBoundedWordCaseIRow (caseI r) A b r where
  c := D.c
  n := D.n
  d := D.d
  t := D.t
  a := D.a
  sourceFirst := D.sourceFirst
  sourceSecond := D.sourceSecond
  a_nonneg := D.a_nonneg
  sourceFirst_nonneg := D.sourceFirst_nonneg
  sourceSecond_nonneg := D.sourceSecond_nonneg
  sourceSecond_le_first := D.sourceSecond_le_first
  first_cap := D.first_cap
  joint_cap := D.joint_cap
  n_nonneg := D.n_nonneg
  c_nonneg := D.c_nonneg
  c_le_one := D.c_le_one
  c_mono := D.c_mono
  d_nonneg := D.d_nonneg
  d_le_quarter := D.d_le_quarter
  d_le_density := D.d_le_density
  degree_eq := D.degree_eq
  enumeration := by
    have h := D.encoding.bound D.a_nonneg D.a_le_degree D.A₀_nonneg r
    simpa only [publishedCaseIExponent, D.A_eq] using h

end PublishedBoundedWordLiteralCaseI

/-! ## The literal Case-II input -/

/-- One excessive-factor peel, independent of the auxiliary mark count.
The actual quotient and the finite injection into residual-object/epimorphism
pairs are retained in `encoding`; `row` derives the exponential estimate.
-/
structure PublishedBoundedWordLiteralCaseII
    (count : ℕ → ℕ → ℝ) (peel : ℕ → ℝ) (A : ℝ) (b k : ℕ) where
  e : ℝ
  w : ℝ
  bThree : ℝ
  bFour : ℝ
  d : ℕ
  n : ℕ
  A₀ : ℝ
  encoding : PublishedCaseIIEpiEncoding peel (count k) b d n A₀ A
  bThree_nonneg : 0 ≤ bThree
  bFour_nonneg : 0 ≤ bFour
  residual_width : bThree + bFour = (b : ℝ) - w
  remaining_degree : (k : ℝ) = (b : ℝ) - w
  excessive :
    e * Nat.log 2 (Nat.card (Subgroup.center encoding.target.Carrier)) +
        Nat.log 2 (Nat.card (commutator encoding.target.Carrier)) ≤ w / 2
  z_cap : (Nat.log 2 (Nat.card (Subgroup.center encoding.target.Carrier)) : ℝ) ≤ w / 4
  source_rank : (d : ℝ) ≤ e * bThree / 4 + bFour / 2
  normal_rank : (n : ℝ) ≤ bThree / 4

namespace PublishedBoundedWordLiteralCaseII

/-- The literal finite epimorphism encoding supplies the old peel row for
every auxiliary rank `r`. -/
noncomputable def row
    {count : ℕ → ℕ → ℝ} {peel : ℕ → ℝ} {A : ℝ} {b k : ℕ}
    (D : PublishedBoundedWordLiteralCaseII count peel A b k) (r : ℕ) :
    PublishedBoundedWordCaseIIPeelRow count (peel r) A b k r where
  e := D.e
  z := Nat.log 2 (Nat.card (Subgroup.center D.encoding.target.Carrier))
  g := Nat.log 2 (Nat.card (commutator D.encoding.target.Carrier))
  w := D.w
  bThree := D.bThree
  bFour := D.bFour
  dSource := D.d + r
  dNormal := D.n
  z_nonneg := by positivity
  g_nonneg := by positivity
  bThree_nonneg := D.bThree_nonneg
  bFour_nonneg := D.bFour_nonneg
  residual_width := D.residual_width
  remaining_degree := D.remaining_degree
  excessive := D.excessive
  z_cap := D.z_cap
  source_rank := by
    have := D.source_rank
    linarith
  normal_rank := D.normal_rank
  enumeration := by
    have h := D.encoding.bound r
    rw [← Real.rpow_natCast] at h
    simpa only [publishedCaseIIPeelExponent, Nat.cast_add, Nat.cast_mul] using h

end PublishedBoundedWordLiteralCaseII

/-- The literal RDT Proposition 7.4 partition, before either marked
optimization.  The zero-degree row is stated as the exact unmarked bound
`count 0 r ≤ 1`. -/
structure PublishedBoundedWordCaseDecomposition
    (count : ℕ → ℕ → ℝ) where
  A : ℝ
  A_nonneg : 0 ≤ A
  count_nonneg : ∀ b r, 0 ≤ count b r
  caseI : ℕ → ℕ → ℝ
  peel : ℕ → ℕ → ℕ → ℝ
  caseI_nonneg : ∀ b r, 0 ≤ caseI b r
  peel_nonneg : ∀ b k r, 0 ≤ peel b k r
  zero_unmarked : ∀ r, count 0 r ≤ 1
  partition : ∀ b r, 0 < b →
    count b r ≤ caseI b r + ∑ k ∈ Finset.range b, peel b k r
  caseILiteral : ∀ b, PublishedBoundedWordLiteralCaseI (caseI b) A b
  peelLiteral : ∀ b k, k < b →
    PublishedBoundedWordLiteralCaseII count (peel b k) A b k

namespace PublishedBoundedWordCaseDecomposition

variable {count : ℕ → ℕ → ℝ}

/-- All marked bounds are derived from the published unoptimized rows. -/
noncomputable def toBoundedWordCaseDecomposition
    (D : PublishedBoundedWordCaseDecomposition count) :
    BoundedWordCaseDecomposition count where
  A := D.A
  A_nonneg := D.A_nonneg
  count_nonneg := D.count_nonneg
  caseI := D.caseI
  peel := D.peel
  caseI_nonneg := D.caseI_nonneg
  peel_nonneg := D.peel_nonneg
  zero := by
    intro r
    exact (D.zero_unmarked r).trans (by
      simpa [markedBase, markedF] using
        (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
          (by positivity : (0 : ℝ) ≤ (r : ℝ) ^ 2 / 2)))
  partition := D.partition
  caseI_bound := fun b r ↦ (D.caseILiteral b |>.row r).bound
  peel_bound := fun b k r hk ↦
    (D.peelLiteral b k hk |>.row r).bound (D.count_nonneg k r)

end PublishedBoundedWordCaseDecomposition

end MarkedC4
end SymmetricSubgroupAsymptotics

end
