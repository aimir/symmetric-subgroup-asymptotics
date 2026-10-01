import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
# Binary columns of finite abelian groups

For a finite commutative group `A` let `A[2]` be its elements of order at most
two and `A²` its squares.  The binary columns of `A` are

`col A 0 = log₂ |A[2]|`,  `col A (k+1) = col (A²) k`,

the numbers of cyclic `2`-power factors of order at least `2^(k+1)`.  This
file proves the elementary counting facts used by the marked `C4` moment:

* `|A| = |A[2]| |A²|`;
* `|Hom(E, B)| ≤ 2^(∑ₖ colₖ E colₖ B)` when `B` has exponent dividing `2^N`;
* an elementary abelian `2`-group of order `2^n` has at most
  `2^(k(n-k)+2)` subgroups of order `2^k`;
* a finite group is generated modulo a subgroup `R` by a set `S` with
  `2^|S| |R| ≤ |M|`.

No structure theorem for finite abelian groups is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u

/-! ## Squares and involutions -/

section Basic

variable (A : Type u) [CommGroup A]

/-- The squaring homomorphism. -/
def sqHom : A →* A := powMonoidHom 2

/-- Elements of order at most two. -/
def tors2 : Subgroup A := (sqHom A).ker

/-- The subgroup of squares. -/
def sqs : Subgroup A := (sqHom A).range

variable {A}

theorem mem_tors2 (x : A) : x ∈ tors2 A ↔ x ^ 2 = 1 := Iff.rfl

theorem mem_sqs (x : A) : x ∈ sqs A ↔ ∃ y : A, y ^ 2 = x := Iff.rfl

theorem sq_mem_sqs (y : A) : y ^ 2 ∈ sqs A := ⟨y, rfl⟩

variable (A)

theorem card_eq_tors2_mul_sqs [Finite A] :
    Nat.card A = Nat.card (tors2 A) * Nat.card (sqs A) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (tors2 A), mul_comm]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (sqHom A)).toEquiv

theorem tors2_isPGroup : IsPGroup 2 (tors2 A) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : A) ^ (2 ^ 1) = 1
  rw [pow_one]
  exact g.2

theorem card_tors2_eq_pow [Finite A] : ∃ n : ℕ, Nat.card (tors2 A) = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (IsPGroup.iff_card).mp (tors2_isPGroup A)

end Basic

/-! ## Columns -/

/-- The binary columns of a finite commutative group. -/
def col : (A : Type u) → [CommGroup A] → [Finite A] → ℕ → ℕ
  | A, _, _, 0 => Nat.log 2 (Nat.card (tors2 A))
  | A, _, _, k + 1 => col (sqs A) k

theorem col_zero (A : Type u) [CommGroup A] [Finite A] :
    col A 0 = Nat.log 2 (Nat.card (tors2 A)) := rfl

theorem col_succ (A : Type u) [CommGroup A] [Finite A] (k : ℕ) :
    col A (k + 1) = col (sqs A) k := rfl

theorem card_tors2 (A : Type u) [CommGroup A] [Finite A] :
    Nat.card (tors2 A) = 2 ^ col A 0 := by
  obtain ⟨n, hn⟩ := card_tors2_eq_pow A
  rw [col_zero, hn, Nat.log_pow (by norm_num)]

theorem card_eq_two_pow_col_mul (A : Type u) [CommGroup A] [Finite A] :
    Nat.card A = 2 ^ col A 0 * Nat.card (sqs A) := by
  rw [card_eq_tors2_mul_sqs, card_tors2]

/-- The image of the squares under an isomorphism. -/
def sqsEquiv {A B : Type u} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    sqs A ≃* sqs B where
  toFun x := ⟨e x, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨e y, by
      change (e y) ^ 2 = e x
      rw [← map_pow]
      exact congrArg e hy⟩⟩
  invFun x := ⟨e.symm x, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨e.symm y, by
      change (e.symm y) ^ 2 = e.symm x
      rw [← map_pow]
      exact congrArg e.symm hy⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv x := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)

theorem card_tors2_congr {A B : Type u} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    Nat.card (tors2 A) = Nat.card (tors2 B) := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨e x, by
        rw [mem_tors2, ← map_pow, (mem_tors2 _).mp x.2, map_one]⟩
      invFun := fun x => ⟨e.symm x, by
        rw [mem_tors2, ← map_pow, (mem_tors2 _).mp x.2, map_one]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply _) }

/-- Columns are isomorphism invariants. -/
theorem col_congr : ∀ (k : ℕ) {A B : Type u} [CommGroup A] [CommGroup B] [Finite A]
    [Finite B] (_ : A ≃* B), col A k = col B k
  | 0, A, B, _, _, _, _, e => by
      rw [col_zero, col_zero, card_tors2_congr e]
  | k + 1, A, B, _, _, _, _, e => by
      rw [col_succ, col_succ]
      exact col_congr k (sqsEquiv e)

/-- The first column bounds the next. -/
theorem col_succ_le (A : Type u) [CommGroup A] [Finite A] (k : ℕ) :
    col A (k + 1) ≤ col A k := by
  induction k generalizing A with
  | zero =>
    rw [col_succ]
    -- `tors2 (sqs A)` injects into `tors2 A`
    have h : Nat.card (tors2 (sqs A)) ≤ Nat.card (tors2 A) := by
      refine Nat.card_le_card_of_injective
        (fun x : tors2 (sqs A) => (⟨((x : sqs A) : A), by
          have := x.2
          rw [mem_tors2] at this ⊢
          exact congrArg Subtype.val this⟩ : tors2 A)) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : tors2 A => (z : A)) hxy
    rw [card_tors2, card_tors2] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  | succ k ih =>
    rw [col_succ, col_succ]
    exact ih (sqs A)

/-! ## Exponents -/

/-- Exponent dividing `2^N`. -/
def HasExp2 (A : Type u) [Group A] (N : ℕ) : Prop := ∀ x : A, x ^ (2 ^ N) = 1

theorem hasExp2_sqs {A : Type u} [CommGroup A] {N : ℕ} (h : HasExp2 A (N + 1)) :
    HasExp2 (sqs A) N := by
  rintro ⟨_, y, rfl⟩
  apply Subtype.ext
  change (y ^ 2) ^ (2 ^ N) = 1
  rw [← pow_mul, ← pow_succ']
  exact h y

theorem subsingleton_of_hasExp2_zero {A : Type u} [Group A] (h : HasExp2 A 0) :
    Subsingleton A :=
  ⟨fun x y => by
    have hx := h x
    have hy := h y
    simp only [pow_zero, pow_one] at hx hy
    rw [hx, hy]⟩

/-! ## Generating sets -/

/-- Homomorphisms are determined by their values on a generating set. -/
theorem card_hom_le_pow_of_closure {G H : Type*} [Group G] [Group H] [Finite H]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
    (X : Set H) (hX : ∀ (f : G →* H) (s : G), s ∈ S → f s ∈ X) :
    Nat.card (G →* H) ≤ Nat.card X ^ S.card := by
  have hinj : Function.Injective
      (fun f : G →* H => (fun s : S => (⟨f s, hX f s s.2⟩ : X))) := by
    intro f g hfg
    apply MonoidHom.eq_of_eqOn_dense hS
    intro s hs
    have := congrFun hfg ⟨s, hs⟩
    exact congrArg Subtype.val this
  calc Nat.card (G →* H) ≤ Nat.card (S → X) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card X ^ S.card := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

/-- Relative generation: `M` is generated modulo `R ≤ M` by a set `S` with
`2^|S| |R| ≤ |M|`. -/
theorem exists_relative_generating_finset {G : Type*} [Group G] [Finite G]
    (R M : Subgroup G) (hRM : R ≤ M) :
    ∃ S : Finset G, (S : Set G) ⊆ M ∧
      Subgroup.closure ((S : Set G) ∪ R) = M ∧ 2 ^ S.card * Nat.card R ≤ Nat.card M := by
  suffices h : ∀ m : ℕ, ∀ S : Finset G, (S : Set G) ⊆ M →
      2 ^ S.card * Nat.card R ≤ Nat.card (Subgroup.closure ((S : Set G) ∪ R)) →
      Nat.card M - Nat.card (Subgroup.closure ((S : Set G) ∪ R)) ≤ m →
      ∃ T : Finset G, (T : Set G) ⊆ M ∧
        Subgroup.closure ((T : Set G) ∪ R) = M ∧ 2 ^ T.card * Nat.card R ≤ Nat.card M by
    refine h (Nat.card M) ∅ (by simp) ?_ (Nat.sub_le _ _)
    simp only [Finset.card_empty, pow_zero, one_mul, Finset.coe_empty, Set.empty_union,
      Subgroup.closure_eq]
    exact le_rfl
  have hcl : ∀ S : Finset G, (S : Set G) ⊆ M →
      Subgroup.closure ((S : Set G) ∪ R) ≤ M := fun S hS =>
    (Subgroup.closure_le _).mpr (Set.union_subset hS hRM)
  intro m
  induction m with
  | zero =>
    intro S hSM hS hm
    have hle := Subgroup.card_le_of_le (hcl S hSM)
    have hcard : Nat.card (Subgroup.closure ((S : Set G) ∪ R)) = Nat.card M :=
      le_antisymm hle (by omega)
    have heq := Subgroup.eq_of_le_of_card_ge (hcl S hSM) hcard.ge
    exact ⟨S, hSM, heq, hS.trans hle⟩
  | succ m ih =>
    intro S hSM hS hm
    by_cases htop : Subgroup.closure ((S : Set G) ∪ R) = M
    · exact ⟨S, hSM, htop, hS.trans (Subgroup.card_le_of_le (hcl S hSM))⟩
    · obtain ⟨g, hgM, hg⟩ : ∃ g ∈ M, g ∉ Subgroup.closure ((S : Set G) ∪ R) := by
        by_contra hall
        push Not at hall
        exact htop (le_antisymm (hcl S hSM) (fun g hg => hall g hg))
      have hgS : g ∉ S := fun h => hg (Subgroup.subset_closure (Or.inl h))
      let S' := insert g S
      have hS'M : (S' : Set G) ⊆ M := by
        intro x hx
        simp only [S', Finset.coe_insert, Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact hgM
        · exact hSM hx
      have hle : Subgroup.closure ((S : Set G) ∪ R) ≤ Subgroup.closure ((S' : Set G) ∪ R) :=
        Subgroup.closure_mono (Set.union_subset_union_left _ (by simp [S']))
      have hgS' : g ∈ Subgroup.closure ((S' : Set G) ∪ R) :=
        Subgroup.subset_closure (Or.inl (by simp [S']))
      have hdvd := Subgroup.card_dvd_of_le hle
      have hlt : Nat.card (Subgroup.closure ((S : Set G) ∪ R)) <
          Nat.card (Subgroup.closure ((S' : Set G) ∪ R)) := by
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) ?_
        intro heq
        have := Subgroup.eq_of_le_of_card_ge hle heq.ge
        exact hg (this ▸ hgS')
      have hdouble : 2 * Nat.card (Subgroup.closure ((S : Set G) ∪ R)) ≤
          Nat.card (Subgroup.closure ((S' : Set G) ∪ R)) := by
        obtain ⟨k, hk⟩ := hdvd
        have hpos : 0 < Nat.card (Subgroup.closure ((S : Set G) ∪ R)) := Nat.card_pos
        rcases k with _ | _ | k
        · omega
        · omega
        · rw [hk]
          nlinarith
      have hcardS' : S'.card = S.card + 1 := Finset.card_insert_of_notMem hgS
      have hM' := Subgroup.card_le_of_le (hcl S' hS'M)
      apply ih S' hS'M
      · rw [hcardS', pow_succ]
        nlinarith
      · omega

/-- Absolute version: `2^|S| ≤ |G|`. -/
theorem exists_generating_finset_card_le (G : Type*) [Group G] [Finite G] :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2 ^ S.card ≤ Nat.card G := by
  obtain ⟨S, -, hS, hcard⟩ := exists_relative_generating_finset (⊥ : Subgroup G) ⊤ bot_le
  refine ⟨S, ?_, ?_⟩
  · rw [← hS, Subgroup.closure_union, Subgroup.closure_eq, sup_bot_eq]
  · simpa [Subgroup.card_bot, Subgroup.card_top] using hcard

/-! ## Homomorphism counts by columns -/

/-- A hom to `B` vanishing on squares lands in `B[2]`; counted on generators. -/
theorem card_hom_quotient_sqs_le (E B : Type u) [CommGroup E] [Finite E] [CommGroup B]
    [Finite B] :
    Nat.card (E ⧸ sqs E →* tors2 B) ≤ 2 ^ (col E 0 * col B 0) := by
  obtain ⟨S, hS, hcard⟩ := exists_generating_finset_card_le (E ⧸ sqs E)
  have hq : Nat.card (E ⧸ sqs E) = 2 ^ col E 0 := by
    have h1 := card_eq_tors2_mul_sqs E
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (sqs E)
    rw [card_tors2] at h1
    have hpos : 0 < Nat.card (sqs E) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h2.symm.trans h1)
  have hScard : S.card ≤ col E 0 := by
    rw [hq] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  calc Nat.card (E ⧸ sqs E →* tors2 B)
      ≤ Nat.card (Set.univ : Set (tors2 B)) ^ S.card :=
        card_hom_le_pow_of_closure S hS Set.univ (fun _ _ _ => Set.mem_univ _)
    _ = (2 ^ col B 0) ^ S.card := by
        rw [Nat.card_univ, card_tors2]
    _ ≤ (2 ^ col B 0) ^ col E 0 :=
        Nat.pow_le_pow_right (Nat.pow_pos (by norm_num)) hScard
    _ = 2 ^ (col E 0 * col B 0) := by rw [← pow_mul, mul_comm]

/-- Restriction of a hom to the squares. -/
def restrictSqs {E B : Type u} [CommGroup E] [CommGroup B] (f : E →* B) :
    sqs E →* sqs B :=
  (f.comp (sqs E).subtype).codRestrict (sqs B) (by
    rintro ⟨_, y, rfl⟩
    exact ⟨f y, by simp [sqHom]⟩)

/-- **Hom counts by columns.**  If `B` has exponent dividing `2^N` then
`|Hom(E,B)| ≤ 2^(∑_{k<N} colₖ E · colₖ B)`. -/
theorem card_hom_le : ∀ (N : ℕ) (E B : Type u) [CommGroup E] [Finite E] [CommGroup B]
    [Finite B], HasExp2 B N →
    Nat.card (E →* B) ≤ 2 ^ (∑ k ∈ Finset.range N, col E k * col B k)
  | 0, E, B, _, _, _, _, hB => by
      haveI := subsingleton_of_hasExp2_zero hB
      haveI : Subsingleton (E →* B) :=
        ⟨fun f g => MonoidHom.ext fun _ => Subsingleton.elim _ _⟩
      simpa using Finite.card_le_one_iff_subsingleton.mpr inferInstance
  | N + 1, E, B, _, _, _, _, hB => by
      have ih := card_hom_le N (sqs E) (sqs B) (hasExp2_sqs hB)
      letI : Finite (E →* B) := Finite.of_injective (fun f : E →* B => (f : E → B))
        DFunLike.coe_injective
      letI : Finite (sqs E →* sqs B) := Finite.of_injective
        (fun f : sqs E →* sqs B => (f : sqs E → sqs B)) DFunLike.coe_injective
      letI : Finite (E ⧸ sqs E →* tors2 B) := Finite.of_injective
        (fun f : E ⧸ sqs E →* tors2 B => (f : E ⧸ sqs E → tors2 B)) DFunLike.coe_injective
      let base : (sqs E →* sqs B) → (E →* B) := Function.invFun restrictSqs
      have hbase : ∀ f : E →* B, restrictSqs (base (restrictSqs f)) = restrictSqs f :=
        fun f => Function.invFun_eq ⟨f, rfl⟩
      -- the difference of `f` and its base is trivial on squares
      let diff : (E →* B) → (E →* B) := fun f => f / base (restrictSqs f)
      have hdiff_sqs : ∀ f (x : E), x ∈ sqs E → diff f x = 1 := by
        intro f x hx
        have h := congrArg (fun g : sqs E →* sqs B => ((g ⟨x, hx⟩ : sqs B) : B)) (hbase f)
        change (base (restrictSqs f)) x = f x at h
        show f x / base (restrictSqs f) x = 1
        rw [h, div_self']
      have hdiff_tors : ∀ f (x : E), diff f x ∈ tors2 B := by
        intro f x
        rw [mem_tors2, ← map_pow]
        exact hdiff_sqs f _ (sq_mem_sqs x)
      let toQ : (E →* B) → (E ⧸ sqs E →* tors2 B) := fun f =>
        QuotientGroup.lift (sqs E)
          ((diff f).codRestrict (tors2 B) (hdiff_tors f))
          (fun x hx => Subtype.ext (hdiff_sqs f x hx))
      have hinj : Function.Injective (fun f => (restrictSqs f, toQ f)) := by
        intro f g hfg
        have h1 : restrictSqs f = restrictSqs g := congrArg Prod.fst hfg
        have h2 : toQ f = toQ g := congrArg Prod.snd hfg
        ext x
        have hx := DFunLike.congr_fun h2 (x : E ⧸ sqs E)
        simp only [toQ, QuotientGroup.lift_mk, MonoidHom.codRestrict_apply] at hx
        have hx' : diff f x = diff g x := congrArg Subtype.val hx
        simp only [diff, MonoidHom.div_apply, h1] at hx'
        exact div_left_injective hx'
      calc Nat.card (E →* B)
          ≤ Nat.card ((sqs E →* sqs B) × (E ⧸ sqs E →* tors2 B)) :=
            Nat.card_le_card_of_injective _ hinj
        _ = Nat.card (sqs E →* sqs B) * Nat.card (E ⧸ sqs E →* tors2 B) := Nat.card_prod _ _
        _ ≤ 2 ^ (∑ k ∈ Finset.range N, col (sqs E) k * col (sqs B) k) *
              2 ^ (col E 0 * col B 0) :=
            Nat.mul_le_mul ih (card_hom_quotient_sqs_le E B)
        _ = 2 ^ (∑ k ∈ Finset.range (N + 1), col E k * col B k) := by
            rw [← pow_add, Finset.sum_range_succ']
            rfl

/-! ## Subgroups of elementary abelian `2`-groups -/

/-- The product `∏_{j<k} (2^k - 2^j)`, the number of ordered bases of `F₂^k`. -/
def basisCount (k : ℕ) : ℕ := ∏ j ∈ Finset.range k, (2 ^ k - 2 ^ j)

theorem basisCount_succ (k : ℕ) :
    basisCount (k + 1) = (2 ^ (k + 1) - 1) * 2 ^ k * basisCount k := by
  unfold basisCount
  rw [Finset.prod_range_succ', pow_zero]
  have h : ∀ j ∈ Finset.range k, 2 ^ (k + 1) - 2 ^ (j + 1) = 2 * (2 ^ k - 2 ^ j) := by
    intro j _
    rw [pow_succ, pow_succ, Nat.mul_sub, mul_comm (2 ^ k), mul_comm (2 ^ j)]
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]
  ring

/-- `2^(k²) ≤ 4 ∏_{j<k} (2^k - 2^j)`. -/
theorem pow_sq_le_four_mul_basisCount (k : ℕ) : 2 ^ (k * k) ≤ 4 * basisCount k := by
  -- strengthened invariant for `k ≥ 1`
  have inv : ∀ k : ℕ, 1 ≤ k →
      2 ^ (k * k) * (2 ^ (k + 1) + 4) ≤ 2 ^ (k + 3) * basisCount k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp [basisCount]
    | succ k hk ih =>
      rw [basisCount_succ]
      set X : ℕ := 2 ^ (k + 1) with hXdef
      have hX : 4 ≤ X := by
        have : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa [hXdef] using this
      have hX1 : 1 ≤ X := by omega
      set a : ℕ := 2 ^ (k * k)
      set Q : ℕ := basisCount k
      have hsq : 2 ^ ((k + 1) * (k + 1)) = a * 2 ^ k * X := by
        simp only [a, hXdef, ← pow_add]
        congr 1
        ring
      have h2X : 2 ^ (k + 1 + 1) = 2 * X := by rw [hXdef, pow_succ]; ring
      have h3 : 2 ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by rw [pow_succ]; ring
      rw [hsq, h2X, h3]
      have key : X * (2 * X + 4) ≤ 2 * (X - 1) * (X + 4) := by
        obtain ⟨Z, hZ⟩ : ∃ Z, X = Z + 1 := ⟨X - 1, by omega⟩
        rw [hZ, Nat.add_sub_cancel]
        nlinarith
      calc a * 2 ^ k * X * (2 * X + 4)
          = 2 ^ k * a * (X * (2 * X + 4)) := by ring
        _ ≤ 2 ^ k * a * (2 * (X - 1) * (X + 4)) := Nat.mul_le_mul_left _ key
        _ = 2 * (X - 1) * 2 ^ k * (a * (X + 4)) := by ring
        _ ≤ 2 * (X - 1) * 2 ^ k * (2 ^ (k + 3) * Q) := Nat.mul_le_mul_left _ ih
        _ = 2 * 2 ^ (k + 3) * ((X - 1) * 2 ^ k * Q) := by ring
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [basisCount]
  · have h := inv k hk
    have h' : 2 ^ (k * k) * 2 ^ (k + 1) ≤ 2 ^ (k + 3) * basisCount k :=
      le_trans (Nat.mul_le_mul_left _ (by omega)) h
    have h8 : 2 ^ (k + 3) = 2 ^ (k + 1) * 4 := by rw [pow_add, pow_add]; ring
    rw [h8, mul_comm (2 ^ (k * k)), mul_assoc] at h'
    exact Nat.le_of_mul_le_mul_left h' (Nat.pow_pos (by norm_num))

/-- The generating tuples of an elementary abelian group of order `2^k`. -/
theorem basisCount_le_card_generating {V : Type u} [CommGroup V] [Finite V]
    (hV : ∀ x : V, x ^ 2 = 1) (k : ℕ) (hk : Nat.card V = 2 ^ k) :
    basisCount k ≤
      Nat.card {t : Fin k → V // Subgroup.closure (Set.range t) = ⊤} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) (by
    intro x
    change (Additive.toMul x) ^ 2 = 1
    exact hV _)
  letI : Fintype (Additive V) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive V) = k := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at h
    have h' : Nat.card (Additive V) = 2 ^ k := hk
    rw [h'] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hli := card_linearIndependent (K := ZMod 2) (V := Additive V) (k := k) (by omega)
  have hq : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [hq, hfin] at hli
  have hbc : basisCount k = Nat.card {s : Fin k → Additive V // LinearIndependent (ZMod 2) s} := by
    rw [hli, basisCount, Finset.prod_range (fun j => 2 ^ k - 2 ^ j)]
  rw [hbc]
  refine Nat.card_le_card_of_injective
    (fun s => ⟨fun i => Additive.toMul (s.1 i), ?_⟩) ?_
  · -- a basis spans, hence generates
    have hspan := s.2.span_eq_top_of_card_eq_finrank' (by simp [hfin])
    rw [eq_top_iff]
    intro x _
    have hx : Additive.ofMul x ∈ Submodule.span (ZMod 2) (Set.range s.1) := by
      rw [hspan]
      exact Submodule.mem_top
    let H : Subgroup V := Subgroup.closure (Set.range (fun i => Additive.toMul (s.1 i)))
    let K : AddSubgroup (Additive V) :=
      { carrier := {a | Additive.toMul a ∈ H}
        add_mem' := fun ha hb => H.mul_mem ha hb
        zero_mem' := H.one_mem
        neg_mem' := fun ha => H.inv_mem ha }
    have hle : Submodule.span (ZMod 2) (Set.range s.1) ≤ AddSubgroup.toZModSubmodule 2 K := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show Additive.toMul (s.1 i) ∈ H
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact hle hx
  · intro s₁ s₂ h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    exact Additive.toMul.injective this

/-- **Gaussian bound.**  An elementary abelian group of order `2^n` has at
most `2^(k(n-k)+2)` subgroups of order `2^k`. -/
theorem card_subgroups_elementary_le {W : Type u} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x ^ 2 = 1) (n k : ℕ) (hn : Nat.card W = 2 ^ n) :
    Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} ≤ 2 ^ (k * (n - k) + 2) := by
  rcases isEmpty_or_nonempty {V : Subgroup W // Nat.card V = 2 ^ k} with hE | hne
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  obtain ⟨V₀⟩ := hne
  have hkn : k ≤ n := by
    have hdvd := Subgroup.card_subgroup_dvd_card V₀.1
    rw [V₀.2, hn] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  let Gen : {V : Subgroup W // Nat.card V = 2 ^ k} → Type u := fun V =>
    {t : Fin k → V.1 // Subgroup.closure (Set.range t) = ⊤}
  have hgen : ∀ V, basisCount k ≤ Nat.card (Gen V) := by
    intro V
    exact basisCount_le_card_generating (V := V.1)
      (fun x => Subtype.ext (hW x)) k V.2
  let F : (Σ V, Gen V) → (Fin k → W) := fun p i => ((p.2.1 i : p.1.1) : W)
  have hclosure : ∀ p : (Σ V, Gen V), Subgroup.closure (Set.range (F p)) = p.1.1 := by
    intro p
    have h1 : Set.range (F p) = (p.1.1.subtype) '' Set.range p.2.1 := by
      ext x
      simp [F]
    rw [h1, ← MonoidHom.map_closure, p.2.2, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hF : Function.Injective F := by
    rintro ⟨V₁, t₁⟩ ⟨V₂, t₂⟩ h
    have hV : V₁ = V₂ := by
      apply Subtype.ext
      rw [← hclosure ⟨V₁, t₁⟩, ← hclosure ⟨V₂, t₂⟩]
      exact congrArg _ (congrArg Set.range h)
    subst hV
    have ht : t₁ = t₂ := by
      apply Subtype.ext
      funext i
      exact Subtype.ext (congrFun h i)
    rw [ht]
  letI : Finite (Σ V, Gen V) := Finite.of_injective F hF
  letI := Fintype.ofFinite {V : Subgroup W // Nat.card V = 2 ^ k}
  have hsum : Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * basisCount k ≤ 2 ^ (n * k) := by
    calc Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * basisCount k
        ≤ Nat.card (Σ V, Gen V) := by
          rw [Nat.card_sigma]
          calc Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * basisCount k
              = ∑ _V : {V : Subgroup W // Nat.card V = 2 ^ k}, basisCount k := by
                rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
                  Nat.card_eq_fintype_card]
            _ ≤ ∑ V, Nat.card (Gen V) := Finset.sum_le_sum (fun V _ => hgen V)
      _ ≤ Nat.card (Fin k → W) := Nat.card_le_card_of_injective F hF
      _ = 2 ^ (n * k) := by rw [Nat.card_fun, Nat.card_fin, hn, ← pow_mul]
  have h4 := pow_sq_le_four_mul_basisCount k
  -- combine: #V * 2^(k*k) ≤ 4 * 2^(n*k)
  have hcomb : Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * 2 ^ (k * k) ≤
      2 ^ (k * (n - k) + 2) * 2 ^ (k * k) := by
    calc Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * 2 ^ (k * k)
        ≤ Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * (4 * basisCount k) :=
          Nat.mul_le_mul_left _ h4
      _ = 4 * (Nat.card {V : Subgroup W // Nat.card V = 2 ^ k} * basisCount k) := by ring
      _ ≤ 4 * 2 ^ (n * k) := Nat.mul_le_mul_left _ hsum
      _ = 2 ^ (k * (n - k) + 2) * 2 ^ (k * k) := by
          rw [← pow_add]
          have : k * (n - k) + 2 + k * k = n * k + 2 := by
            have : k * (n - k) + k * k = n * k := by
              rw [← Nat.mul_add, Nat.sub_add_cancel hkn, mul_comm]
            omega
          rw [this, pow_add]
          ring
  exact Nat.le_of_mul_le_mul_right hcomb (Nat.pow_pos (by norm_num))

end MarkedC4
end SymmetricSubgroupAsymptotics
