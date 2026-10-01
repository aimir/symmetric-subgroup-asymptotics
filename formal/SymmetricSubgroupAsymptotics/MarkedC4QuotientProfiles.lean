import SymmetricSubgroupAsymptotics.MarkedC4AbelianColumns

/-!
# Quotients of a finite abelian `2`-group by column profile

For a finite commutative group `T` of exponent dividing `2^N` and a column
profile `y`, the number of subgroups `K ≤ T` with `colₖ(T/K) = yₖ` for all
`k < N` is at most

`2^(∑_{k<N} (yₖ (colₖ T - yₖ) + 2))`.

This is the Birkhoff-type bound used in the abelian Hall splice.  The proof
peels the top binary layer: `K` is recorded by its trace `K ∩ T²` on the
squares, the subgroup `K T²`, and a coset representative choice for a
relative generating set of `K T²` over `T²`.  The trace is counted by
induction; `K T²` lies between `T²` and an explicit bound `Mmax`, so it is a
subgroup of an elementary abelian group of the right order; the
representatives are square roots of fixed elements in a group whose first
column is `y₁`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u

/-! ## Generalities -/

/-- A map whose fibres have at most `m` elements. -/
theorem card_le_mul_of_fibres {α β : Type*} [Finite α] [Finite β] (f : α → β) (m : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} ≤ m) : Nat.card α ≤ Nat.card β * m := by
  letI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  calc ∑ b, Nat.card {a // f a = b} ≤ ∑ _b : β, m := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card β * m := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- The product formula in a finite commutative group. -/
theorem card_sup_mul_card_inf {G : Type*} [CommGroup G] [Finite G] (K R : Subgroup G) :
    Nat.card (K ⊔ R : Subgroup G) * Nat.card (K ⊓ R : Subgroup G) =
      Nat.card K * Nat.card R := by
  let φ : K × R →* G := (K.subtype.comp (MonoidHom.fst K R)) *
    (R.subtype.comp (MonoidHom.snd K R))
  have hφ : ∀ p : K × R, φ p = (p.1 : G) * p.2 := fun p => rfl
  have hrange : φ.range = K ⊔ R := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_sup]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.1.2, p.2, p.2.2, (hφ p).symm⟩
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  have hker : Nat.card φ.ker = Nat.card (K ⊓ R : Subgroup G) := by
    apply Nat.card_congr
    refine
      { toFun := fun p => ⟨((p : K × R).1 : G), (p : K × R).1.2, by
          have h : ((p : K × R).1 : G) * (p : K × R).2 = 1 := p.2
          have : ((p : K × R).1 : G) = ((p : K × R).2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this]
          exact R.inv_mem (p : K × R).2.2⟩
        invFun := fun t => ⟨(⟨t, t.2.1⟩, ⟨(t : G)⁻¹, R.inv_mem t.2.2⟩), by
          change (t : G) * (t : G)⁻¹ = 1
          exact mul_inv_cancel _⟩
        left_inv := fun p => by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            have h : ((p : K × R).1 : G) * (p : K × R).2 = 1 := p.2
            exact (eq_inv_of_mul_eq_one_right h).symm
        right_inv := fun t => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
    Nat.card_prod] at h1
  rw [h1, mul_comm]

/-- Cardinality of a preimage of a subgroup of the range. -/
theorem card_comap_of_le_range {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (X : Subgroup H) (hX : X ≤ f.range) :
    Nat.card (X.comap f) = Nat.card f.ker * Nat.card X := by
  let g : X.comap f →* X := (f.comp (X.comap f).subtype).codRestrict X (fun x => x.2)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hX x.2
    exact ⟨⟨y, by
      show f y ∈ X
      rw [hy]
      exact x.2⟩, Subtype.ext hy⟩
  have hker : Nat.card g.ker = Nat.card f.ker := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨((x : X.comap f) : G), by
          have : g x = 1 := x.2
          exact congrArg Subtype.val this⟩
        invFun := fun y => ⟨⟨y, by
          show f y ∈ X
          rw [show f y = 1 from y.2]
          exact X.one_mem⟩, Subtype.ext (show f y = 1 from y.2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker] at h1
  rw [h1, mul_comm]

/-- Cardinality of the image of a subgroup containing the kernel. -/
theorem card_map_mk_mul {G : Type*} [CommGroup G] [Finite G] (R X : Subgroup G)
    (hRX : R ≤ X) :
    Nat.card (X.map (QuotientGroup.mk' R)) * Nat.card R = Nat.card X := by
  have h := card_comap_of_le_range (QuotientGroup.mk' R) (X.map (QuotientGroup.mk' R))
    (by
      rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective R)]
      exact le_top)
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hRX] at h
  rw [h, mul_comm]

/-! ## The squares of a quotient -/

/-- The squares of `T/K` are the squares of `T` modulo their trace in `K`. -/
def sqsQuotientEquiv {T : Type u} [CommGroup T] (K : Subgroup T) :
    sqs T ⧸ K.comap (sqs T).subtype ≃* sqs (T ⧸ K) := by
  let φ : sqs T →* T ⧸ K := (QuotientGroup.mk' K).comp (sqs T).subtype
  have hker : φ.ker = K.comap (sqs T).subtype := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : φ.range = sqs (T ⧸ K) := by
    ext z
    constructor
    · rintro ⟨⟨_, y, rfl⟩, rfl⟩
      exact ⟨(y : T ⧸ K), by
        change ((y : T ⧸ K)) ^ 2 = ((y ^ 2 : T) : T ⧸ K)
        rw [QuotientGroup.mk_pow]⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      refine ⟨⟨y ^ 2, sq_mem_sqs y⟩, ?_⟩
      change ((y ^ 2 : T) : T ⧸ K) = ((y : T ⧸ K)) ^ 2
      rw [QuotientGroup.mk_pow]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))

theorem col_quotient_succ {T : Type u} [CommGroup T] [Finite T] (K : Subgroup T) (k : ℕ) :
    col (T ⧸ K) (k + 1) = col (sqs T ⧸ K.comap (sqs T).subtype) k := by
  rw [col_succ]
  exact (col_congr k (sqsQuotientEquiv K)).symm

/-- `|K T²| 2^(col₀ (T/K)) = |T|`. -/
theorem card_sup_sqs_mul {T : Type u} [CommGroup T] [Finite T] (K : Subgroup T) :
    Nat.card (K ⊔ sqs T : Subgroup T) * 2 ^ col (T ⧸ K) 0 = Nat.card T := by
  have h1 := card_eq_two_pow_col_mul (T ⧸ K)
  have h2 : Nat.card (sqs (T ⧸ K)) * Nat.card (K ⊓ sqs T : Subgroup T) =
      Nat.card (sqs T) := by
    rw [← Nat.card_congr (sqsQuotientEquiv K).toEquiv]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.comap (sqs T).subtype)
    have hc : Nat.card (K.comap (sqs T).subtype) = Nat.card (K ⊓ sqs T : Subgroup T) := by
      apply Nat.card_congr
      refine
        { toFun := fun x => ⟨((x : sqs T) : T), x.2, (x : sqs T).2⟩
          invFun := fun y => ⟨⟨y, y.2.2⟩, y.2.1⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [← hc, ← h]
  have h3 := card_sup_mul_card_inf K (sqs T)
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hpos : 0 < Nat.card (K ⊓ sqs T : Subgroup T) := Nat.card_pos
  have hpos' : 0 < Nat.card K := Nat.card_pos
  -- |T| = |T/K| |K| = 2^y |sqs(T/K)| |K|, and |K ⊔ T²| |K ⊓ T²| = |K| |T²|
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (K ⊔ sqs T : Subgroup T) * 2 ^ col (T ⧸ K) 0 *
        Nat.card (K ⊓ sqs T : Subgroup T)
      = 2 ^ col (T ⧸ K) 0 * (Nat.card K * Nat.card (sqs T)) := by rw [← h3]; ring
    _ = 2 ^ col (T ⧸ K) 0 * (Nat.card K * (Nat.card (sqs (T ⧸ K)) *
          Nat.card (K ⊓ sqs T : Subgroup T))) := by rw [h2]
    _ = (2 ^ col (T ⧸ K) 0 * Nat.card (sqs (T ⧸ K))) * Nat.card K *
          Nat.card (K ⊓ sqs T : Subgroup T) := by ring
    _ = Nat.card T * Nat.card (K ⊓ sqs T : Subgroup T) := by rw [← h1, ← h4]

/-! ## The quotient-profile bound -/

/-- Subgroups with a prescribed column profile of the quotient. -/
def ProfileSet (T : Type u) [CommGroup T] [Finite T] (N : ℕ) (y : ℕ → ℕ) : Type u :=
  {K : Subgroup T // ∀ k < N, col (T ⧸ K) k = y k}

instance (T : Type u) [CommGroup T] [Finite T] (N : ℕ) (y : ℕ → ℕ) :
    Finite (ProfileSet T N y) := by
  unfold ProfileSet
  infer_instance

theorem col_quotient_zero_le {T : Type u} [CommGroup T] [Finite T] (K : Subgroup T) :
    col (T ⧸ K) 0 ≤ col T 0 := by
  have h := card_sup_sqs_mul K
  have h2 := card_eq_two_pow_col_mul T
  have hle : Nat.card (sqs T) ≤ Nat.card (K ⊔ sqs T : Subgroup T) :=
    Subgroup.card_le_of_le le_sup_right
  have hpos : 0 < Nat.card (sqs T) := Nat.card_pos
  have : 2 ^ col (T ⧸ K) 0 * Nat.card (sqs T) ≤ 2 ^ col T 0 * Nat.card (sqs T) := by
    rw [← h2, ← h, mul_comm]
    exact Nat.mul_le_mul_right _ hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right this hpos)

/-! ## One binary layer -/

section Layer

variable {T : Type u} [CommGroup T] [Finite T]

/-- The trace of `K` on the squares, viewed in `T`. -/
theorem inf_sqs_eq_map (K : Subgroup T) (K' : Subgroup (sqs T))
    (hK : K.comap (sqs T).subtype = K') :
    K ⊓ sqs T = K'.map (sqs T).subtype := by
  ext x
  constructor
  · rintro ⟨hxK, hxR⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    rw [← hK]
    exact hxK
  · rintro ⟨z, hz, rfl⟩
    rw [← hK] at hz
    exact ⟨hz, z.2⟩

/-- `|M| 2^y = |T|` gives `|M/T²| = 2^(col₀ T - y)`. -/
theorem card_map_mk_eq_of {M : Subgroup T} (hRM : sqs T ≤ M) {y : ℕ}
    (hM : Nat.card M * 2 ^ y = Nat.card T) :
    y ≤ col T 0 ∧ Nat.card (M.map (QuotientGroup.mk' (sqs T))) = 2 ^ (col T 0 - y) := by
  have h1 := card_map_mk_mul (sqs T) M hRM
  have h2 := card_eq_two_pow_col_mul T
  have hpos : 0 < Nat.card (sqs T) := Nat.card_pos
  have h3 : Nat.card (M.map (QuotientGroup.mk' (sqs T))) * 2 ^ y = 2 ^ col T 0 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (M.map (QuotientGroup.mk' (sqs T))) * 2 ^ y * Nat.card (sqs T)
        = (Nat.card (M.map (QuotientGroup.mk' (sqs T))) * Nat.card (sqs T)) * 2 ^ y := by ring
      _ = 2 ^ col T 0 * Nat.card (sqs T) := by rw [h1, hM, h2]
  have hdvd : 2 ^ y ∣ 2 ^ col T 0 := ⟨_, by rw [← h3, mul_comm]⟩
  have hy : y ≤ col T 0 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  refine ⟨hy, ?_⟩
  have h4 : 2 ^ col T 0 = 2 ^ (col T 0 - y) * 2 ^ y := by
    rw [← pow_add, Nat.sub_add_cancel hy]
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num)) h3

/-- The quotient `T/T²` has exponent two. -/
theorem quotient_sqs_sq (z : T ⧸ sqs T) : z ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact sq_mem_sqs x

/-- The bound `Mmax` for `K T²` in terms of the trace `K'`. -/
def mmax (K' : Subgroup (sqs T)) : Subgroup T :=
  (K'.map (sqs T).subtype ⊔ (sqs (sqs T)).map (sqs T).subtype).comap (sqHom T)

theorem sqs_le_mmax (K' : Subgroup (sqs T)) : sqs T ≤ mmax K' := by
  intro x hx
  unfold mmax
  rw [Subgroup.mem_comap]
  apply Subgroup.mem_sup_right
  exact ⟨⟨x, hx⟩ ^ 2, sq_mem_sqs _, rfl⟩

theorem sup_le_mmax (K : Subgroup T) (K' : Subgroup (sqs T))
    (hK : K.comap (sqs T).subtype = K') : K ⊔ sqs T ≤ mmax K' := by
  intro x hx
  rw [Subgroup.mem_sup] at hx
  obtain ⟨k, hk, r, hr, rfl⟩ := hx
  unfold mmax
  rw [Subgroup.mem_comap]
  change (k * r) ^ 2 ∈ K'.map (sqs T).subtype ⊔ (sqs (sqs T)).map (sqs T).subtype
  rw [mul_pow]
  apply Subgroup.mul_mem
  · apply Subgroup.mem_sup_left
    rw [← inf_sqs_eq_map K K' hK]
    exact ⟨K.pow_mem hk 2, sq_mem_sqs k⟩
  · apply Subgroup.mem_sup_right
    exact ⟨⟨r, hr⟩ ^ 2, sq_mem_sqs _, rfl⟩

/-- `|Mmax| 2^(y₁) = 2^(col₀ T) |T²|`. -/
theorem card_mmax_mul (K' : Subgroup (sqs T)) :
    Nat.card (mmax K') * 2 ^ col (sqs T ⧸ K') 0 = 2 ^ col T 0 * Nat.card (sqs T) := by
  have hle : K'.map (sqs T).subtype ⊔ (sqs (sqs T)).map (sqs T).subtype ≤ (sqHom T).range := by
    rw [← Subgroup.map_sup]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have h1 := card_comap_of_le_range (sqHom T) _ hle
  have h2 : Nat.card (K'.map (sqs T).subtype ⊔ (sqs (sqs T)).map (sqs T).subtype : Subgroup T) =
      Nat.card (K' ⊔ sqs (sqs T) : Subgroup (sqs T)) := by
    rw [← Subgroup.map_sup]
    exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).symm.toEquiv)
  have h3 := card_sup_sqs_mul K'
  have h4 : Nat.card (sqHom T).ker = 2 ^ col T 0 := card_tors2 T
  unfold mmax
  rw [h1, h4, h2, mul_assoc, h3]

/-- The image of `T²` in `T/K` is `T²` modulo the trace. -/
def sqsImageEquiv (K' : Subgroup (sqs T)) :
    sqs T ⧸ K' ≃* (sqs T).map (QuotientGroup.mk' (K'.map (sqs T).subtype)) := by
  let φ : sqs T →* T ⧸ K'.map (sqs T).subtype :=
    (QuotientGroup.mk' _).comp (sqs T).subtype
  have hker : φ.ker = K' := by
    ext z
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := Subtype.ext hwz
      rw [← this]
      exact hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hrange : φ.range = (sqs T).map (QuotientGroup.mk' (K'.map (sqs T).subtype)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))

/-- Square roots of a fixed element in a subgroup are at most its involutions. -/
theorem card_sqrt_le {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G) (c : G) :
    Nat.card {z : G // z ∈ H ∧ z ^ 2 = c} ≤ Nat.card (tors2 H) := by
  rcases isEmpty_or_nonempty {z : G // z ∈ H ∧ z ^ 2 = c} with h | hne
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  obtain ⟨z₀⟩ := hne
  refine Nat.card_le_card_of_injective
    (fun z => (⟨⟨z.1 / z₀.1, H.div_mem z.2.1 z₀.2.1⟩, by
      rw [mem_tors2]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, div_pow, z.2.2, z₀.2.2, div_self']⟩ :
      tors2 H)) ?_
  intro z w hzw
  have := congrArg (fun x : tors2 H => ((x : H) : G)) hzw
  simp only at this
  exact Subtype.ext (div_left_injective this)

/-- **One layer.**  With the trace on the squares fixed, the subgroups with
first quotient column `y₀` number at most `2^(y₀ (col₀ T - y₀) + 2)`. -/
theorem card_fibre_le (y₀ : ℕ) (K' : Subgroup (sqs T)) :
    Nat.card {K : Subgroup T // col (T ⧸ K) 0 = y₀ ∧ K.comap (sqs T).subtype = K'} ≤
      2 ^ (y₀ * (col T 0 - y₀) + 2) := by
  set t₀ := col T 0
  set y₁ := col (sqs T ⧸ K') 0
  set KT : Subgroup T := K'.map (sqs T).subtype
  let F := {K : Subgroup T // col (T ⧸ K) 0 = y₀ ∧ K.comap (sqs T).subtype = K'}
  rcases isEmpty_or_nonempty F with hF | hne
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  obtain ⟨K₀⟩ := hne
  -- numerical facts from one member
  have hy₁y₀ : y₁ ≤ y₀ := by
    have h := col_succ_le (T ⧸ K₀.1) 0
    rw [col_quotient_succ, K₀.2.2, K₀.2.1] at h
    exact h
  have hsupK₀ := card_sup_sqs_mul K₀.1
  rw [K₀.2.1] at hsupK₀
  have hy₀t₀ := (card_map_mk_eq_of (M := K₀.1 ⊔ (sqs T)) le_sup_right hsupK₀).1
  -- the elementary abelian ambient of `K T² / T²`
  let W : Subgroup (T ⧸ (sqs T)) := (mmax K').map (QuotientGroup.mk' (sqs T))
  have hWcard : Nat.card W = 2 ^ (t₀ - y₁) := by
    have h1 := card_map_mk_mul (sqs T) (mmax K') (sqs_le_mmax K')
    have h2 := card_mmax_mul K'
    have hpos : 0 < Nat.card (sqs T) := Nat.card_pos
    have h3 : Nat.card W * 2 ^ y₁ = 2 ^ t₀ := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc Nat.card W * 2 ^ y₁ * Nat.card (sqs T) = (Nat.card W * Nat.card (sqs T)) * 2 ^ y₁ := by ring
        _ = 2 ^ t₀ * Nat.card (sqs T) := by rw [h1, h2]
    have hy : y₁ ≤ t₀ := le_trans hy₁y₀ hy₀t₀
    have h4 : 2 ^ t₀ = 2 ^ (t₀ - y₁) * 2 ^ y₁ := by rw [← pow_add, Nat.sub_add_cancel hy]
    rw [h4] at h3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num)) h3
  have hWexp : ∀ x : W, x ^ 2 = 1 := fun x => Subtype.ext (quotient_sqs_sq (x : T ⧸ (sqs T)))
  -- the middle subgroups
  let Mid := {M : Subgroup T // (sqs T) ≤ M ∧ M ≤ mmax K' ∧ Nat.card M * 2 ^ y₀ = Nat.card T}
  have hMid : Nat.card Mid ≤ 2 ^ ((t₀ - y₀) * (y₀ - y₁) + 2) := by
    have hmapW : ∀ M : Mid, M.1.map (QuotientGroup.mk' (sqs T)) ≤ W :=
      fun M => Subgroup.map_mono M.2.2.1
    let g : Mid → {V : Subgroup W // Nat.card V = 2 ^ (t₀ - y₀)} := fun M =>
      ⟨(M.1.map (QuotientGroup.mk' (sqs T))).subgroupOf W, by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hmapW M)).toEquiv]
        exact (card_map_mk_eq_of M.2.1 M.2.2.2).2⟩
    have hg : Function.Injective g := by
      intro M₁ M₂ h
      have h1 := congrArg Subtype.val h
      simp only [g] at h1
      rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr (hmapW M₁),
        inf_eq_left.mpr (hmapW M₂)] at h1
      apply Subtype.ext
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (sqs T))) h1
      rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        sup_eq_left.mpr M₁.2.1, sup_eq_left.mpr M₂.2.1] at this
    calc Nat.card Mid ≤ Nat.card {V : Subgroup W // Nat.card V = 2 ^ (t₀ - y₀)} :=
          Nat.card_le_card_of_injective g hg
      _ ≤ 2 ^ ((t₀ - y₀) * ((t₀ - y₁) - (t₀ - y₀)) + 2) :=
          card_subgroups_elementary_le hWexp (t₀ - y₁) (t₀ - y₀) hWcard
      _ = 2 ^ ((t₀ - y₀) * (y₀ - y₁) + 2) := by
          rw [show (t₀ - y₁) - (t₀ - y₀) = y₀ - y₁ by omega]
  -- the subgroups over a fixed middle subgroup
  have hKcount : ∀ M : Mid, Nat.card {K : F // K.1 ⊔ (sqs T) = M.1} ≤ 2 ^ (y₁ * (t₀ - y₀)) := by
    intro M
    obtain ⟨S, hSM, hScl, hScard⟩ := exists_relative_generating_finset (sqs T) M.1 M.2.1
    have hSle : S.card ≤ t₀ - y₀ := by
      have h := (card_map_mk_eq_of M.2.1 M.2.2.2).2
      have h1 := card_map_mk_mul (sqs T) M.1 M.2.1
      rw [← h1, h] at hScard
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp
        (Nat.le_of_mul_le_mul_right hScard Nat.card_pos)
    have hex : ∀ (K : {K : F // K.1 ⊔ (sqs T) = M.1}) (s : S),
        ∃ k ∈ K.1.1, (s : T)⁻¹ * k ∈ (sqs T) := by
      intro K s
      have hs : (s : T) ∈ K.1.1 ⊔ (sqs T) := by
        rw [K.2]
        exact hSM s.2
      rw [Subgroup.mem_sup] at hs
      obtain ⟨k, hk, r, hr, hkr⟩ := hs
      refine ⟨k, hk, ?_⟩
      rw [← hkr]
      have : (k * r)⁻¹ * k = r⁻¹ := by group
      rw [this]
      exact (sqs T).inv_mem hr
    let rep : {K : F // K.1 ⊔ (sqs T) = M.1} → S → T := fun K s => Classical.choose (hex K s)
    have hrep : ∀ K s, rep K s ∈ K.1.1 ∧ (s : T)⁻¹ * rep K s ∈ (sqs T) :=
      fun K s => Classical.choose_spec (hex K s)
    have hKTeq : KT = K'.map (sqs T).subtype := rfl
    have hKT : ∀ K : F, KT ≤ K.1 := by
      intro K
      rw [hKTeq, ← inf_sqs_eq_map K.1 K' K.2.2]
      exact inf_le_left
    let Rbar : Subgroup (T ⧸ KT) := (sqs T).map (QuotientGroup.mk' KT)
    let Z : S → Type u := fun s =>
      {z : T ⧸ KT // z ∈ Rbar ∧ z ^ 2 = (((s : T) ^ 2 : T) : T ⧸ KT)⁻¹}
    have hsq : ∀ (K : {K : F // K.1 ⊔ (sqs T) = M.1}) (s : S),
        ((((s : T)⁻¹ * rep K s : T) : T ⧸ KT)) ^ 2 = (((s : T) ^ 2 : T) : T ⧸ KT)⁻¹ := by
      intro K s
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_inv, QuotientGroup.eq]
      have hk2 : rep K s ^ 2 ∈ KT := by
        rw [hKTeq, ← inf_sqs_eq_map K.1.1 K' K.1.2.2]
        exact ⟨K.1.1.pow_mem (hrep K s).1 2, sq_mem_sqs _⟩
      have : (((s : T)⁻¹ * rep K s) ^ 2)⁻¹ * ((s : T) ^ 2)⁻¹ = (rep K s ^ 2)⁻¹ := by
        rw [mul_pow, inv_pow, mul_inv, inv_inv, mul_comm ((s : T) ^ 2), mul_assoc,
          mul_inv_cancel, mul_one]
      rw [this]
      exact KT.inv_mem hk2
    let code : {K : F // K.1 ⊔ (sqs T) = M.1} → (s : S) → Z s := fun K s =>
      ⟨((((s : T)⁻¹ * rep K s : T)) : T ⧸ KT), ⟨_, (hrep K s).2, rfl⟩, hsq K s⟩
    -- the cardinality of every `K` over `M`
    have hcardK : ∀ K : F, K.1 ⊔ (sqs T) = M.1 → Nat.card K.1 * Nat.card (sqs T) =
        Nat.card M.1 * Nat.card KT := by
      intro K hKM
      have h := card_sup_mul_card_inf K.1 (sqs T)
      rw [hKM, inf_sqs_eq_map K.1 K' K.2.2] at h
      rw [← h]
    have hcode : Function.Injective code := by
      intro K₁ K₂ h
      have hmem : ∀ s, rep K₂ s ∈ K₁.1.1 := by
        intro s
        have h1 := congrArg Subtype.val (congrFun h s)
        simp only [code] at h1
        rw [QuotientGroup.eq] at h1
        have heq : rep K₂ s = rep K₁ s * (((s : T)⁻¹ * rep K₁ s)⁻¹ * ((s : T)⁻¹ * rep K₂ s)) := by
          group
        rw [heq]
        exact K₁.1.1.mul_mem (hrep K₁ s).1 (hKT K₁.1 h1)
      let Kt : Subgroup T := Subgroup.closure (Set.range (rep K₂) ∪ KT)
      have hKt₂ : Kt ≤ K₂.1.1 := by
        rw [Subgroup.closure_le]
        rintro x (⟨s, rfl⟩ | hx)
        · exact (hrep K₂ s).1
        · exact hKT K₂.1 hx
      have hKt₁ : Kt ≤ K₁.1.1 := by
        rw [Subgroup.closure_le]
        rintro x (⟨s, rfl⟩ | hx)
        · exact hmem s
        · exact hKT K₁.1 hx
      have hKtsup : Kt ⊔ (sqs T) = M.1 := by
        apply le_antisymm
        · rw [← K₂.2]
          exact sup_le_sup_right hKt₂ _
        · rw [← hScl, Subgroup.closure_le]
          rintro x (hx | hx)
          · have heq : x = rep K₂ ⟨x, hx⟩ * ((x : T)⁻¹ * rep K₂ ⟨x, hx⟩)⁻¹ := by group
            rw [heq]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
              (Subgroup.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)))
              (Subgroup.mem_sup_right ((sqs T).inv_mem (hrep K₂ ⟨x, hx⟩).2))
          · exact Subgroup.mem_sup_right hx
      have hKtinf : KT ≤ Kt ⊓ (sqs T) := by
        intro x hx
        refine ⟨Subgroup.subset_closure (Or.inr hx), ?_⟩
        obtain ⟨z, -, rfl⟩ := hx
        exact z.2
      have hKtcard : Nat.card K₂.1.1 ≤ Nat.card Kt := by
        have h1 := card_sup_mul_card_inf Kt (sqs T)
        rw [hKtsup] at h1
        have h2 := hcardK K₂.1 K₂.2
        have h3 : Nat.card KT ≤ Nat.card (Kt ⊓ (sqs T) : Subgroup T) := Subgroup.card_le_of_le hKtinf
        have hpos : 0 < Nat.card (sqs T) := Nat.card_pos
        apply Nat.le_of_mul_le_mul_right _ hpos
        rw [h2, ← h1]
        exact Nat.mul_le_mul_left _ h3
      have hKt₂eq : Kt = K₂.1.1 := Subgroup.eq_of_le_of_card_ge hKt₂ hKtcard
      have h21 : K₂.1.1 ≤ K₁.1.1 := hKt₂eq ▸ hKt₁
      have hc : Nat.card K₁.1.1 ≤ Nat.card K₂.1.1 := by
        have h1 := hcardK K₁.1 K₁.2
        have h2 := hcardK K₂.1 K₂.2
        have hpos : 0 < Nat.card (sqs T) := Nat.card_pos
        exact (Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)).le
      exact Subtype.ext (Subtype.ext (Subgroup.eq_of_le_of_card_ge h21 hc).symm)
    have hZ : ∀ s : S, Nat.card (Z s) ≤ 2 ^ y₁ := by
      intro s
      have h := card_sqrt_le Rbar ((((s : T) ^ 2 : T) : T ⧸ KT)⁻¹)
      rw [card_tors2] at h
      have hcol : col Rbar 0 = y₁ := (col_congr 0 (sqsImageEquiv K')).symm
      rw [hcol] at h
      exact h
    letI : ∀ s : S, Finite (Z s) := fun s => inferInstance
    calc Nat.card {K : F // K.1 ⊔ (sqs T) = M.1}
        ≤ Nat.card ((s : S) → Z s) := Nat.card_le_card_of_injective code hcode
      _ = ∏ s : S, Nat.card (Z s) := Nat.card_pi
      _ ≤ ∏ _s : S, 2 ^ y₁ := Finset.prod_le_prod' (fun s _ => hZ s)
      _ = 2 ^ (y₁ * S.card) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
      _ ≤ 2 ^ (y₁ * (t₀ - y₀)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hSle)
  -- assemble
  let f : F → Mid := fun K => ⟨K.1 ⊔ (sqs T), le_sup_right, sup_le_mmax K.1 K' K.2.2, by
    have h := card_sup_sqs_mul K.1
    rw [K.2.1] at h
    exact h⟩
  have hfib : ∀ M : Mid, Nat.card {K // f K = M} ≤ 2 ^ (y₁ * (t₀ - y₀)) := by
    intro M
    refine le_trans (Nat.card_le_card_of_injective
      (fun K : {K // f K = M} => (⟨K.1, congrArg Subtype.val K.2⟩ : {K : F // K.1 ⊔ (sqs T) = M.1}))
      ?_) (hKcount M)
    intro K₁ K₂ h
    exact Subtype.ext (congrArg (fun x : {K : F // K.1 ⊔ sqs T = M.1} => x.1) h)
  calc Nat.card F ≤ Nat.card Mid * 2 ^ (y₁ * (t₀ - y₀)) := card_le_mul_of_fibres f _ hfib
    _ ≤ 2 ^ ((t₀ - y₀) * (y₀ - y₁) + 2) * 2 ^ (y₁ * (t₀ - y₀)) :=
        Nat.mul_le_mul_right _ hMid
    _ = 2 ^ (y₀ * (t₀ - y₀) + 2) := by
        rw [← pow_add]
        congr 1
        have : (t₀ - y₀) * (y₀ - y₁) + y₁ * (t₀ - y₀) = y₀ * (t₀ - y₀) := by
          rw [mul_comm y₁, ← Nat.mul_add, Nat.sub_add_cancel hy₁y₀, mul_comm]
        omega

end Layer

/-! ## The profile bound -/

/-- Quotient columns are at most the columns of the group. -/
theorem col_quotient_le : ∀ (k : ℕ) {T : Type u} [CommGroup T] [Finite T] (K : Subgroup T),
    col (T ⧸ K) k ≤ col T k
  | 0, _, _, _, K => col_quotient_zero_le K
  | k + 1, T, _, _, K => by
      rw [col_quotient_succ, col_succ]
      exact col_quotient_le k _

/-- **Quotient profiles.**  For `T` of exponent dividing `2^N`, the subgroups
`K` with prescribed quotient columns `y` number at most
`2^(∑_{k<N} (yₖ (colₖ T - yₖ) + 2))`. -/
theorem card_profileSet_le : ∀ (N : ℕ) (T : Type u) [CommGroup T] [Finite T], HasExp2 T N →
    ∀ y : ℕ → ℕ, Nat.card (ProfileSet T N y) ≤
      2 ^ (∑ k ∈ Finset.range N, (y k * (col T k - y k) + 2))
  | 0, T, _, _, hT, y => by
      haveI := subsingleton_of_hasExp2_zero hT
      haveI : Subsingleton (ProfileSet T 0 y) := ⟨fun K₁ K₂ => Subtype.ext (by
        ext x
        rw [Subsingleton.elim x 1]
        exact ⟨fun _ => K₂.1.one_mem, fun _ => K₁.1.one_mem⟩)⟩
      simpa using Finite.card_le_one_iff_subsingleton.mpr inferInstance
  | N + 1, T, _, _, hT, y => by
      have ih := card_profileSet_le N (sqs T) (hasExp2_sqs hT) (fun k => y (k + 1))
      let tr : ProfileSet T (N + 1) y → ProfileSet (sqs T) N (fun k => y (k + 1)) := fun K =>
        ⟨K.1.comap (sqs T).subtype, fun k hk => by
          rw [← col_quotient_succ]
          exact K.2 (k + 1) (by omega)⟩
      have hfib : ∀ K' : ProfileSet (sqs T) N (fun k => y (k + 1)),
          Nat.card {K // tr K = K'} ≤ 2 ^ (y 0 * (col T 0 - y 0) + 2) := by
        intro K'
        refine le_trans (Nat.card_le_card_of_injective
          (fun K : {K // tr K = K'} =>
            (⟨K.1.1, K.1.2 0 (by omega), congrArg Subtype.val K.2⟩ :
              {K : Subgroup T // col (T ⧸ K) 0 = y 0 ∧ K.comap (sqs T).subtype = K'.1}))
          ?_) (card_fibre_le (y 0) K'.1)
        intro K₁ K₂ h
        exact Subtype.ext (Subtype.ext (congrArg
          (fun x : {K : Subgroup T // col (T ⧸ K) 0 = y 0 ∧
            K.comap (sqs T).subtype = K'.1} => x.1) h))
      calc Nat.card (ProfileSet T (N + 1) y)
          ≤ Nat.card (ProfileSet (sqs T) N (fun k => y (k + 1))) *
              2 ^ (y 0 * (col T 0 - y 0) + 2) := card_le_mul_of_fibres tr _ hfib
        _ ≤ 2 ^ (∑ k ∈ Finset.range N, (y (k + 1) * (col (sqs T) k - y (k + 1)) + 2)) *
              2 ^ (y 0 * (col T 0 - y 0) + 2) := Nat.mul_le_mul_right _ ih
        _ = 2 ^ (∑ k ∈ Finset.range (N + 1), (y k * (col T k - y k) + 2)) := by
            rw [← pow_add, Finset.sum_range_succ']
            rfl

end MarkedC4
end SymmetricSubgroupAsymptotics
