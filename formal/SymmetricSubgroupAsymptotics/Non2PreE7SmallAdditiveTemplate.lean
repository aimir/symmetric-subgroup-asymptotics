import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogue
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank

/-!
# The small fixed-degree additive template

Several historical earlier owners of fixed small degree have, on every
complete source `J ≤ S_b`, the additive estimate

`Z_J(U) ≤ B Z_J(Q) + C 2^(θ b)`

for a comparator `Q` of smaller faithful degree.  On the literal normal
menu this means: every literal quotient `U/N` is either one literal quotient
of `Q` (it is then one summand of `Z_J(Q)`), or its onto maps obey a proved
source-independent tail `Epi(J, U/N) ≤ C_N 2^(θ b)`.

This file proves that template once.  It produces the ordinary
`PreE7EarlierActionComparatorCertificate`, hence an action of the mixed
local catalogue, together with the entry parameters and the cold tail gap
at the global `ρ = 1/8192`.

It also proves the reusable tail used by the dihedral owners.  Suppose the
derived subgroup `A = Q'` is self-centralizing, has no nontrivial fixed point
under conjugation, and carries one character `χ` whose conjugates separate
it.  Then an onto map `J → Q` is determined, up to the automorphisms of `Q`,
by one character of the derived subgroup `J'`.  Hence
`|Epi(J,Q)| ≤ |Aut Q| · |Hom(J', C_p)|`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

/-! ## A derived cyclic-dual onto bound -/

/-- A derived subgroup which is self-centralizing, has no nontrivial fixed
point under conjugation, and carries a character whose conjugates separate
it. -/
structure DerivedCyclicDual (Q : Type*) [Group Q] (p : ℕ) where
  character : commutator Q →* Multiplicative (ZMod p)
  self_centralizing : ∀ q : Q, (∀ a : commutator Q, q * a = a * q) → q ∈ commutator Q
  no_fixed : ∀ a : commutator Q, (∀ q : Q, q * (a : Q) * q⁻¹ = (a : Q)) → a = 1
  separating : ∀ a : commutator Q,
    (∀ q : Q, character (MulAut.conjNormal q a) = 1) → a = 1

namespace DerivedCyclicDual

variable {Q : Type*} [Group Q] {p : ℕ} (D : DerivedCyclicDual Q p)
  {J : Type*} [Group J]

omit D in
/-- An onto map carries the derived subgroup onto the derived subgroup. -/
theorem map_commutator_of_surjective (φ : J →* Q) (hφ : Function.Surjective φ) :
    (commutator J).map φ = commutator Q := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ hφ]

/-- The restriction of an onto map to the derived subgroups. -/
def derivedRestriction (φ : GroupEpimorphism J Q) :
    commutator J →* commutator Q :=
  (φ.1.comp (commutator J).subtype).codRestrict (commutator Q) (by
    intro k
    have hmem : φ.1 k ∈ (commutator J).map φ.1 := ⟨k, k.2, rfl⟩
    rwa [map_commutator_of_surjective φ.1 φ.2] at hmem)

theorem derivedRestriction_surjective (φ : GroupEpimorphism J Q) :
    Function.Surjective (derivedRestriction φ) := by
  rintro ⟨a, ha⟩
  rw [← map_commutator_of_surjective φ.1 φ.2] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact ⟨⟨k, hk⟩, rfl⟩

/-- The single character label of an onto map. -/
def label (φ : GroupEpimorphism J Q) : commutator J →* Multiplicative (ZMod p) :=
  D.character.comp (derivedRestriction φ)

theorem derivedRestriction_eq_one_iff (φ : GroupEpimorphism J Q)
    (k : commutator J) :
    derivedRestriction φ k = 1 ↔
      ∀ g : J, D.label φ (MulAut.conjNormal g k) = 1 := by
  constructor
  · intro hk g
    have heq : derivedRestriction φ (MulAut.conjNormal g k) =
        MulAut.conjNormal (φ.1 g) (derivedRestriction φ k) := by
      apply Subtype.ext
      simp [derivedRestriction]
    simp only [label, MonoidHom.comp_apply, heq, hk, map_one]
  · intro h
    apply D.separating
    intro q
    obtain ⟨g, rfl⟩ := φ.2 q
    have heq : derivedRestriction φ (MulAut.conjNormal g k) =
        MulAut.conjNormal (φ.1 g) (derivedRestriction φ k) := by
      apply Subtype.ext
      simp [derivedRestriction]
    rw [← heq]
    exact h g

/-- Equal labels give equal onto kernels. -/
theorem ker_le_of_label_eq (φ φ' : GroupEpimorphism J Q)
    (h : D.label φ = D.label φ') : φ.1.ker ≤ φ'.1.ker := by
  have hker : ∀ k : commutator J,
      derivedRestriction φ k = 1 ↔ derivedRestriction φ' k = 1 := by
    intro k
    rw [D.derivedRestriction_eq_one_iff, D.derivedRestriction_eq_one_iff, h]
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  -- the image centralizes the derived subgroup
  have hcent : ∀ a : commutator Q, φ'.1 g * a = a * φ'.1 g := by
    intro a
    obtain ⟨k, rfl⟩ := derivedRestriction_surjective φ' a
    have hc : ⁅g, (k : J)⁆ ∈ commutator J :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)
    have h1 : derivedRestriction φ ⟨_, hc⟩ = 1 := by
      apply Subtype.ext
      simp [derivedRestriction, commutatorElement_def, hg]
    have h2 := (hker ⟨_, hc⟩).mp h1
    have h3 := congrArg Subtype.val h2
    simp only [derivedRestriction, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, commutatorElement_def, map_mul, map_inv,
      OneMemClass.coe_one] at h3
    change φ'.1 g * φ'.1 k = φ'.1 k * φ'.1 g
    calc φ'.1 g * φ'.1 k
        = (φ'.1 g * φ'.1 k * (φ'.1 g)⁻¹ * (φ'.1 k)⁻¹) * (φ'.1 k * φ'.1 g) := by group
      _ = φ'.1 k * φ'.1 g := by rw [h3, one_mul]
  have hmem := D.self_centralizing _ hcent
  -- the image is fixed by conjugation
  let a : commutator Q := ⟨φ'.1 g, hmem⟩
  have hfix : ∀ q : Q, q * (a : Q) * q⁻¹ = (a : Q) := by
    intro q
    obtain ⟨h', rfl⟩ := φ'.2 q
    have hc : ⁅h', g⁆ ∈ commutator J :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top g)
    have h1 : derivedRestriction φ ⟨_, hc⟩ = 1 := by
      apply Subtype.ext
      simp [derivedRestriction, commutatorElement_def, hg]
    have h2 := congrArg Subtype.val ((hker ⟨_, hc⟩).mp h1)
    simp only [derivedRestriction, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, commutatorElement_def, map_mul, map_inv,
      OneMemClass.coe_one] at h2
    change φ'.1 h' * φ'.1 g * (φ'.1 h')⁻¹ = φ'.1 g
    calc φ'.1 h' * φ'.1 g * (φ'.1 h')⁻¹
        = (φ'.1 h' * φ'.1 g * (φ'.1 h')⁻¹ * (φ'.1 g)⁻¹) * φ'.1 g := by group
      _ = φ'.1 g := by rw [h2, one_mul]
  exact congrArg Subtype.val (D.no_fixed _ hfix)

include D in
/-- `|Epi(J, Q)| ≤ |Aut Q| · |Hom(J', C_p)|`. -/
theorem epi_card_le [Finite J] [Finite Q] [NeZero p] :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (commutator J →* Multiplicative (ZMod p)) * Nat.card (Q ≃* Q) := by
  letI : Finite (commutator J →* Multiplicative (ZMod p)) :=
    Finite.of_injective (fun f : commutator J →* Multiplicative (ZMod p) =>
      (f : commutator J → Multiplicative (ZMod p))) DFunLike.coe_injective
  exact groupEpimorphism_card_le_kernel_labels D.label (fun φ φ' h =>
    le_antisymm (D.ker_le_of_label_eq φ φ' h) (D.ker_le_of_label_eq φ' φ h.symm))

end DerivedCyclicDual

/-- Characters of a finite group into a cyclic group of order `n` number at
most the order of its abelianization. -/
theorem cyclicCharacter_card_le_abelianization (G : Type*) [Group G] [Finite G]
    (n : ℕ) [NeZero n] :
    Nat.card (G →* Multiplicative (ZMod n)) ≤ Nat.card (Abelianization G) := by
  rw [Nat.card_congr (AddMonoidHom.toMultiplicativeRight (α := G)
    (β := ZMod n)).symm]
  exact addMonoidHom_zmod_card_le_abelianization G n

/-- Kovács--Praeger for the derived subgroup of an actual `J ≤ S_b`. -/
theorem derived_abelianization_le (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (Abelianization (commutator J)) : ℝ) ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := by
  let D : Subgroup (Equiv.Perm (Fin b)) := (commutator J).map J.subtype
  let e : commutator J ≃* D :=
    Subgroup.equivMapOfInjective (commutator J) J.subtype Subtype.val_injective
  have hcard : Nat.card (Abelianization (commutator J)) = Nat.card (Abelianization D) :=
    Nat.card_congr (MulEquiv.abelianizationCongr e).toEquiv
  rw [hcard]
  exact hKP b D

/-- Onto maps to a group of order at most two: at most `2^(b/2)`. -/
theorem groupEpimorphism_card_le_of_card_le_two {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q ≤ 2) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
  have htwo : IsPGroup 2 Q := by
    rcases Nat.lt_or_ge (Nat.card Q) 2 with h | h
    · have h1 : Nat.card Q = 1 := by
        have := Nat.card_pos (α := Q)
        omega
      exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · exact IsPGroup.of_card (n := 1) (by simpa using le_antisymm hQ h)
  have hhom := binaryTargetOrder_hom_card_le (J := J) htwo
  have hlog : Nat.log 2 (Nat.card Q) ≤ 1 :=
    (Nat.log_mono_right hQ).trans (by norm_num)
  have hrank := permutation_binaryCharacterRank_le_half J (Fin b)
  rw [Nat.card_fin] at hrank
  have hrank' : binaryCharacterRank J ≤ b / 2 := hrank
  have hepi : Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := by
    letI : Finite (J →* Q) := Finite.of_injective
      (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hnat : Nat.card (GroupEpimorphism J Q) ≤ 2 ^ (b / 2) :=
    hepi.trans (hhom.trans (Nat.pow_le_pow_right (by norm_num)
      ((Nat.mul_le_mul_right _ hlog).trans (by simpa using hrank'))))
  calc (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ ((2 ^ (b / 2) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = (2 : ℝ) ^ (((b / 2 : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
        push_cast
        rfl
    _ ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have := Nat.cast_div_le (m := b) (n := 2) (α := ℝ)
        push_cast at this
        linarith

namespace Non2UnipotentPrefixFiniteMenu

/-! ## The per-axis certificates -/

/-- One fixed certificate on a literal normal axis: either the quotient is a
literal quotient of the comparator, or its onto maps obey a proved tail of
slope `θ`. -/
inductive PreE7SmallAxisCertificate {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (N : {N : Subgroup U // N.Normal}) (R : Type) [Group R] (θ : ℝ) : Type
  | comparator (M : {M : Subgroup R // M.Normal}) (e : (U ⧸ N.1) ≃* (R ⧸ M.1))
  | tail (C : ℝ) (hC : 0 ≤ C)
      (bound : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤ C * (2 : ℝ) ^ (θ * b))

namespace PreE7SmallAxisCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  {N : {N : Subgroup U // N.Normal}} {R : Type} [Group R] {θ : ℝ}

/-- The comparator coefficient. -/
def mainCoefficient : PreE7SmallAxisCertificate U N R θ → ℝ
  | .comparator _ _ => 1
  | .tail _ _ _ => 0

/-- The tail coefficient. -/
def tailCoefficient : PreE7SmallAxisCertificate U N R θ → ℝ
  | .comparator _ _ => 0
  | .tail C _ _ => C

theorem mainCoefficient_nonneg (c : PreE7SmallAxisCertificate U N R θ) :
    0 ≤ c.mainCoefficient := by
  cases c <;> simp [mainCoefficient]

theorem tailCoefficient_nonneg (c : PreE7SmallAxisCertificate U N R θ) :
    0 ≤ c.tailCoefficient := by
  cases c with
  | comparator => simp [tailCoefficient]
  | tail C hC _ => exact hC

theorem envelope [Finite R] (c : PreE7SmallAxisCertificate U N R θ) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
      (c.mainCoefficient * (2 : ℝ) ^ ((0 : ℝ) * b)) *
          completeQuotientWeight (R := R) J +
        c.tailCoefficient * (2 : ℝ) ^ (θ * b) := by
  cases c with
  | comparator M e =>
    simp only [mainCoefficient, tailCoefficient, zero_mul, Real.rpow_zero,
      mul_one, one_mul, add_zero]
    exact card_groupEpimorphism_le_completeQuotientWeight J M e
  | tail C hC hbound =>
    simp only [mainCoefficient, tailCoefficient, zero_mul, zero_add]
    exact hbound b J

end PreE7SmallAxisCertificate

/-! ## Template data and the certificate -/

/-- One literal retained action with a small comparator and a fixed axis
certificate on every literal normal quotient. -/
structure PreE7SmallAdditiveData (w : ℕ) (i : PreE7NonPairActionClass w) :
    Type 1 where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  degree : ℕ
  action : R →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  tailSlope : ℝ
  comparator_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  tail_window : tailSlope ≤ preE7CharacterWindow w
  axis : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N R tailSlope

attribute [instance] PreE7SmallAdditiveData.groupR PreE7SmallAdditiveData.finiteR

namespace PreE7SmallAdditiveData

variable {w : ℕ} {i : PreE7NonPairActionClass w} (D : PreE7SmallAdditiveData w i)

/-- The comparator degree after the two-point floor. -/
def sourceDegree : ℕ := max 2 D.degree

/-- The padded comparator degree. -/
def paddedDegree : ℕ := paddedComparatorDegree preE7CharacterRho D.sourceDegree w

/-- The padded residual margin. -/
def delta : ℝ := paddedComparatorDelta preE7CharacterRho 0 D.sourceDegree w

/-- The hot/cold threshold exponent. -/
def cutoff : ℝ := (D.paddedDegree : ℝ) / 8 + D.delta / 2

theorem degree_le : D.degree ≤ D.paddedDegree :=
  (le_max_right 2 D.degree).trans (le_max_left _ _)

/-- The per-axis additive envelope on the broad source. -/
theorem axis_envelope (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
      ((D.axis N).mainCoefficient * (2 : ℝ) ^ ((0 : ℝ) * b)) *
          completeQuotientWeight (R := D.R) J +
        (D.axis N).tailCoefficient * (2 : ℝ) ^ (D.tailSlope * b) :=
  (fusionSurvivingEpiCount_le_groupEpimorphism_card _ _ N J).trans
    ((D.axis N).envelope J)

/-- The ordinary family certificate of the small additive template. -/
def certificate (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7EarlierActionComparatorCertificate family w i where
  R := D.R
  v := D.paddedDegree
  action := (characterComparatorPadHom D.degree_le).comp D.action
  action_injective := (characterComparatorPadHom_injective _).comp D.action_injective
  C := fun _ N => (D.axis N).mainCoefficient
  tailCoefficient := fun _ N => (D.axis N).tailCoefficient
  eta := 0
  delta := D.delta
  cutoff := D.cutoff
  alpha := 0 + D.cutoff
  theta := D.tailSlope
  alpha_eq := rfl
  coefficient_nonneg := fun _ N => (D.axis N).mainCoefficient_nonneg
  tail_nonneg := fun _ N => (D.axis N).tailCoefficient_nonneg
  broad_axis_envelope := fun b N J => D.axis_envelope b N J

include D in
/-- The action is accepted by the mixed local catalogue. -/
theorem localFamilyAction (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    preE7NoPairNoC3EarlierLocalFamilyAction family w i :=
  preE7EarlierLocalFamilyAction_ofComparator (D.certificate family)

/-- The certificate meets every transfer parameter at `ρ = 1/8192`, and its
tail slope meets the cold gap. -/
theorem entryParameters (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (D.certificate family).v (D.certificate family).eta
      (D.certificate family).delta (D.certificate family).cutoff
      (D.certificate family).alpha (D.certificate family).theta := by
  let ι : ℕ → Type := fun w' => {_u : Unit // w' = w}
  have hP := growingPadded_parameterBound (ι := ι) (ρ := preE7CharacterRho)
    (fun _ _ => D.sourceDegree) (fun _ _ => (0 : ℝ))
    (by norm_num [preE7CharacterRho]) (by norm_num [preE7CharacterRho])
    (fun _ _ => le_rfl) (fun _ _ => le_max_left _ _)
    (by
      rintro w' ⟨_, rfl⟩
      show preE7CharacterRho * w' ≤ ((evenWidth w' : ℝ) - (D.sourceDegree : ℝ)) / 8 - 0
      rw [sub_zero]
      exact D.comparator_window)
  let j : ι w := ⟨(), rfl⟩
  exact
    { delta_nonneg := hP.delta_nonneg w j
      degree_pos := hP.degree_pos w j
      ratio := hP.ratio w j
      degree_upper := hP.degree_upper w j
      delta_lower := hP.delta_lower w j
      hot_margin := hP.hot_margin w j
      threshold_eq := hP.threshold_eq w j
      delta_upper := hP.delta_upper w j
      degree_lower := hP.degree_lower w j
      degree_width := hP.degree_width w j
      cold_slope := hP.cold_slope w j
      cold_gap := hP.cold_gap w j
      tail_gap := D.tail_window }

/-- All coefficients are bounded independently of the complement degree. -/
theorem coefficient_bounded :
    ∃ K : ℝ, ∀ N, (D.axis N).mainCoefficient ≤ K ∧ (D.axis N).tailCoefficient ≤ K := by
  refine ⟨1 + ∑ N, (D.axis N).tailCoefficient, fun N => ?_⟩
  have hsum : (D.axis N).tailCoefficient ≤ ∑ N, (D.axis N).tailCoefficient :=
    Finset.single_le_sum (f := fun N => (D.axis N).tailCoefficient)
      (fun N _ => (D.axis N).tailCoefficient_nonneg) (Finset.mem_univ N)
  have hnonneg : 0 ≤ ∑ N, (D.axis N).tailCoefficient :=
    Finset.sum_nonneg (fun N _ => (D.axis N).tailCoefficient_nonneg)
  constructor
  · cases h : D.axis N <;> simp [PreE7SmallAxisCertificate.mainCoefficient] <;>
      linarith
  · linarith

end PreE7SmallAdditiveData

/-- A comparator which never occurs: the trivial group on two points.  It is
used by owners whose every axis carries a tail. -/
def trivialSmallComparatorWindow {w : ℕ} (hw : 6 ≤ w) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - ((max 2 0 : ℕ) : ℝ)) / 8 := by
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hw' : (6 : ℝ) ≤ w := by exact_mod_cast hw
  unfold preE7CharacterRho
  norm_num
  linarith

/-- The slope `log₂ 3 / 3` meets the cold gap at every width at least six. -/
theorem logThreeThird_le_window {w : ℕ} (hw : 6 ≤ w) :
    Real.logb 2 3 / 3 ≤ preE7CharacterWindow w := by
  have hlog : Real.logb 2 3 < 8 / 5 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    have : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 3 ^ 5) this
      (by norm_num : (0 : ℝ) < 1 / 5)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hhalf : (w : ℝ) ≤ 2 * halfDegree w + 1 := by
    have : w ≤ 2 * halfDegree w + 1 := by
      unfold halfDegree
      omega
    exact_mod_cast this
  have hw' : (6 : ℝ) ≤ w := by exact_mod_cast hw
  unfold preE7CharacterWindow preE7CharacterRho
  linarith

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
