import SymmetricSubgroupAsymptotics.DegreeTwelveFourBlockFullness

/-!
# The whole ternary quotient on the nine ambient local translations

A translation is a block together with one of the three nonidentity Klein
translations on its four original points. Ambient transport conjugates these
local translations. Its kernel is the intrinsic binary core, so the action
factors faithfully through the WHOLE quotient A/W. This is not the block-top
C3 action. Full local A4 images make this quotient action transitive.

Individual supported translations are ambient permutations; they are not
assumed to belong to the possibly correlated original core.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeTwelveNineTranslations

open DegreeTwelveFourBlockCore DegreeTwelveFourBlockFullness

abbrev LocalTranslation := {v : V4 // v ≠ 1}

private theorem klein_conjugate_mem (g : Equiv.Perm (Fin 4)) (v : V4) :
    MulAut.conjNormal g (v : A4) ∈ V4 := by
  have hchar : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by simp)
  exact (Subgroup.characteristic_iff_le_comap.mp hchar (MulAut.conjNormal g)) v.2

private theorem klein_square (v : V4) : v ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one v
  rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)] at h
  exact h

private theorem even_square_mem_klein (v : A4) (hv : v ^ 2 = 1) : v ∈ V4 := by
  have hperm : (v : Equiv.Perm (Fin 4)) ^ 2 = 1 := congrArg Subtype.val hv
  have hd : orderOf (v : Equiv.Perm (Fin 4)) ∣ 2 ^ 1 := by
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one hperm
  have htypes := alternatingGroup.mem_kleinFour_of_order_two_pow
    (by simp : Nat.card (Fin 4) = 4) v.2 hd
  rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
  rcases htypes with h | h
  · left
    exact Subtype.ext (Equiv.Perm.cycleType_eq_zero.mp h)
  · exact Or.inr h

private theorem local_even (v : LocalTranslation) :
    Equiv.Perm.sign (((v.val : V4) : A4) : Equiv.Perm (Fin 4)) = 1 :=
  Equiv.Perm.mem_alternatingGroup.mp v.val.val.property

private theorem local_square (v : LocalTranslation) :
    ((((v.val : V4) : A4) : Equiv.Perm (Fin 4))) ^ 2 = 1 :=
  congrArg (fun z : V4 => ((z : A4) : Equiv.Perm (Fin 4))) (klein_square v.val)

private theorem local_ne_one (v : LocalTranslation) :
    (((v.val : V4) : A4) : Equiv.Perm (Fin 4)) ≠ 1 := by
  intro h
  exact v.2 (Subtype.ext (Subtype.ext h))

/-- This adapter has no enumeration of the noncomputable closure subtype. -/
private def translationOf (v : Equiv.Perm (Fin 4))
    (heven : Equiv.Perm.sign v = 1) (hsquare : v ^ 2 = 1) (hne : v ≠ 1) :
    LocalTranslation :=
  ⟨⟨⟨v, Equiv.Perm.mem_alternatingGroup.mpr heven⟩,
      even_square_mem_klein ⟨v, Equiv.Perm.mem_alternatingGroup.mpr heven⟩
        (Subtype.ext hsquare)⟩,
    fun h => hne (congrArg (fun z : V4 => ((z : A4) : Equiv.Perm (Fin 4))) h)⟩

/-- All finite computation below is on plain permutations, never on the
subtype defined by a subgroup closure or on a noncomputable Fintype. -/
private theorem fourPoint_centralizer_test (g : Equiv.Perm (Fin 4)) :
    (∀ v : Equiv.Perm (Fin 4), Equiv.Perm.sign v = 1 → v ^ 2 = 1 → v ≠ 1 →
      g * v * g⁻¹ = v) ↔ Equiv.Perm.sign g = 1 ∧ g ^ 2 = 1 := by
  decide +kernel +revert

private theorem fourPoint_nontrivial_even_square_moves (v : Equiv.Perm (Fin 4))
    (heven : Equiv.Perm.sign v = 1) (hsquare : v ^ 2 = 1) (hne : v ≠ 1)
    (i : Fin 4) : v i ≠ i := by
  decide +kernel +revert

private theorem fourPoint_even_conjugator (v w : Equiv.Perm (Fin 4))
    (hveven : Equiv.Perm.sign v = 1) (hvsquare : v ^ 2 = 1) (hvne : v ≠ 1)
    (hweven : Equiv.Perm.sign w = 1) (hwsquare : w ^ 2 = 1) (hwne : w ≠ 1) :
    ∃ g : Equiv.Perm (Fin 4), Equiv.Perm.sign g = 1 ∧ g * v * g⁻¹ = w := by
  decide +kernel +revert

/-- Conjugation by any four-point bijection preserves the original Klein
translations, including odd changes of the local point chart. -/
def kleinConjugation (g : Equiv.Perm (Fin 4)) : MulAut V4 where
  toFun v := ⟨MulAut.conjNormal g (v : A4), klein_conjugate_mem g v⟩
  invFun v := ⟨MulAut.conjNormal g⁻¹ (v : A4), klein_conjugate_mem g⁻¹ v⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change g⁻¹ * (g * ((v : A4) : Equiv.Perm (Fin 4)) * g⁻¹) * g = _
    group
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change g * (g⁻¹ * ((v : A4) : Equiv.Perm (Fin 4)) * g) * g⁻¹ = _
    group
  map_mul' v w := by
    apply Subtype.ext
    apply Subtype.ext
    change g * (((v : A4) : Equiv.Perm (Fin 4)) * ((w : A4) : Equiv.Perm (Fin 4))) * g⁻¹ =
      (g * ((v : A4) : Equiv.Perm (Fin 4)) * g⁻¹) *
        (g * ((w : A4) : Equiv.Perm (Fin 4)) * g⁻¹)
    group

@[simp] theorem kleinConjugation_one : kleinConjugation 1 = 1 := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  change 1 * ((v : A4) : Equiv.Perm (Fin 4)) * 1⁻¹ = _
  simp

theorem kleinConjugation_mul (g h : Equiv.Perm (Fin 4)) :
    kleinConjugation (g * h) = kleinConjugation g * kleinConjugation h := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  change (g * h) * ((v : A4) : Equiv.Perm (Fin 4)) * (g * h)⁻¹ =
    g * (h * ((v : A4) : Equiv.Perm (Fin 4)) * h⁻¹) * g⁻¹
  group

/-- The literal permutation of the three nonidentity local translations. -/
def localConjugation : Equiv.Perm (Fin 4) →* Equiv.Perm LocalTranslation where
  toFun g := {
    toFun := fun v => ⟨kleinConjugation g v, by
      intro h
      apply v.2
      apply (kleinConjugation g).injective
      exact h.trans (kleinConjugation g).map_one.symm⟩
    invFun := fun v => ⟨(kleinConjugation g).symm v, by
      intro h
      apply v.2
      apply (kleinConjugation g).symm.injective
      exact h.trans (kleinConjugation g).symm.map_one.symm⟩
    left_inv := fun v => Subtype.ext ((kleinConjugation g).symm_apply_apply v)
    right_inv := fun v => Subtype.ext ((kleinConjugation g).apply_symm_apply v) }
  map_one' := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun f : MulAut V4 => f v) kleinConjugation_one
  map_mul' g h := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun f : MulAut V4 => f v) (kleinConjugation_mul g h)

/-- The finite local kernel is the Klein group, characterized intrinsically
by evenness and square one. -/
theorem localConjugation_eq_one_iff (g : Equiv.Perm (Fin 4)) :
    localConjugation g = 1 ↔ g ∈ alternatingGroup (Fin 4) ∧ g ^ 2 = 1 := by
  constructor
  · intro h
    have hc : ∀ v : Equiv.Perm (Fin 4), Equiv.Perm.sign v = 1 → v ^ 2 = 1 →
        v ≠ 1 → g * v * g⁻¹ = v := by
      intro v heven hsquare hne
      let t := translationOf v heven hsquare hne
      have ht := congrArg (fun f : Equiv.Perm LocalTranslation => f t) h
      exact congrArg
        (fun z : LocalTranslation => (((z.val : V4) : A4) : Equiv.Perm (Fin 4))) ht
    have hg := (fourPoint_centralizer_test g).mp hc
    exact ⟨Equiv.Perm.mem_alternatingGroup.mpr hg.1, hg.2⟩
  · rintro ⟨heven, hsquare⟩
    have hc := (fourPoint_centralizer_test g).mpr
      ⟨Equiv.Perm.mem_alternatingGroup.mp heven, hsquare⟩
    apply Equiv.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hc _ (local_even v) (local_square v) (local_ne_one v)

theorem localTranslation_card : Nat.card LocalTranslation = 3 := by
  have hv : Nat.card V4 = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  rw [Nat.card_eq_fintype_card] at hv ⊢
  rw [Fintype.card_subtype_compl (fun v : V4 => v = 1)]
  simp only [Fintype.card_unique, hv]

private theorem localTranslation_moves (v : LocalTranslation) (i : Fin 4) :
    (((v.val : V4) : A4) : Equiv.Perm (Fin 4)) i ≠ i := by
  exact fourPoint_nontrivial_even_square_moves _
    (local_even v) (local_square v) (local_ne_one v) i

private theorem a4_transitive_local (v w : LocalTranslation) :
    ∃ g : A4, localConjugation (g : Equiv.Perm (Fin 4)) v = w := by
  obtain ⟨g, hgEven, hg⟩ := fourPoint_even_conjugator _ _
    (local_even v) (local_square v) (local_ne_one v)
    (local_even w) (local_square w) (local_ne_one w)
  refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hgEven⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hg

section AmbientAction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x)

abbrev Translations := X × LocalTranslation

/-- The supported local translation on the ORIGINAL point type. Its support
is contained in its literal fibre; it need not lie in the original group. -/
def originalLocalPermutation (s : Translations (X := X)) : Equiv.Perm Ω :=
  (((s.2.val : V4) : A4) : Equiv.Perm (Fin 4)).extendDomain (e s.1)

@[simp] theorem originalLocalPermutation_on_fibre (x : X) (v : LocalTranslation)
    (i : Fin 4) :
    originalLocalPermutation b e (x, v) ((e x i : originalBlockFibre b x) : Ω) =
      ((e x ((((v.val : V4) : A4) : Equiv.Perm (Fin 4)) i) : originalBlockFibre b x) : Ω) :=
  Equiv.Perm.extendDomain_apply_image _ _ i

theorem originalLocalPermutation_off_fibre (x : X) (v : LocalTranslation)
    (ω : Ω) (hω : b ω ≠ x) : originalLocalPermutation b e (x, v) ω = ω :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ hω

/-- Distinct block/translation labels give distinct ambient permutations.
Thus the nine-point action below really labels nine original supported
translations, including when the original core has fewer than 64 elements. -/
theorem originalLocalPermutation_injective :
    Function.Injective (originalLocalPermutation b e) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  have hxy : x = y := by
    by_contra hxy
    have hv : originalLocalPermutation b e (x, v) (e x 0).val ≠ (e x 0).val := by
      intro he
      apply localTranslation_moves v 0
      apply (e x).injective
      apply Subtype.ext
      simpa only [originalLocalPermutation_on_fibre] using he
    apply hv
    have he := congrArg (fun f : Equiv.Perm Ω => f (e x 0).val) h
    exact he.trans (originalLocalPermutation_off_fibre b e y w (e x 0).val
      (by rw [(e x 0).2]; exact hxy))
  subst y
  apply Prod.ext
  · rfl
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have he := congrArg (fun f : Equiv.Perm Ω => f (e x i).val) h
  change originalLocalPermutation b e (x, v) (e x i).val =
    originalLocalPermutation b e (x, w) (e x i).val at he
  rw [originalLocalPermutation_on_fibre, originalLocalPermutation_on_fibre] at he
  exact (e x).injective (Subtype.ext he)

/-- Whole-A transport of the ambient translations, retaining the original
block and point charts. -/
def ambientAction : A →* Equiv.Perm (Translations (X := X)) where
  toFun a := {
    toFun := fun s => (a • s.1, localConjugation (transition b hb e a s.1) s.2)
    invFun := fun s => (a⁻¹ • s.1, localConjugation (transition b hb e a⁻¹ s.1) s.2)
    left_inv := by
      rintro ⟨x, v⟩
      apply Prod.ext
      · exact inv_smul_smul a x
      · have h := transition_mul b hb e a⁻¹ a x
        rw [inv_mul_cancel, transition_one] at h
        have hc : localConjugation (transition b hb e a⁻¹ (a • x)) *
            localConjugation (transition b hb e a x) = 1 := by
          rw [← map_mul, ← h, map_one]
        exact congrArg (fun f : Equiv.Perm LocalTranslation => f v) hc
    right_inv := by
      rintro ⟨x, v⟩
      apply Prod.ext
      · exact smul_inv_smul a x
      · have h := transition_mul b hb e a a⁻¹ x
        rw [mul_inv_cancel, transition_one] at h
        have hc : localConjugation (transition b hb e a (a⁻¹ • x)) *
            localConjugation (transition b hb e a⁻¹ x) = 1 := by
          rw [← map_mul, ← h, map_one]
        exact congrArg (fun f : Equiv.Perm LocalTranslation => f v) hc }
  map_one' := by
    apply Equiv.ext
    rintro ⟨x, v⟩
    apply Prod.ext
    · exact one_smul A x
    · change localConjugation (transition b hb e 1 x) v = v
      rw [transition_one, map_one]
      rfl
  map_mul' a c := by
    apply Equiv.ext
    rintro ⟨x, v⟩
    apply Prod.ext
    · exact mul_smul a c x
    · change localConjugation (transition b hb e (a * c) x) v =
        localConjugation (transition b hb e a (c • x))
          (localConjugation (transition b hb e c x) v)
      rw [transition_mul, map_mul]
      rfl

@[simp] theorem ambientAction_apply (a : A) (s : Translations (X := X)) :
    ambientAction b hb e a s =
      (a • s.1, localConjugation (transition b hb e a s.1) s.2) := rfl

/-- For a kernel element the ambient transport is the original local
permutation coordinate, without passing to the block-top quotient. -/
theorem transition_kernel (k : Kernel (A := A) (X := X)) (x : X) :
    transition b hb e (k : A) x = fibreCoordinate b hb e x k := by
  have hx : (k : A) • x = x := congrArg (fun f : Equiv.Perm X => f x) k.2
  have hchart (j : Fin 4) : (e ((k : A) • x) j).val = (e x j).val := by
    rw [hx]
  apply Equiv.ext
  intro i
  apply (e ((k : A) • x)).injective
  apply Subtype.ext
  rw [transition_apply_chart, hchart]
  change (k : A) • (e x i).val =
    (e x ((e x).symm (OriginalBlockClassBound.coordinate b hb x k (e x i)))).val
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] theorem ambientAction_kernel_apply (k : Kernel (A := A) (X := X))
    (s : Translations (X := X)) :
    ambientAction b hb e (k : A) s =
      (s.1, localConjugation (fibreCoordinate b hb e s.1 k) s.2) := by
  rw [ambientAction_apply, transition_kernel]
  have hx : (k : A) • s.1 = s.1 := congrArg (fun f : Equiv.Perm X => f s.1) k.2
  rw [hx]

/-- The chart action is exactly conjugation of each supported original
local translation. No supported translation is claimed to lie in A. -/
theorem originalLocalPermutation_conjugation (a : A) (s : Translations (X := X)) :
    originalLocalPermutation b e (ambientAction b hb e a s) =
      MulAction.toPermHom A Ω a * originalLocalPermutation b e s *
        (MulAction.toPermHom A Ω a)⁻¹ := by
  rcases s with ⟨x, v⟩
  apply Equiv.ext
  intro ω
  by_cases hω : b ω = a • x
  · let j := (e (a • x)).symm ⟨ω, hω⟩
    have hj : ((e (a • x) j : originalBlockFibre b (a • x)) : Ω) = ω := by
      exact congrArg Subtype.val ((e (a • x)).apply_symm_apply ⟨ω, hω⟩)
    rw [← hj]
    rw [show ambientAction b hb e a (x, v) =
      (a • x, localConjugation (transition b hb e a x) v) from rfl]
    rw [originalLocalPermutation_on_fibre]
    change ((e (a • x)
      ((transition b hb e a x * (((v.val : V4) : A4) : Equiv.Perm (Fin 4)) *
        (transition b hb e a x)⁻¹) j)).val) =
      a • (originalLocalPermutation b e (x, v) (a⁻¹ • (e (a • x) j).val))
    have hpre : a⁻¹ • (e (a • x) j).val =
        (e x ((transition b hb e a x)⁻¹ j)).val := by
      apply (MulAction.injective a)
      change a • (a⁻¹ • (e (a • x) j).val) =
        a • (e x ((transition b hb e a x)⁻¹ j)).val
      rw [smul_inv_smul]
      have h := transition_apply_chart b hb e a x ((transition b hb e a x)⁻¹ j)
      have hcancel : (transition b hb e a x) ((transition b hb e a x)⁻¹ j) = j :=
        (transition b hb e a x).apply_symm_apply j
      rw [hcancel] at h
      exact h
    rw [hpre, originalLocalPermutation_on_fibre]
    simp only [Equiv.Perm.mul_apply]
    exact transition_apply_chart b hb e a x _
  · have hpre : b (a⁻¹ • ω) ≠ x := by
      intro h
      apply hω
      calc
        b ω = b (a • (a⁻¹ • ω)) := by rw [smul_inv_smul]
        _ = a • b (a⁻¹ • ω) := hb a (a⁻¹ • ω)
        _ = a • x := congrArg (fun y : X => a • y) h
    change originalLocalPermutation b e
      (a • x, localConjugation (transition b hb e a x) v) ω =
        a • (originalLocalPermutation b e (x, v) (a⁻¹ • ω))
    rw [originalLocalPermutation_off_fibre b e _ _ _ hω,
      originalLocalPermutation_off_fibre b e _ _ _ hpre, smul_inv_smul]

end AmbientAction

section Quotient

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x) (hEven : AllEven b hb e)

abbrev originalCore := core (MulAction.toPermHom A X)
  (alternatingCoordinates b hb e hEven) (alternatingCoordinates_injective b hb e hEven)

/-- Exactly the original intrinsic binary core acts trivially on the
ambient local translations. This retains the whole quotient, not only its
permutation action on the blocks. -/
theorem ambientAction_ker : (ambientAction b hb e).ker = originalCore b hb e hEven := by
  ext a
  constructor
  · intro ha
    have he : ambientAction b hb e a = 1 := ha
    obtain ⟨v⟩ : Nonempty LocalTranslation :=
      (Nat.card_pos_iff.mp (by rw [localTranslation_card]; omega)).1
    have hak : a ∈ (MulAction.toPermHom A X).ker := by
      apply Equiv.ext
      intro x
      exact congrArg Prod.fst (congrArg (fun f => f (x, v)) he)
    let k : Kernel (A := A) (X := X) := ⟨a, hak⟩
    refine ⟨hak, ?_⟩
    have hk2 : k ^ 2 = 1 := by
      apply OriginalBlockClassBound.coordinates_injective b hb
      funext x
      apply (e x).symm.permCongrHom.injective
      change fibreCoordinate b hb e x (k ^ 2) = fibreCoordinate b hb e x 1
      rw [map_pow, map_one]
      have hc : localConjugation (fibreCoordinate b hb e x k) = 1 := by
        apply Equiv.ext
        intro w
        have h := congrArg Prod.snd (congrArg (fun f => f (x, w)) he)
        change localConjugation (transition b hb e (k : A) x) w = w at h
        rwa [transition_kernel] at h
      exact ((localConjugation_eq_one_iff _).mp hc).2
    exact congrArg Subtype.val hk2
  · intro ha
    let k : Kernel (A := A) (X := X) := ⟨a, ha.1⟩
    apply Equiv.ext
    rintro ⟨x, v⟩
    change ambientAction b hb e (k : A) (x, v) = (x, v)
    rw [ambientAction_kernel_apply]
    have hc : localConjugation (fibreCoordinate b hb e x k) = 1 := by
      apply (localConjugation_eq_one_iff _).mpr
      refine ⟨hEven x k, ?_⟩
      have hk2 : k ^ 2 = 1 := Subtype.ext ha.2
      simpa only [map_pow, map_one] using congrArg (fibreCoordinate b hb e x) hk2
    rw [hc]
    rfl

/-- The actual quotient by the original binary core, with its exact
original ambient reconstruction on every quotient representative. -/
def quotientAction : A ⧸ originalCore b hb e hEven →*
    Equiv.Perm (Translations (X := X)) :=
  QuotientGroup.lift (originalCore b hb e hEven) (ambientAction b hb e)
    (ambientAction_ker b hb e hEven).symm.le

@[simp] theorem quotientAction_mk (a : A) :
    quotientAction b hb e hEven (QuotientGroup.mk' (originalCore b hb e hEven) a) =
      ambientAction b hb e a := rfl

theorem quotientAction_injective : Function.Injective (quotientAction b hb e hEven) := by
  apply (MonoidHom.ker_eq_bot_iff (quotientAction b hb e hEven)).mp
  change (QuotientGroup.lift (originalCore b hb e hEven) (ambientAction b hb e)
    (ambientAction_ker b hb e hEven).symm.le).ker = ⊥
  rw [QuotientGroup.ker_lift, ambientAction_ker b hb e hEven,
    QuotientGroup.map_mk'_self]

end Quotient

section Transitivity

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x) (hEven : AllEven b hb e)
    (hfull : ∀ x, Function.Surjective (alternatingCoordinate b hb e hEven x))

omit [FaithfulSMul A Ω] in
include hfull in
/-- Full local A4 images give transitivity on all ambient nonidentity
translations, even when the original binary core is correlated. -/
theorem ambientAction_transitive (s t : Translations (X := X)) :
    ∃ a : A, ambientAction b hb e a s = t := by
  rcases s with ⟨x, v⟩
  rcases t with ⟨y, w⟩
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A x y
  obtain ⟨g, hg⟩ := a4_transitive_local
    (localConjugation (transition b hb e a x) v) w
  obtain ⟨k, hk⟩ := hfull (a • x) g
  refine ⟨(k : A) * a, ?_⟩
  rw [map_mul]
  change ambientAction b hb e (k : A)
    (a • x, localConjugation (transition b hb e a x) v) = (a • x, w)
  rw [ambientAction_kernel_apply]
  have hc : fibreCoordinate b hb e (a • x) k = (g : Equiv.Perm (Fin 4)) :=
    congrArg Subtype.val hk
  rw [hc, hg]

include hfull in
theorem quotientAction_transitive (s t : Translations (X := X)) :
    ∃ q : A ⧸ originalCore b hb e hEven, quotientAction b hb e hEven q s = t := by
  obtain ⟨a, ha⟩ := ambientAction_transitive b hb e hEven hfull s t
  exact ⟨QuotientGroup.mk' (originalCore b hb e hEven) a, ha⟩

end Transitivity

/-- Three original blocks give nine ambient local translations. -/
theorem translations_card {X : Type} [Finite X] (hX : Nat.card X = 3) :
    Nat.card (Translations (X := X)) = 9 := by
  rw [Nat.card_prod, hX, localTranslation_card]

end DegreeTwelveNineTranslations

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The complete saturated original branch yields a faithful transitive
nine-translation action of its WHOLE ternary quotient. The quotient is not
identified with the three-point block top. No earlier-owner count is asserted. -/
theorem fourByThree_nineTranslationQuotient
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3) (hTopOrder : Nat.card D.Top = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x) :
    let hEven := D.fourByThree_allEven N c hPoints hTopOrder hWeight hTop hRank e
    let W := DegreeTwelveNineTranslations.originalCore D.map D.map_equivariant e hEven
    let act := DegreeTwelveNineTranslations.quotientAction D.map D.map_equivariant e hEven
    IsPGroup 3 (A ⧸ W) ∧
      Nat.card (DegreeTwelveNineTranslations.Translations (X := D.Points)) = 9 ∧
      Function.Injective act ∧ ∀ s t, ∃ q : A ⧸ W, act q s = t := by
  dsimp only
  refine ⟨?_, DegreeTwelveNineTranslations.translations_card hPoints,
    DegreeTwelveNineTranslations.quotientAction_injective D.map D.map_equivariant e
      (D.fourByThree_allEven N c hPoints hTopOrder hWeight hTop hRank e), ?_⟩
  · exact DegreeTwelveFourBlockCore.quotient_isPGroup D.topMap _ _ hTopOrder
  · intro s t
    apply DegreeTwelveNineTranslations.quotientAction_transitive D.map D.map_equivariant e _ ?_ s t
    have hHead := D.fourByThree_intersection_head_eq_one N c hPoints hWeight hTop hRank
    intro x
    exact DegreeTwelveFourBlockFullness.alternatingCoordinate_surjective
      D.map D.map_equivariant e (hTopOrder.trans hPoints.symm) N
        (by rw [hHead]; norm_num) _ x

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics
