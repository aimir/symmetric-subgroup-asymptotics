import SymmetricSubgroupAsymptotics.DegreeTwelveNineTranslations

/-!
# Klein-character coordinates of the degree-twelve binary core

For a nonidentity Klein translation `t`, the function on the Klein group
which vanishes exactly on `{1, t}` is a binary character.  Evaluating these
three characters on each of the three literal block coordinates of the
original binary core gives an injective additive map from the core into the
functions on the nine ambient local translations.  Conjugation by the whole
original group transports the block coordinate and the translation label by
the same local chart change, so the coordinates are compatible with the
actual nine-translation action.  Only finite four-point permutation facts
are checked by kernel computation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace DegreeTwelveNineTranslations

open DegreeTwelveFourBlockCore DegreeTwelveFourBlockFullness

/-- The binary character on four-point permutations vanishing on `{1, t}`. -/
def kleinCharPerm (t u : Equiv.Perm (Fin 4)) : ZMod 2 :=
  if u = 1 ∨ u = t then 0 else 1

private theorem kleinCoset_mul : ∀ t u w : Equiv.Perm (Fin 4),
    Equiv.Perm.sign t = 1 → t ^ 2 = 1 → t ≠ 1 →
    Equiv.Perm.sign u = 1 → u ^ 2 = 1 →
    Equiv.Perm.sign w = 1 → w ^ 2 = 1 →
    ((u * w = 1 ∨ u * w = t) ↔ ((u = 1 ∨ u = t) ↔ (w = 1 ∨ w = t))) := by
  decide +kernel

private theorem kleinCharPerm_mul (t u w : Equiv.Perm (Fin 4))
    (hts : Equiv.Perm.sign t = 1) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hus : Equiv.Perm.sign u = 1) (hu2 : u ^ 2 = 1)
    (hws : Equiv.Perm.sign w = 1) (hw2 : w ^ 2 = 1) :
    kleinCharPerm t (u * w) = kleinCharPerm t u + kleinCharPerm t w := by
  have key := kleinCoset_mul t u w hts ht2 ht1 hus hu2 hws hw2
  unfold kleinCharPerm
  by_cases hu : u = 1 ∨ u = t
  · by_cases hw : w = 1 ∨ w = t
    · rw [if_pos (key.mpr (iff_of_true hu hw)), if_pos hu, if_pos hw]
      decide
    · rw [if_neg (fun huw => hw ((key.mp huw).mp hu)), if_pos hu, if_neg hw]
      decide
  · by_cases hw : w = 1 ∨ w = t
    · rw [if_neg (fun huw => hu ((key.mp huw).mpr hw)), if_neg hu, if_pos hw]
      decide
    · rw [if_pos (key.mpr (iff_of_false hu hw)), if_neg hu, if_neg hw]
      decide

theorem kleinSquare (v : V4) : v ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one v
  rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)] at h
  exact h

theorem kleinPerm_square (v : V4) :
    ((v : A4) : Equiv.Perm (Fin 4)) ^ 2 = 1 := by
  have h := congrArg (fun z : V4 => ((z : A4) : Equiv.Perm (Fin 4))) (kleinSquare v)
  simpa using h

theorem kleinPerm_sign (v : V4) :
    Equiv.Perm.sign ((v : A4) : Equiv.Perm (Fin 4)) = 1 :=
  Equiv.Perm.mem_alternatingGroup.mp (v : A4).property

theorem kleinPerm_injective {u v : V4}
    (h : ((u : A4) : Equiv.Perm (Fin 4)) = ((v : A4) : Equiv.Perm (Fin 4))) :
    u = v :=
  Subtype.ext (Subtype.ext h)

/-- The Klein character attached to one nonidentity local translation. -/
def kleinCharacter (t : LocalTranslation) (u : V4) : ZMod 2 :=
  kleinCharPerm ((t.val : A4) : Equiv.Perm (Fin 4)) ((u : A4) : Equiv.Perm (Fin 4))

theorem kleinCharacter_one (t : LocalTranslation) : kleinCharacter t 1 = 0 := by
  simp [kleinCharacter, kleinCharPerm]

theorem kleinCharacter_mul (t : LocalTranslation) (u w : V4) :
    kleinCharacter t (u * w) = kleinCharacter t u + kleinCharacter t w := by
  have htne : ((t.val : A4) : Equiv.Perm (Fin 4)) ≠ 1 := by
    intro h
    apply t.2
    apply kleinPerm_injective
    rw [h]
    rfl
  exact kleinCharPerm_mul _ _ _ (kleinPerm_sign t.val) (kleinPerm_square t.val) htne
    (kleinPerm_sign u) (kleinPerm_square u) (kleinPerm_sign w) (kleinPerm_square w)

theorem kleinCharacter_eq_one {t : LocalTranslation} {u : V4}
    (hu : u ≠ 1) (ht : u ≠ t.val) : kleinCharacter t u = 1 := by
  unfold kleinCharacter kleinCharPerm
  rw [if_neg]
  rintro (h | h)
  · exact hu (kleinPerm_injective (h.trans rfl))
  · exact ht (kleinPerm_injective h)

/-- A nonidentity Klein element is detected by some local translation. -/
theorem exists_kleinCharacter_eq_one {u : V4} (hu : u ≠ 1) :
    ∃ t : LocalTranslation, kleinCharacter t u = 1 := by
  have hcard : 1 < Nat.card LocalTranslation := by
    rw [localTranslation_card]
    norm_num
  obtain ⟨t₁, t₂, hne⟩ := (Finite.one_lt_card_iff_nontrivial.mp hcard).exists_pair_ne
  by_cases h₁ : u = t₁.val
  · refine ⟨t₂, kleinCharacter_eq_one hu ?_⟩
    intro h₂
    exact hne (Subtype.ext (h₁.symm.trans h₂))
  · exact ⟨t₁, kleinCharacter_eq_one hu h₁⟩

/-- Simultaneous conjugation of the character label and the argument. -/
theorem kleinCharacter_conjugation (c : Equiv.Perm (Fin 4)) (t : LocalTranslation)
    (u : V4) :
    kleinCharacter (localConjugation c t) (kleinConjugation c u) =
      kleinCharacter t u := by
  unfold kleinCharacter kleinCharPerm
  change (if c * ((u : A4) : Equiv.Perm (Fin 4)) * c⁻¹ = 1 ∨
      c * ((u : A4) : Equiv.Perm (Fin 4)) * c⁻¹ =
        c * ((t.val : A4) : Equiv.Perm (Fin 4)) * c⁻¹ then (0 : ZMod 2) else 1) = _
  have h1 : c * ((u : A4) : Equiv.Perm (Fin 4)) * c⁻¹ = 1 ↔
      ((u : A4) : Equiv.Perm (Fin 4)) = 1 := by
    constructor
    · intro h
      have h' := congrArg (fun z => c⁻¹ * z * c) h
      simpa [mul_assoc] using h'
    · intro h
      rw [h, mul_one, mul_inv_cancel]
  have h2 : c * ((u : A4) : Equiv.Perm (Fin 4)) * c⁻¹ =
        c * ((t.val : A4) : Equiv.Perm (Fin 4)) * c⁻¹ ↔
      ((u : A4) : Equiv.Perm (Fin 4)) = ((t.val : A4) : Equiv.Perm (Fin 4)) := by
    constructor
    · intro h
      have h' := congrArg (fun z => c⁻¹ * z * c) h
      simpa [mul_assoc] using h'
    · intro h
      rw [h]
  simp only [h1, h2]

section Coordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x) (hEven : AllEven b hb e)

/-- The literal Klein block coordinate of a core element. -/
abbrev coreBlockCoordinate (k : originalCore b hb e hEven) (x : X) : V4 :=
  coreCoordinates (MulAction.toPermHom A X) (alternatingCoordinates b hb e hEven)
    (alternatingCoordinates_injective b hb e hEven) k x

/-- Klein-character coordinates on the nine ambient local translations. -/
def kleinCoordinates :
    Additive (originalCore b hb e hEven) →+ (Translations (X := X) → ZMod 2) where
  toFun v s := kleinCharacter s.2 (coreBlockCoordinate b hb e hEven v.toMul s.1)
  map_zero' := by
    funext s
    change kleinCharacter s.2 (coreBlockCoordinate b hb e hEven 1 s.1) = 0
    rw [coreBlockCoordinate, map_one]
    exact kleinCharacter_one s.2
  map_add' v w := by
    funext s
    change kleinCharacter s.2
        (coreBlockCoordinate b hb e hEven (v.toMul * w.toMul) s.1) =
      kleinCharacter s.2 (coreBlockCoordinate b hb e hEven v.toMul s.1) +
        kleinCharacter s.2 (coreBlockCoordinate b hb e hEven w.toMul s.1)
    rw [coreBlockCoordinate, map_mul, Pi.mul_apply]
    exact kleinCharacter_mul s.2 _ _

theorem kleinCoordinates_apply (v : Additive (originalCore b hb e hEven))
    (s : Translations (X := X)) :
    kleinCoordinates b hb e hEven v s =
      kleinCharacter s.2 (coreBlockCoordinate b hb e hEven v.toMul s.1) := rfl

theorem kleinCoordinates_injective :
    Function.Injective (kleinCoordinates b hb e hEven) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hcoord : coreCoordinates (MulAction.toPermHom A X)
      (alternatingCoordinates b hb e hEven)
      (alternatingCoordinates_injective b hb e hEven) v.toMul = 1 := by
    funext x
    by_contra hx
    obtain ⟨t, ht⟩ := exists_kleinCharacter_eq_one hx
    have h := congrFun hv (x, t)
    rw [kleinCoordinates_apply] at h
    change kleinCharacter t (coreBlockCoordinate b hb e hEven v.toMul x) = 0 at h
    rw [ht] at h
    exact one_ne_zero h
  have hk : v.toMul = 1 := by
    apply coreCoordinates_injective (MulAction.toPermHom A X)
      (alternatingCoordinates b hb e hEven)
      (alternatingCoordinates_injective b hb e hEven)
    rw [hcoord, map_one]
  exact Additive.toMul.injective (hk.trans rfl)

/-- Whole-group conjugation moves the block coordinate by the actual local
chart transition. -/
theorem coreBlockCoordinate_conjugation [Finite Ω] (a : A)
    (k : originalCore b hb e hEven) (x : X) :
    coreBlockCoordinate b hb e hEven (MulAut.conjNormal a k) (a • x) =
      kleinConjugation (transition b hb e a x) (coreBlockCoordinate b hb e hEven k x) := by
  apply Subtype.ext
  apply Subtype.ext
  let kk : Kernel (A := A) (X := X) := ⟨(k : A), k.property.1⟩
  have hconj : (⟨((MulAut.conjNormal a k : originalCore b hb e hEven) : A),
      (MulAut.conjNormal a k).property.1⟩ : Kernel (A := A) (X := X)) =
        MulAut.conjNormal a kk := Subtype.ext rfl
  change fibreCoordinate b hb e (a • x)
      ⟨((MulAut.conjNormal a k : originalCore b hb e hEven) : A),
        (MulAut.conjNormal a k).property.1⟩ =
    transition b hb e a x * fibreCoordinate b hb e x kk * (transition b hb e a x)⁻¹
  rw [hconj]
  exact fibreCoordinate_conjugation b hb e a x kk

/-- The Klein coordinates are compatible with the actual ambient action on
the nine local translations. -/
theorem kleinCoordinates_conjugation [Finite Ω] (a : A)
    (k : originalCore b hb e hEven) (s : Translations (X := X)) :
    kleinCoordinates b hb e hEven (Additive.ofMul (MulAut.conjNormal a k))
        (ambientAction b hb e a s) =
      kleinCoordinates b hb e hEven (Additive.ofMul k) s := by
  rcases s with ⟨x, t⟩
  rw [kleinCoordinates_apply, kleinCoordinates_apply, ambientAction_apply]
  change kleinCharacter (localConjugation (transition b hb e a x) t)
      (coreBlockCoordinate b hb e hEven (MulAut.conjNormal a k) (a • x)) =
    kleinCharacter t (coreBlockCoordinate b hb e hEven k x)
  rw [coreBlockCoordinate_conjugation, kleinCharacter_conjugation]

end Coordinates

end DegreeTwelveNineTranslations
end SymmetricSubgroupAsymptotics

end
