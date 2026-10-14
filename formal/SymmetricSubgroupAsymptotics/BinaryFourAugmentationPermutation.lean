import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions

/-! The common augmentation model acts on the original sixteen points.
The construction uses the displayed block generators and conjugation
identities, without enumerating either permutation group. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourBlockAugmentation

open SemidirectProduct

def kleinPermutation : Klein →* Equiv.Perm (Fin 16) where
  toFun p := uPerm ^ (p.toAdd 0).val * vPerm ^ (p.toAdd 1).val
  map_one' := by simp
  map_mul' p q := by
    apply Equiv.ext
    intro i
    revert p q i
    decide +kernel

theorem cPerm_cube : cPerm ^ 3 = 1 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

def ternaryPermutation : Ternary →* Equiv.Perm (Fin 16) :=
  powersHom 3 cPerm cPerm_cube

theorem permutationCompatibility (z : Ternary) :
    kleinPermutation.comp (kleinCyclicAction z).toMonoidHom =
      (MulAut.conj (ternaryPermutation z)).toMonoidHom.comp kleinPermutation := by
  apply MonoidHom.ext
  intro p
  apply Equiv.ext
  intro i
  revert z p i
  decide +kernel

def complementPermutation : Complement →* Equiv.Perm (Fin 16) :=
  SemidirectProduct.lift kleinPermutation ternaryPermutation permutationCompatibility

theorem conjugate_translation_power (P : Equiv.Perm (Fin 16))
    (L : Coordinates ≃ₗ[Scalar] Coordinates)
    (h : ∀ x, P * translations (Multiplicative.ofAdd x) * P⁻¹ =
      translations (Multiplicative.ofAdd (L x))) (n : ℕ) (x : Coordinates) :
    P ^ n * translations (Multiplicative.ofAdd x) * (P ^ n)⁻¹ =
      translations (Multiplicative.ofAdd ((L ^ n) x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ']
      calc
        (P * P ^ n) * translations (Multiplicative.ofAdd x) * (P * P ^ n)⁻¹ =
          P * (P ^ n * translations (Multiplicative.ofAdd x) * (P ^ n)⁻¹) * P⁻¹ := by
            group
        _ = P * translations (Multiplicative.ofAdd ((L ^ n) x)) * P⁻¹ := by rw [ih]
        _ = _ := h _

theorem kleinLinear_formula (p : Klein) (x : Coordinates) :
    (u ^ (p.toAdd 0).val) ((v ^ (p.toAdd 1).val) x) = kleinLinear p x := by
  revert p x
  decide +kernel

theorem kleinPermutation_conjugate (p : Klein) (x : Coordinates) :
    kleinPermutation p * translations (Multiplicative.ofAdd x) * (kleinPermutation p)⁻¹ =
      translations (Multiplicative.ofAdd (kleinLinear p x)) := by
  change (uPerm ^ (p.toAdd 0).val * vPerm ^ (p.toAdd 1).val) *
      translations (Multiplicative.ofAdd x) *
      (uPerm ^ (p.toAdd 0).val * vPerm ^ (p.toAdd 1).val)⁻¹ = _
  calc
    _ = uPerm ^ (p.toAdd 0).val *
      (vPerm ^ (p.toAdd 1).val * translations (Multiplicative.ofAdd x) *
        (vPerm ^ (p.toAdd 1).val)⁻¹) * (uPerm ^ (p.toAdd 0).val)⁻¹ := by group
    _ = translations (Multiplicative.ofAdd
        ((u ^ (p.toAdd 0).val) ((v ^ (p.toAdd 1).val) x))) := by
      rw [conjugate_translation_power vPerm v conjugate_v,
        conjugate_translation_power uPerm u conjugate_u]
    _ = _ := by rw [kleinLinear_formula]

theorem complementPermutation_conjugate (r : Complement) (x : Coordinates) :
    complementPermutation r * translations (Multiplicative.ofAdd x) *
        (complementPermutation r)⁻¹ =
      translations (Multiplicative.ofAdd (complementLinear r x)) := by
  change (kleinPermutation r.left * cPerm ^ r.right.toAdd.val) *
      translations (Multiplicative.ofAdd x) *
      (kleinPermutation r.left * cPerm ^ r.right.toAdd.val)⁻¹ = _
  calc
    _ = kleinPermutation r.left *
      (cPerm ^ r.right.toAdd.val * translations (Multiplicative.ofAdd x) *
        (cPerm ^ r.right.toAdd.val)⁻¹) * (kleinPermutation r.left)⁻¹ := by group
    _ = translations (Multiplicative.ofAdd
        (kleinLinear r.left ((c ^ r.right.toAdd.val) x))) := by
      rw [conjugate_translation_power cPerm c conjugate_c, kleinPermutation_conjugate]
    _ = _ := rfl

def spaceInclusion (full : Bool) : Multiplicative (space full) →* Multiplicative Coordinates where
  toFun x := Multiplicative.ofAdd (x.toAdd : Coordinates)
  map_one' := rfl
  map_mul' _ _ := rfl

def modelPermutation (full : Bool) : Model full →* Equiv.Perm (Fin 16) :=
  SemidirectProduct.lift (translations.comp (spaceInclusion full)) complementPermutation (by
    intro r
    apply MonoidHom.ext
    intro x
    exact (complementPermutation_conjugate r (x.toAdd : Coordinates)).symm)

theorem modelPermutation_inl (full : Bool) (x : Multiplicative (space full)) :
    modelPermutation full (inl x) = translations (spaceInclusion full x) := by
  exact SemidirectProduct.lift_inl _ _ _ x

theorem modelPermutation_u (full : Bool) :
    modelPermutation full (inr uElement) = uPerm := by
  rw [modelPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem modelPermutation_v (full : Bool) :
    modelPermutation full (inr vElement) = vPerm := by
  rw [modelPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem modelPermutation_c (full : Bool) :
    modelPermutation full (inr cElement) = cPerm := by
  rw [modelPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem modelTranslation_mem_range (full : Bool) (x : Coordinates)
    (hx : x ∈ space full) : translations (Multiplicative.ofAdd x) ∈
      (modelPermutation full).range :=
  ⟨inl (Multiplicative.ofAdd ⟨x, hx⟩), modelPermutation_inl full _⟩

theorem translation_basis_word (x : Coordinates) :
    translations (Multiplicative.ofAdd x) =
      translations (Multiplicative.ofAdd (basisVector 0)) ^ (x 0).val *
      translations (Multiplicative.ofAdd (basisVector 1)) ^ (x 1).val *
      translations (Multiplicative.ofAdd (basisVector 2)) ^ (x 2).val *
      translations (Multiplicative.ofAdd (basisVector 3)) ^ (x 3).val *
      translations (Multiplicative.ofAdd (basisVector 4)) ^ (x 4).val *
      translations (Multiplicative.ofAdd (basisVector 5)) ^ (x 5).val := by
  have h : Multiplicative.ofAdd x =
      Multiplicative.ofAdd (basisVector 0) ^ (x 0).val *
      Multiplicative.ofAdd (basisVector 1) ^ (x 1).val *
      Multiplicative.ofAdd (basisVector 2) ^ (x 2).val *
      Multiplicative.ofAdd (basisVector 3) ^ (x 3).val *
      Multiplicative.ofAdd (basisVector 4) ^ (x 4).val *
      Multiplicative.ofAdd (basisVector 5) ^ (x 5).val := by
    apply Multiplicative.toAdd.injective
    revert x
    decide +kernel
  rw [h]
  simp only [map_mul, map_pow]

theorem modelPermutation_range_le (full : Bool) (H : Subgroup (Equiv.Perm (Fin 16)))
    (hB : ∀ i : Fin 5, translations (Multiplicative.ofAdd (basisVector i.castSucc)) ∈ H)
    (hF : full = true → translations (Multiplicative.ofAdd (basisVector 5)) ∈ H)
    (hu : uPerm ∈ H) (hv : vPerm ∈ H) (hc : cPerm ∈ H) :
    (modelPermutation full).range ≤ H := by
  have hT (x : space full) : translations (Multiplicative.ofAdd (x : Coordinates)) ∈ H := by
    rw [translation_basis_word]
    have hlast : translations (Multiplicative.ofAdd (basisVector 5)) ^
        ((x : Coordinates) 5).val ∈ H := by
      cases full
      · have hx : (x : Coordinates) 5 = 0 := x.property rfl
        simpa only [hx, ZMod.val_zero, pow_zero] using H.one_mem
      · exact H.pow_mem (hF rfl) _
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.pow_mem (hB 0) _) (H.pow_mem (hB 1) _)) (H.pow_mem (hB 2) _))
      (H.pow_mem (hB 3) _)) (H.pow_mem (hB 4) _)) hlast
  rintro _ ⟨g, rfl⟩
  change translations (Multiplicative.ofAdd (g.left.toAdd : Coordinates)) *
    ((uPerm ^ (g.right.left.toAdd 0).val * vPerm ^ (g.right.left.toAdd 1).val) *
      cPerm ^ g.right.right.toAdd.val) ∈ H
  exact H.mul_mem (hT g.left.toAdd)
    (H.mul_mem (H.mul_mem (H.pow_mem hu _) (H.pow_mem hv _)) (H.pow_mem hc _))

end BinaryFourBlockAugmentation
end SymmetricSubgroupAsymptotics

end
