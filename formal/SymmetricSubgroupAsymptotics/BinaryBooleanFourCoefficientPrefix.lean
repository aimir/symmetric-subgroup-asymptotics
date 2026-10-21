import SymmetricSubgroupAsymptotics.BinaryBooleanFourDifferenceOperators
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.PermutationCentralizerPointWords

/-! One thirteen-dimensional coefficient prefix is preserved by every
permutation commuting with the four actual Boolean translations. Only
sixteen point words and their action on thirteen basis vectors are checked.
No subgroup, normal, or extension census is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

def prefixChart : BinaryCoordinateSpace 16 13 where
  inclusion := {
    toFun v j := if h : j.val<13 then v ⟨j.val,h⟩ else 0
    map_add' v w := by
      funext j
      by_cases h : j.val < 13 <;> simp [h,Pi.add_apply]
    map_smul' c v := by
      funext j
      by_cases h : j.val < 13 <;> simp [h,Pi.smul_apply] }
  coordinates := {
    toFun v j := v ⟨j.val,lt_trans j.isLt (by decide : 13<16)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  left_inverse v := by
    funext j
    change (if h : j.val<13 then v ⟨j.val,h⟩ else 0)=v j
    simp only [dif_pos j.isLt]

theorem mem_prefixChart (v : V) : v∈prefixChart.space ↔ ∀ j : Fin 16,13≤j.val → v j=0 := by
  rw [prefixChart.mem_iff]
  constructor
  · intro h j hj
    have he := congrFun h j
    change (if h : j.val<13 then v ⟨j.val,by omega⟩ else 0)=v j at he
    simpa only [dif_neg (by omega : ¬j.val<13)] using he.symm
  · intro h
    funext j
    change (if h : j.val<13 then v ⟨j.val,by omega⟩ else 0)=v j
    split
    · rfl
    · exact (h j (by omega)).symm

def booleanPointWords (x : Fin 16) : List (Fin 4) :=
  (List.finRange 4).filter (fun i => x.val.testBit i.val)

def booleanPointCandidate (y : Fin 16) : Equiv.Perm (Fin 16) :=
  pointWordPermutation pointTranslation (booleanPointWords y)

private theorem point_words : ∀ x : Fin 16,
    pointWordPermutation pointTranslation (booleanPointWords x) 0=x := by decide +kernel

private theorem point_words_symmetric : ∀ x y : Fin 16,
    pointWordPermutation pointTranslation (booleanPointWords x) y=
      pointWordPermutation pointTranslation (booleanPointWords y) x := by decide +kernel

theorem centralizing_boolean_translations_is_candidate
    (p : Equiv.Perm (Fin 16)) (hp : ∀ i : Fin 4,Commute p (pointTranslation i)) :
    p=booleanPointCandidate (p 0) := by
  apply Equiv.ext
  intro x
  exact (centralizer_eq_pointWord_candidate pointTranslation 0 booleanPointWords
    point_words p hp x).trans (point_words_symmetric x (p 0))

def candidateCoefficientAction (y : Fin 16) : V →ₗ[ZMod 2] V :=
  evaluate.comp ((binaryPermutationRepresentation 16 (booleanPointCandidate y)⁻¹).comp evaluate)

private theorem candidate_prefix_basis : ∀ (y : Fin 16) (j : Fin 13),
    candidateCoefficientAction y (prefixChart.inclusion (Pi.single j 1)) ∈ prefixChart.space := by
  decide +kernel

private theorem coordinate_image_mem_of_basis {w d : ℕ}
    (K : BinaryCoordinateSpace w d)
    (L : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))
    (R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hb : ∀ j,L (K.inclusion (Pi.single j 1))∈R)
    (v : Fin w → ZMod 2) (hv : v∈K.space) : L v∈R := by
  exact K.le_of_basis_mem (R.comap L) hb hv

theorem candidate_preserves_prefix (y : Fin 16) (v : V) (hv : v∈prefixChart.space) :
    candidateCoefficientAction y v∈prefixChart.space := by
  exact coordinate_image_mem_of_basis prefixChart (candidateCoefficientAction y)
    prefixChart.space (candidate_prefix_basis y) v hv

theorem centralizing_permutation_preserves_prefix
    (p : Equiv.Perm (Fin 16)) (hp : ∀ i : Fin 4,Commute p (pointTranslation i))
    (v : V) (hv : v∈prefixChart.space) :
    evaluate (fun x => evaluate v (p x))∈prefixChart.space := by
  rw [centralizing_boolean_translations_is_candidate p hp]
  exact candidate_preserves_prefix (p 0) v hv

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
