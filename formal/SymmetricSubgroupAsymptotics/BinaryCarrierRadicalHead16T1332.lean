import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationHead
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1332
import Mathlib.Tactic.FinCases

/-! The four actual relative-radical rows of the original 16T1332 group
have a two-row subgroup reached by one original commutator from every
other row. This finite certificate bounds the relative binary head of
EVERY whole-original-group normal subgroup inside that radical. The
ambient group and its conjugation action are never replaced by R itself. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalHead16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
private abbrev g := BinaryActionData16.node1332Generators
private abbrev ambient := closureGenerators g
private abbrev radicalCertificate := BinaryCarrierDerivedRadical16T1332.certificate
private abbrev rows := BinaryCarrierDerivedRadical16T1332.elements
private abbrev ambientRows := BinaryCarrierDerivedRadical16T1332.ambientRows

/-- The original radical row1 is the square of the fifth original
derived generator. Its literal cyclic subgroup, rather than a model C2. -/
def centralGenerator (_ : Fin 1) : Original := rows 1

def Z : Subgroup Original := Subgroup.closure (Set.range centralGenerator)

private theorem rows_coe (i : Fin 4) :
    (rows i : Equiv.Perm (Fin 16)) = ambientRows i :=
  BinaryCarrierDerivedRadical16T1332.elements_coe i

private theorem generator_square_pointwise : ∀ x : Fin 16,
    (ambientRows 1 * ambientRows 1) x = x := by
  decide +kernel

private theorem generator_square : rows 1 * rows 1 = 1 := by
  apply Subtype.ext
  change (rows 1 : Equiv.Perm (Fin 16)) * (rows 1 : Equiv.Perm (Fin 16)) = 1
  rw [rows_coe]
  exact Equiv.ext generator_square_pointwise

private def smallRows (i : Fin 2) : Original := ![1, rows 1] i
private def smallWords (i : Fin 2) : List (Fin 1) := ![[], [0]] i
private def smallIndex (i : Fin 2) : Fin 4 := ![0, 1] i

private theorem smallRows_eq (i : Fin 2) : smallRows i = rows (smallIndex i) := by
  fin_cases i <;> rfl

private def smallCayley : FiniteCayleyCertificate centralGenerator 2 where
  elements := smallRows
  identity := 0
  identity_eq := rfl
  next i _ := ![1, 0] i
  next_eq := by
    intro i j
    fin_cases i
    · change rows 1 = 1 * rows 1
      exact (one_mul _).symm
    · change 1 = rows 1 * rows 1
      exact generator_square.symm
  words := smallWords
  words_eq := by
    intro i
    fin_cases i
    · change (1 : Original) = 1
      rfl
    · change rows 1 = rows 1 * 1
      exact (mul_one _).symm

private theorem smallRows_injective : Function.Injective smallRows := by
  have hindex : Function.Injective smallIndex := by decide +kernel
  intro i j h
  apply hindex
  apply radicalCertificate.rows_injective
  change rows (smallIndex i) = rows (smallIndex j)
  rw [← smallRows_eq i, ← smallRows_eq j]
  exact h

theorem card_Z : Nat.card Z = 2 := smallCayley.card_closure smallRows_injective

theorem Z_le_radical : Z ≤ R := by
  apply (Subgroup.closure_le R).mpr
  rintro _ ⟨j, rfl⟩
  exact BinaryCarrierDerivedRadical16T1332.elements_mem_radical 1

private def inside : Fin 4 → Bool := ![true, true, false, false]

private def saturationWords (i : Fin 4) (_ : Fin 1) : List (List (Fin 5)) :=
  ![[], [], [[4]], [[4]]] i

private theorem inside_cases : ∀ i : Fin 4, inside i = true → i = 0 ∨ i = 1 := by
  decide +kernel

private theorem words_pointwise : ∀ (i : Fin 4), inside i = false →
    ∀ (j : Fin 1) (x : Fin 16),
      originalCommutatorProduct g (ambientRows i) (saturationWords i j) x =
        ambientRows 1 x := by
  decide +kernel

/-- Every original radical element is covered by the already checked
four-row radical certificate. No subgroup of R is enumerated. -/
private theorem rows_cover (x : Original) (hx : x ∈ R) : ∃ i, rows i = x := by
  have hd : _ = R := radicalCertificate.closure_eq_radical (closureGenerators_full g)
    BinaryCarrierDerivedOrder16T1332.certificate.subgroup_eq_commutator
  rw [← hd] at hx
  exact (radicalCertificate.cayley.mem_closure_iff x).mp hx

def certificate : NormalSubgroupSaturationCertificate R Z ambient centralGenerator 4 where
  radical_le := Z_le_radical
  radical_full := rfl
  rows := rows
  rows_mem := BinaryCarrierDerivedRadical16T1332.elements_mem_radical
  rows_cover := rows_cover
  inside := inside
  inside_mem := by
    intro i hi
    rcases inside_cases i hi with rfl | rfl
    · exact Z.one_mem
    · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 1))
  words := saturationWords
  words_eq := by
    intro i hi j
    apply Subtype.ext
    change Original.subtype
      (originalCommutatorProduct ambient (rows i) (saturationWords i j)) =
        (rows 1 : Equiv.Perm (Fin 16))
    rw [map_originalCommutatorProduct]
    change originalCommutatorProduct g (rows i : Equiv.Perm (Fin 16))
      (saturationWords i j) = (rows 1 : Equiv.Perm (Fin 16))
    rw [rows_coe, rows_coe]
    exact Equiv.ext (words_pointwise i hi j)

theorem nonempty_words : certificate.NonemptyWords := by
  change ∀ i : Fin 4, inside i = false → ∀ j : Fin 1,
    ∀ w ∈ saturationWords i j, w ≠ []
  decide +kernel

/-- This maximum quantifies over all normals in the whole original
group contained in R, not over an intrinsic normal menu of R. -/
theorem normalHeadMax_le_one : primeNormalHeadMax 2 R ≤ 1 :=
  NormalSubgroupSaturationCertificate.primeNormalHeadMax_le 2 certificate nonempty_words 1
    (by rw [card_Z]; decide)
    (by rw [BinaryCarrierDerivedRadical16T1332.card_relative_radical, card_Z]; decide)

theorem relativeHead_le_one (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 1 :=
  (primeRelativeHead_le_normalHeadMax 2 R M hM).trans normalHeadMax_le_one

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalHead16T1332
