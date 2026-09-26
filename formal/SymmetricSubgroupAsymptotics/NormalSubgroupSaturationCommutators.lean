import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCertificate
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! Nonempty original commutator paths strengthen finite saturation from
R≤B to R≤[B,G]. In the actual relative-radical case this identifies both
[B,G] and the whole-G relative radical of B with the same R_D whenever
B≤D is not contained in R_D. The previously checked base certificate is
unchanged; path nonemptiness is an additional finite proof obligation. -/
set_option autoImplicit false
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G]

/-- The first original commutator puts a nonempty path in [B,G]; all
later steps remain there by its whole-ambient normality. -/
theorem iteratedOriginalCommutator_mem_mixed
    (g : ι → G) (B : Subgroup G) [B.Normal]
    (x : G) (hx : x ∈ B) (w : List ι) (hw : w ≠ []) :
    iteratedOriginalCommutator g x w ∈ ⁅B, (⊤ : Subgroup G)⁆ := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons i w =>
    exact iteratedOriginalCommutator_mem g ⁅B, (⊤ : Subgroup G)⁆
      ⁅x, g i⁆ (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top (g i))) w

theorem originalCommutatorProduct_mem_mixed
    (g : ι → G) (B : Subgroup G) [B.Normal]
    (x : G) (hx : x ∈ B) (words : List (List ι))
    (hne : ∀ w ∈ words, w ≠ []) :
    originalCommutatorProduct g x words ∈ ⁅B, (⊤ : Subgroup G)⁆ := by
  apply (⁅B, (⊤ : Subgroup G)⁆).list_prod_mem
  intro y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
  exact iteratedOriginalCommutator_mem_mixed g B x hx w (hne w hw)

namespace NormalSubgroupSaturationCertificate

variable {D R : Subgroup G} {ambient : ι → G} {radicalGenerators : κ → G} {n : ℕ}

/-- Every path actually used to recover an R-generator starts with a
commutator. The empty outer product is permitted, but an empty inner path
would merely return the original element and is expressly excluded. -/
def NonemptyWords
    (C : NormalSubgroupSaturationCertificate D R ambient radicalGenerators n) : Prop :=
  ∀ i, C.inside i = false → ∀ j, ∀ w ∈ C.words i j, w ≠ []

variable (C : NormalSubgroupSaturationCertificate D R ambient radicalGenerators n)
include C

/-- Concrete nonempty word recovery forces every R-generator into the
actual original mixed commutator, not merely into the normal subgroup. -/
theorem radical_le_commutator (hne : C.NonemptyWords)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D) (hnot : ¬B ≤ R) :
    R ≤ ⁅B, (⊤ : Subgroup G)⁆ := by
  obtain ⟨b, hb, hbR⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨i, hi⟩ := C.rows_cover b (hBD hb)
  have hiB : C.rows i ∈ B := by rw [hi]; exact hb
  have hiR : C.rows i ∉ R := by rw [hi]; exact hbR
  have hout : C.inside i = false := by
    cases h : C.inside i with
    | false => rfl
    | true => exact False.elim (hiR (C.inside_mem i h))
  rw [← C.radical_full]
  apply (Subgroup.closure_le ⁅B, (⊤ : Subgroup G)⁆).mpr
  rintro _ ⟨j, rfl⟩
  rw [← C.words_eq i hout j]
  exact originalCommutatorProduct_mem_mixed ambient B (C.rows i) hiB
    (C.words i j) (hne i hout j)

end NormalSubgroupSaturationCertificate

variable (p : ℕ) [Fact p.Prime]

/-- Relative radicals are monotone for inclusions of original normal
subgroups with the SAME whole-ambient conjugation action. -/
theorem primeRelativeRadical_mono (B D : Subgroup G) [B.Normal] [D.Normal]
    (hBD : B ≤ D) : primeRelativeRadical p B ≤ primeRelativeRadical p D := by
  rw [primeRelativeRadical_eq_powerCommutator p B]
  apply sup_le
  · apply (Subgroup.closure_le (primeRelativeRadical p D)).mpr
    rintro _ ⟨b, rfl⟩
    exact pow_mem_primeRelativeRadical p D ⟨(b : G), hBD b.2⟩
  · exact (Subgroup.commutator_mono hBD le_rfl).trans
      ((primeRelativePowerCommutator_commutator_le p D).trans
        (primeRelativePowerCommutator_le_radical p D))

namespace NormalSubgroupSaturationCertificate

variable {D : Subgroup G} [D.Normal]
    {ambient : ι → G} {radicalGenerators : κ → G} {n : ℕ}
variable (C : NormalSubgroupSaturationCertificate D
  (primeRelativeRadical p D) ambient radicalGenerators n)
include C

/-- The lower bound from actual nonempty words and the automatic upper
bound [B,G]≤[D,G]≤R_D identify the same original mixed commutator exactly. -/
theorem commutator_eq_relativeRadical (hne : C.NonemptyWords)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hnot : ¬B ≤ primeRelativeRadical p D) :
    ⁅B, (⊤ : Subgroup G)⁆ = primeRelativeRadical p D := by
  apply le_antisymm
  · exact (Subgroup.commutator_mono hBD le_rfl).trans
      ((primeRelativePowerCommutator_commutator_le p D).trans
        (primeRelativePowerCommutator_le_radical p D))
  · exact C.radical_le_commutator hne B hBD hnot

/-- The full relative radical of B equals R_D; original B-powers are
retained in the upper bound and are not asserted to vanish separately. -/
theorem relativeRadical_eq (hne : C.NonemptyWords)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hnot : ¬B ≤ primeRelativeRadical p D) :
    primeRelativeRadical p B = primeRelativeRadical p D := by
  apply le_antisymm (primeRelativeRadical_mono p B D hBD)
  exact (C.radical_le_commutator hne B hBD hnot).trans
    ((primeRelativePowerCommutator_commutator_le p B).trans
      (primeRelativePowerCommutator_le_radical p B))

/-- Exact head cardinal factorization for every such original B follows
from its actual relative radical, without supplying a numerical head. -/
theorem card_eq_pow_head_mul_relativeRadical [Finite G] (hne : C.NonemptyWords)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hnot : ¬B ≤ primeRelativeRadical p D) :
    Nat.card B = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) *
      Nat.card (primeRelativeRadical p D) := by
  have h := primeRelativeRadical_card_factorization p B
  rwa [relativeRadical_eq p C hne B hBD hnot] at h

end NormalSubgroupSaturationCertificate
end SymmetricSubgroupAsymptotics
