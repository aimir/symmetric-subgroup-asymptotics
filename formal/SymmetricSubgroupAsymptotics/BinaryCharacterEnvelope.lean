import SymmetricSubgroupAsymptotics.BinaryIrreducibleTuple
import SymmetricSubgroupAsymptotics.CharacterEpimorphismBound
import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Nilpotent

/-! Original-source character envelopes for every finite binary target.
The faithful irreducible tuple and restriction to an original Sylow are
proved. The only external input is Maróti's published class-count bound
for an actual nilpotent permutation group of its actual degree.
The finite integer criterion then gives the strict even-width gap. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binary_groupEpimorphism_card_le_characters
    {J Q : Type} [Group J] [Group Q] [Finite J] [Finite Q]
    (hQ : IsPGroup 2 Q) :
    Nat.card (GroupEpimorphism J Q)≤Nat.card (Q≃*Q)*
      Nat.card (ConjClasses J)^Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) := by
  letI : Invertible (Nat.card J:ℂ) := invertibleOfNonzero
    (by exact_mod_cast (Nat.card_pos (α := J)).ne')
  obtain ⟨ρ,hρ⟩ := exists_binary_faithful_irreducible_tuple (k := ℂ) hQ
  simpa only [Fintype.card_fin] using
    groupEpimorphism_card_le_faithful_characters (k := ℂ) (J := J)
      (fun i=>(ρ i).Space) (fun i=>(ρ i).action) hρ

/-- Maróti, *Bounding the number of conjugacy classes of a permutation
group*, Theorem1.5 (author PDF p.2). This is a named literature hypothesis,
not a project capacity conclusion and not an axiom. -/
def NilpotentConjugacyClassInput : Prop :=
  ∀ (b : ℕ) (P : Subgroup (Equiv.Perm (Fin b))),Group.IsNilpotent P →
    (Nat.card (ConjClasses P):ℝ)≤(38/25:ℝ)^b

def binaryCharacterSlope (z : ℕ) : ℝ := (z:ℝ)*Real.logb 2 (38/25)

theorem binaryCharacterSlope_power (b z : ℕ) :
    (2:ℝ)^(binaryCharacterSlope z*(b:ℝ))=(38/25:ℝ)^(b*z) := by
  calc
    _=(2:ℝ)^(Real.logb 2 (38/25)*((b*z:ℕ):ℝ)) := by
      unfold binaryCharacterSlope
      congr 1
      push_cast
      ring
    _=_ := by
      rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2),
        Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) (by norm_num),
        Real.rpow_natCast]

theorem originalSylow_conjugacyClass_bound (hMaroti : NilpotentConjugacyClassInput)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) (P : Sylow 2 J) :
    (Nat.card (ConjClasses (P:Subgroup J)):ℝ)≤(38/25:ℝ)^b := by
  let T := (P:Subgroup J).map J.subtype
  let e : (P:Subgroup J)≃*T :=
    Subgroup.equivMapOfInjective (P:Subgroup J) J.subtype Subtype.val_injective
  have hT : IsPGroup 2 T := P.isPGroup'.of_equiv e
  have hn : Group.IsNilpotent T := hT.isNilpotent
  have hc : Nat.card (ConjClasses (P:Subgroup J))≤Nat.card (ConjClasses T) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (by exact_mod_cast hc : (Nat.card (ConjClasses (P:Subgroup J)):ℝ)≤
    (Nat.card (ConjClasses T):ℝ)).trans (hMaroti b T hn)

/-- The complement J is arbitrary. Restriction is to its actual Sylow
inside the same S_b, and the original target automorphism factor survives. -/
theorem binary_groupEpimorphism_original_envelope
    (hMaroti : NilpotentConjugacyClassInput)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q):ℝ)≤(Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binaryCharacterSlope
        (Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)))*(b:ℝ)) := by
  classical
  let P : Sylow 2 J := Classical.choice inferInstance
  let z := Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q))
  have hnat := (groupEpimorphism_card_le_sylow P hQ).trans
    (binary_groupEpimorphism_card_le_characters (J := (P:Subgroup J)) hQ)
  have hp := pow_le_pow_left₀ (show (0:ℝ)≤Nat.card (ConjClasses (P:Subgroup J)) by positivity)
    (originalSylow_conjugacyClass_bound hMaroti b J P) z
  rw [binaryCharacterSlope_power]
  calc
    _≤(Nat.card (Q≃*Q):ℝ)*(Nat.card (ConjClasses (P:Subgroup J)):ℝ)^z := by
      exact_mod_cast hnat
    _≤(Nat.card (Q≃*Q):ℝ)*((38/25:ℝ)^b)^z :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _=_ := by rw [←pow_mul]

theorem BinaryNormalCharacterCriterion.slope_gap
    {Q : Type} [Group Q] {w : ℕ} (C : BinaryNormalCharacterCriterion Q w) :
    binaryCharacterSlope C.dimension<(w:ℝ)/8 := by
  have hg : (38:ℝ)^(8*C.dimension)<(2:ℝ)^w*(25:ℝ)^(8*C.dimension) := by
    exact_mod_cast C.gap
  have hdiv : (38/25:ℝ)^(8*C.dimension)<(2:ℝ)^w := by
    rw [div_pow]
    exact (div_lt_iff₀ (by positivity)).mpr hg
  have hl := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hdiv
  simp only [Real.logb_pow,Nat.cast_mul,Nat.cast_ofNat] at hl
  rw [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hl
  unfold binaryCharacterSlope
  nlinarith

theorem BinaryNormalCharacterCriterion.original_envelope
    (hMaroti : NilpotentConjugacyClassInput)
    {Q : Type} [Group Q] [Finite Q] {w : ℕ} (C : BinaryNormalCharacterCriterion Q w)
    (hQ : IsPGroup 2 Q) (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q):ℝ)≤(Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binaryCharacterSlope C.dimension*(b:ℝ)) := by
  simpa only [C.exact_dimension] using
    binary_groupEpimorphism_original_envelope hMaroti hQ b J

end SymmetricSubgroupAsymptotics
