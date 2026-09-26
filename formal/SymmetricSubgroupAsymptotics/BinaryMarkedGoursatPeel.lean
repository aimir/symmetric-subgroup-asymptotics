import SymmetricSubgroupAsymptotics.FullSubdirectGoursat
import SymmetricSubgroupAsymptotics.BinaryMarkedSubdirect
import SymmetricSubgroupAsymptotics.BinaryStructuredEpiPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! One genuine weighted carrier peel over a fixed complete tail. Each
literal normal axis has its actual character/radical row and actual target
quotient. The structured epi count shifts the SAME tail mark. Arbitrary
nonnegative original weights remain attached to their literal axes.
No finite row values, domination matrix, or carrier coverage is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryMarkedGoursatPeel

open FullSubdirectGoursat

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

local instance homFinite {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) := Finite.of_injective
      (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

attribute [local instance] Fintype.ofFinite

def exponent (G : Type) [Group G] [Finite G] (x y z : ℝ) : ℝ :=
  x*(binaryCharacterRank G : ℝ) + y*(primeDerivedNormalRank 2 G : ℝ) +
    z*(Module.finrank (ZMod 2) (terminalRestrictedInflationKernel G) : ℝ)

def mark (G : Type) [Group G] [Finite G] (x y z : ℝ) : ℝ :=
  (2 : ℝ)^(exponent G x y z)

theorem mark_nonneg (G : Type) [Group G] [Finite G] (x y z : ℝ) :
    0 ≤ mark G x y z := Real.rpow_nonneg (by norm_num) _

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

def head (N : NormalAxis A) : ℕ :=
  Module.finrank (ZMod 2) (primeRelativeCharacters 2 N.1)

def orderLog (N : NormalAxis A) : ℕ := Nat.log 2 (Nat.card N.1)

def derivedHead (N : NormalAxis A) : ℕ :=
  primeNormalHeadMax 2 (N.1 ⊓ commutator A)

def radicalHead (N : NormalAxis A) : ℕ :=
  Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N.1))

def cost (N : NormalAxis A) (x y z : ℝ) : ℝ :=
  z*((head N : ℝ)+(max (derivedHead N) (radicalHead N) : ℕ)) +
    jointCapacitySupport (head N) (orderLog N) (derivedHead N) (x-z) y

def centerSlope (N : NormalAxis A) : ℕ := Nat.log 2 (Nat.card (Subgroup.center (A ⧸ N.1)))

def derivedSlope (N : NormalAxis A) : ℕ := Nat.log 2 (Nat.card (commutator (A ⧸ N.1)))

def polynomial (N : NormalAxis A) (B : Type) [Group B] [Finite B] : ℝ :=
  ((binaryStructuredEpiConstant (A ⧸ N.1) *
    (binaryCharacterRank B+2)^(binaryStructuredEpiConstant (A ⧸ N.1)) : ℕ) : ℝ)

/-- The checked three-invariant inequality exponentiates on the same
actual K and tail B. The first mark is allowed to be negative. -/
theorem mark_le (K : Full A B) (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    mark K.1 x y z ≤ mark B x y z * (2 : ℝ)^(cost (axis K) x y z) := by
  have ht := binarySubdirect_marked_transition K.1 K.2.1 K.2.2 x y z hy hz
  have ht' : exponent K.1 x y z ≤ exponent B x y z + cost (axis K) x y z := by
    change exponent K.1 x y z ≤ exponent B x y z +
      z*((head (axis K) : ℝ)+(max (derivedHead (axis K)) (radicalHead (axis K)) : ℕ)) +
      jointCapacitySupport (head (axis K)) (orderLog (axis K))
        (derivedHead (axis K)) (x-z) y at ht
    exact ht.trans_eq (add_assoc _ _ _)
  calc
    _ ≤ (2 : ℝ)^(exponent B x y z + cost (axis K) x y z) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ht'
    _ = _ := Real.rpow_add (by norm_num) _ _

/-- All maps in this literal quotient fibre are counted. Multiplication
by the original tail mark creates exactly one nonnegative epi tilt. -/
theorem epi_mul_mark_le (N : NormalAxis A) (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (x y z : ℝ) :
    (Nat.card {β : B →* A ⧸ N.1 // Function.Surjective β} : ℝ) * mark B x y z ≤
      polynomial N B * mark B (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  have hQ : IsPGroup 2 (A ⧸ N.1) :=
    hA.of_surjective (QuotientGroup.mk' N.1) (QuotientGroup.mk'_surjective N.1)
  let e := centerSlope N*binaryCharacterRank B + derivedSlope N*primeDerivedNormalRank 2 B
  have hbound := binaryStructured_epimorphism_card_le_polynomial hB hQ
  have hboundR : (Nat.card {β : B →* A ⧸ N.1 // Function.Surjective β} : ℝ) ≤
      polynomial N B * (2 : ℝ)^e := by
    dsimp only [polynomial,e,centerSlope,derivedSlope]
    exact_mod_cast hbound
  have he : (e : ℝ) = (centerSlope N : ℝ)*(binaryCharacterRank B : ℝ) +
      (derivedSlope N : ℝ)*(primeDerivedNormalRank 2 B : ℝ) := by
    simp only [e,Nat.cast_add,Nat.cast_mul]
  rw [← Real.rpow_natCast,he] at hboundR
  have hshift : (centerSlope N : ℝ)*(binaryCharacterRank B : ℝ) +
      (derivedSlope N : ℝ)*(primeDerivedNormalRank 2 B : ℝ) + exponent B x y z =
      exponent B (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
    unfold exponent
    ring
  calc
    _ ≤ (polynomial N B * (2 : ℝ)^((centerSlope N : ℝ)*(binaryCharacterRank B : ℝ) +
        (derivedSlope N : ℝ)*(primeDerivedNormalRank 2 B : ℝ))) * mark B x y z :=
      mul_le_mul_of_nonneg_right hboundR (mark_nonneg B x y z)
    _ = _ := by
      unfold mark
      rw [mul_assoc,← Real.rpow_add (by norm_num),hshift]

/-- The fixed-tail weighted recurrence is derived from actual Goursat
coding and the proved local and epi bounds. Every normal axis is retained;
there is no hypothesis asserting the desired recurrence or a row majorant. -/
theorem weighted_peel (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (w : NormalAxis A → ℝ) (hw : ∀ N, 0 ≤ w N)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ K : Full A B, w (axis K) * mark K.1 x y z) ≤
      ∑ N : NormalAxis A, w N * polynomial N B * (2 : ℝ)^(cost N x y z) *
        mark B (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  classical
  let W (d : Data A B) := w d.1 * (mark B x y z * (2 : ℝ)^(cost d.1 x y z))
  have hW (d : Data A B) : 0 ≤ W d :=
    mul_nonneg (hw d.1) (mul_nonneg (mark_nonneg B x y z)
      (Real.rpow_nonneg (by norm_num) _))
  have hpoint (K : Full A B) : w (axis K)*mark K.1 x y z ≤ W (code K) :=
    mul_le_mul_of_nonneg_left (mark_le K x y z hy hz) (hw (axis K))
  refine (sum_le_code_sum _ W hW hpoint).trans ?_
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro N _
  have hweight : 0 ≤ w N*(2 : ℝ)^(cost N x y z) :=
    mul_nonneg (hw N) (Real.rpow_nonneg (by norm_num) _)
  calc
    (∑ β : {β : B →* A ⧸ N.1 // Function.Surjective β}, W ⟨N,β⟩) =
        (w N*(2 : ℝ)^(cost N x y z)) *
          ((Nat.card {β : B →* A ⧸ N.1 // Function.Surjective β} : ℝ)*mark B x y z) := by
      simp only [W,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
      ring
    _ ≤ (w N*(2 : ℝ)^(cost N x y z)) *
        (polynomial N B*mark B (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z) :=
      mul_le_mul_of_nonneg_left (epi_mul_mark_le N hA hB x y z) hweight
    _ = _ := by ring

/-- A predicate on the original full subgroup remains on the left.
Enlargement to all literal maps gives an upper bound, without asserting
physical disjointness, acceptance, or deletion of any original condition. -/
theorem surviving_weighted_peel (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (P : Full A B → Prop) (w : NormalAxis A → ℝ) (hw : ∀ N, 0 ≤ w N)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ K : Full A B, if P K then w (axis K)*mark K.1 x y z else 0) ≤
      ∑ N : NormalAxis A, w N * polynomial N B * (2 : ℝ)^(cost N x y z) *
        mark B (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  classical
  refine le_trans (Finset.sum_le_sum (fun K _ => ?_)) (weighted_peel hA hB w hw x y z hy hz)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw (axis K)) (mark_nonneg K.1 x y z)

end BinaryMarkedGoursatPeel
end SymmetricSubgroupAsymptotics
