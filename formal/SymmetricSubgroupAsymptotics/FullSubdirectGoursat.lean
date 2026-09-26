import Mathlib.GroupTheory.Goursat
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-! A full subdirect subgroup over one fixed complete tail has a literal
normal axis and one actual epimorphism from that same tail. The decoding
identity proves injectivity before any bound or physical weight is used.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace FullSubdirectGoursat

variable {A B : Type*} [Group A] [Group B]

abbrev Full (A B : Type*) [Group A] [Group B] :=
  {K : Subgroup (A × B) //
    Function.Surjective (Prod.fst ∘ K.subtype) ∧
    Function.Surjective (Prod.snd ∘ K.subtype)}

abbrev NormalAxis (A : Type*) [Group A] := {N : Subgroup A // N.Normal}

instance normalAxis_normal (N : NormalAxis A) : N.1.Normal := N.2

def axis (K : Full A B) : NormalAxis A :=
  ⟨K.1.goursatFst,Subgroup.normal_goursatFst K.2.1⟩

def second (K : Full A B) : K.1 →* B := (MonoidHom.snd A B).comp K.1.subtype

def originalQuotient (K : Full A B) : K.1 →* A ⧸ (axis K).1 :=
  (QuotientGroup.mk' (axis K).1).comp ((MonoidHom.fst A B).comp K.1.subtype)

theorem second_ker_le (K : Full A B) : (second K).ker ≤ (originalQuotient K).ker := by
  intro x hx
  have hs : x.1.2 = 1 := hx
  apply (QuotientGroup.eq_one_iff (N := (axis K).1) _).mpr
  change x.1.1 ∈ K.1.goursatFst
  apply Subgroup.mem_goursatFst.mpr
  simpa only [← hs] using x.2

/-- The quotient map is descended along the actual onto tail projection. -/
def quotientMap (K : Full A B) : B →* A ⧸ (axis K).1 :=
  (second K).liftOfSurjective K.2.2 ⟨originalQuotient K,second_ker_le K⟩

@[simp] theorem quotientMap_apply (K : Full A B) (x : K.1) :
    quotientMap K x.1.2 = QuotientGroup.mk' (axis K).1 x.1.1 :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem quotientMap_surjective (K : Full A B) : Function.Surjective (quotientMap K) := by
  intro q
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (axis K).1 q
  obtain ⟨x,hx⟩ := K.2.1 a
  refine ⟨x.1.2,?_⟩
  rw [quotientMap_apply]
  exact (congrArg (QuotientGroup.mk' (axis K).1) hx).trans ha

abbrev Data (A B : Type*) [Group A] [Group B] :=
  Σ N : NormalAxis A, {β : B →* A ⧸ N.1 // Function.Surjective β}

def code (K : Full A B) : Data A B :=
  ⟨axis K,quotientMap K,quotientMap_surjective K⟩

/-- Decoding retains both original product coordinates. -/
def decode (d : Data A B) : Subgroup (A × B) where
  carrier := {x | QuotientGroup.mk' d.1.1 x.1 = d.2.1 x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change QuotientGroup.mk' d.1.1 (x.1*y.1) = d.2.1 (x.2*y.2)
    rw [map_mul,map_mul,hx,hy]
  inv_mem' := by
    intro x hx
    change QuotientGroup.mk' d.1.1 x.1⁻¹ = d.2.1 x.2⁻¹
    rw [map_inv,map_inv,hx]

/-- The original full subgroup, including every cross-coordinate
correlation, is recovered from its literal axis and one actual map. -/
theorem decode_code (K : Full A B) : decode (code K) = K.1 := by
  ext x
  constructor
  · intro hx
    change QuotientGroup.mk' (axis K).1 x.1 = quotientMap K x.2 at hx
    obtain ⟨y,hy⟩ := K.2.2 x.2
    have hq : QuotientGroup.mk' (axis K).1 x.1 =
        QuotientGroup.mk' (axis K).1 y.1.1 :=
      hx.trans ((congrArg (quotientMap K) hy).symm.trans (quotientMap_apply K y))
    have ha : x.1*y.1.1⁻¹ ∈ K.1.goursatFst := by
      apply (QuotientGroup.eq_one_iff (N := (axis K).1) _).mp
      change QuotientGroup.mk' (axis K).1 (x.1*y.1.1⁻¹) = 1
      rw [map_mul,map_inv,hq,mul_inv_cancel]
    have hm := K.1.mul_mem (Subgroup.mem_goursatFst.mp ha) y.2
    have he : (x.1*y.1.1⁻¹,(1 : B))*y.1 = x := by
      apply Prod.ext
      · simp
      · change y.1.2 = x.2 at hy
        change (1 : B)*y.1.2 = x.2
        simpa only [one_mul] using hy
    exact he ▸ hm
  · intro hx
    exact (quotientMap_apply K ⟨x,hx⟩).symm

theorem code_injective : Function.Injective (code (A := A) (B := B)) := by
  intro K L h
  apply Subtype.ext
  exact (decode_code K).symm.trans ((congrArg decode h).trans (decode_code L))

section Finite
variable [Finite A] [Finite B]

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

local instance homFinite {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) := Finite.of_injective
      (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

local instance quotientFinite (N : NormalAxis A) : Finite (A ⧸ N.1) :=
  Finite.of_surjective (QuotientGroup.mk' N.1) (QuotientGroup.mk'_surjective N.1)

local instance dataFinite : Finite (Data A B) := by
  change Finite (Σ N : NormalAxis A,
    {β : B →* A ⧸ N.1 // Function.Surjective β})
  infer_instance

local instance fullFintype : Fintype (Full A B) := Fintype.ofFinite _
local instance dataFintype : Fintype (Data A B) := Fintype.ofFinite _

attribute [local instance] Fintype.ofFinite

/-- An arbitrary nonnegative weight on the exact code may be summed
without a quotient-automorphism divisor. Missing codes only overcount. -/
theorem sum_le_code_sum [Fintype (Full A B)] [Fintype (Data A B)]
    (f : Full A B → ℝ) (w : Data A B → ℝ)
    (hw : ∀ d, 0 ≤ w d) (hf : ∀ K, f K ≤ w (code K)) :
    (∑ K : Full A B, f K) ≤ ∑ d : Data A B, w d := by
  classical
  calc
    _ ≤ ∑ K : Full A B, w (code K) := Finset.sum_le_sum (fun K _ => hf K)
    _ = ∑ d ∈ Finset.univ.image code, w d := by
      rw [Finset.sum_image]
      intro K _ L _ he
      exact code_injective he
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun d _ _ => hw d)

end Finite
end FullSubdirectGoursat
end SymmetricSubgroupAsymptotics
