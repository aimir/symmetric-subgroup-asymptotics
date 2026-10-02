import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Central projective maps on every literal quotient

Let `pi : G -> P` be an epimorphism with central kernel.  For every normal
subgroup `M` of `G`, the induced map

`G / M -> P / pi(M)`

is again onto and has central kernel.  More precisely, its kernel is an
epimorphic image of `ker pi`.  This is the small structural fact needed to
pass from a faithful linear complement to every literal quotient occurring
in the degree-nine primitive-affine owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C2 := Multiplicative (ZMod 2)

namespace ProjectiveCentralQuotient

variable {G P : Type*} [Group G] [Group P] [Finite G] [Finite P]
  (pi : G →* P) (hpi : Function.Surjective pi)
  (M : {M : Subgroup G // M.Normal})

local instance hM : M.1.Normal := M.2

/-- The normal projective image, bundled so that the chosen surjectivity proof
is retained in the quotient's type and its normality instance. -/
def normalImage : {N : Subgroup P // N.Normal} :=
  ⟨Subgroup.map pi M.1, Subgroup.Normal.map M.2 pi hpi⟩

local instance hMapM : (normalImage pi hpi M).1.Normal :=
  (normalImage pi hpi M).2

/-- The projective map induced on a literal normal quotient. -/
def map : G ⧸ M.1 →* P ⧸ (normalImage pi hpi M).1 :=
  QuotientGroup.map M.1 (normalImage pi hpi M).1 pi (by
    intro g hg
    exact ⟨g, hg, rfl⟩)

theorem map_surjective : Function.Surjective (map pi hpi M) := by
  intro y
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (normalImage pi hpi M).1 y
  obtain ⟨g, rfl⟩ := hpi p
  exact ⟨QuotientGroup.mk' M.1 g, rfl⟩

/-- The original central kernel maps onto the kernel of the induced map. -/
def kernelMap : pi.ker →* (map pi hpi M).ker where
  toFun k := ⟨QuotientGroup.mk' M.1 k.1, by
    rw [MonoidHom.mem_ker]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨1, M.1.one_mem, by simpa using k.2.symm⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp

theorem kernelMap_surjective : Function.Surjective (kernelMap pi hpi M) := by
  rintro ⟨z, hz⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M.1 z
  have himage : pi g ∈ (normalImage pi hpi M).1 := by
    rw [MonoidHom.mem_ker] at hz
    exact (QuotientGroup.eq_one_iff _).mp hz
  obtain ⟨m, hm, hmg⟩ := himage
  let k : G := m⁻¹ * g
  have hk : k ∈ pi.ker := by
    rw [MonoidHom.mem_ker]
    change pi (m⁻¹ * g) = 1
    rw [map_mul, map_inv, hmg, inv_mul_cancel]
  refine ⟨⟨k, hk⟩, ?_⟩
  apply Subtype.ext
  change QuotientGroup.mk' M.1 k = QuotientGroup.mk' M.1 g
  change QuotientGroup.mk' M.1 (m⁻¹ * g) = QuotientGroup.mk' M.1 g
  rw [map_mul, map_inv]
  have hmone : QuotientGroup.mk' M.1 m = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hm
  rw [hmone, inv_one, one_mul]

/-- Centrality survives passage to every literal normal quotient. -/
theorem central_kernel
    (hcentral : ∀ z ∈ pi.ker, ∀ g : G, z * g = g * z) :
    ∀ z ∈ (map pi hpi M).ker, ∀ x : G ⧸ M.1, z * x = x * z := by
  intro z hz x
  obtain ⟨k, hk⟩ := kernelMap_surjective pi hpi M ⟨z, hz⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M.1 x
  have hkval : QuotientGroup.mk' M.1 k.1 = z :=
    congrArg Subtype.val hk
  rw [← hkval, ← map_mul, ← map_mul, hcentral k.1 k.2 g]

/-- The induced kernel has no more elements than the original kernel. -/
theorem card_kernel_le :
    Nat.card (map pi hpi M).ker ≤ Nat.card pi.ker :=
  Nat.card_le_card_of_surjective (kernelMap pi hpi M)
    (kernelMap_surjective pi hpi M)

end ProjectiveCentralQuotient

/-! ## A faithful binary character for a kernel of order at most two -/

/-- Every finite group of cardinality at most two embeds in `C2`.  Keeping
this as a paired map/injectivity datum avoids choosing a cyclic generator in
the degree-nine quotient constructor. -/
noncomputable def binaryEmbeddingOfCardLETwo
    (K : Type*) [Group K] [Finite K] (hK : Nat.card K ≤ 2) :
    {chi : K →* C2 // Function.Injective chi} :=
  Classical.choice (show Nonempty {chi : K →* C2 // Function.Injective chi} from by
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hcard : Nat.card K = 1 ∨ Nat.card K = 2 := by omega
    rcases hcard with hcard | hcard
    · letI : Subsingleton K := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact ⟨⟨1, fun _ _ _ => Subsingleton.elim _ _⟩⟩
    · have hC2 : Nat.card C2 = 2 := by simp
      let e : K ≃* C2 := mulEquivOfPrimeCardEq hcard hC2
      exact ⟨⟨e.toMonoidHom, e.injective⟩⟩)

end SymmetricSubgroupAsymptotics
