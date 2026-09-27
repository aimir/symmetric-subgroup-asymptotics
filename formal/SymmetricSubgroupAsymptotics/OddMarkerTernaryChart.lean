import SymmetricSubgroupAsymptotics.OddMarker
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The original three-point alternating kernel in ternary coordinates

The chart sends one in the additive field F₃ to the literal cycle
(0 1)(1 2) on the original Fin 3. Conjugation by every original S₃
permutation acts through its actual sign, with scalar +1 or -1.

The two signs are identified faithfully with F₃ units. Consequently
equality of scalar functions is exactly equality of the original sign
functions; repeated marker coordinates are not made independent.
All finite decisions concern only the two signs, three field elements,
and six permutations of the three original points.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-- The faithful scalar action of the two actual signs on F₃. -/
def signUnitHom : Multiplicative (ZMod 2) →* (ZMod 3)ˣ where
  toFun s := if s = 1 then 1 else -1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def signScalar (s : Multiplicative (ZMod 2)) : ZMod 3 := (signUnitHom s : ZMod 3)

@[simp] theorem signScalar_one : signScalar 1 = 1 := by decide +kernel

@[simp] theorem signScalar_nontrivial :
    signScalar (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by decide +kernel

theorem signScalar_mul (s t : Multiplicative (ZMod 2)) :
    signScalar (s*t) = signScalar s * signScalar t :=
  congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) (signUnitHom.map_mul s t)

theorem signScalar_injective : Function.Injective signScalar := by decide +kernel

@[simp] theorem signScalar_eq_iff (s t : Multiplicative (ZMod 2)) :
    signScalar s = signScalar t ↔ s = t := signScalar_injective.eq_iff

theorem signUnitHom_injective : Function.Injective signUnitHom := by
  intro s t h
  exact signScalar_injective (congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) h)

theorem signUnitHom_surjective : Function.Surjective signUnitHom := by
  intro u
  have hcases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by decide +kernel
  rcases hcases (u : ZMod 3) with hzero | hone | hneg
  · exact False.elim (u.ne_zero hzero)
  · refine ⟨1, ?_⟩
    apply Units.ext
    change (1 : ZMod 3) = (u : ZMod 3)
    exact hone.symm
  · refine ⟨Multiplicative.ofAdd (1 : ZMod 2), ?_⟩
    apply Units.ext
    change (-1 : ZMod 3) = (u : ZMod 3)
    exact hneg.symm

/-- A genuine two-sign equivalence, with no quotient of the sign labels. -/
def signScalarEquiv : Multiplicative (ZMod 2) ≃* (ZMod 3)ˣ :=
  MulEquiv.ofBijective signUnitHom ⟨signUnitHom_injective, signUnitHom_surjective⟩

@[simp] theorem signScalarEquiv_coe (s : Multiplicative (ZMod 2)) :
    (signScalarEquiv s : ZMod 3) = signScalar s := rfl

/-- Equality of the full scalar functions detects equality of the full
original sign functions on the same source, which may be infinite. -/
theorem signScalar_functions_eq_iff {J : Type*}
    (s t : J → Multiplicative (ZMod 2)) :
    (fun j => signScalar (s j)) = (fun j => signScalar (t j)) ↔ s = t := by
  constructor
  · intro h
    funext j
    exact signScalar_injective (congrFun h j)
  · rintro rfl
    rfl

theorem signScalar_characters_eq_iff {J : Type*} [Monoid J]
    (s t : J →* Multiplicative (ZMod 2)) :
    (fun j => signScalar (s j)) = (fun j => signScalar (t j)) ↔ s = t := by
  constructor
  · intro h
    apply DFunLike.ext
    intro j
    exact signScalar_injective (congrFun h j)
  · rintro rfl
    rfl

/-- This sends 0 to 1, 1 to 2, and 2 to 0 on the original point set. -/
def rotation : OddMarkerGroup := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- Explicit ternary rotations, before restricting to the original sign
kernel. Only three values and their nine multiplication equations occur. -/
def embedding : Multiplicative (ZMod 3) →* OddMarkerGroup where
  toFun z := rotation ^ z.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

@[simp] theorem embedding_generator :
    embedding (Multiplicative.ofAdd (1 : ZMod 3)) = rotation := by decide +kernel

theorem embedding_injective : Function.Injective embedding := by decide +kernel

theorem embedding_mem_kernel (z : Multiplicative (ZMod 3)) :
    embedding z ∈ oddMarkerSign.ker := by
  have h : ∀ w : Multiplicative (ZMod 3), oddMarkerSign (embedding w) = 1 := by
    decide +kernel
  exact h z

def kernelMap : Multiplicative (ZMod 3) →* oddMarkerSign.ker where
  toFun z := ⟨embedding z, embedding_mem_kernel z⟩
  map_one' := Subtype.ext embedding.map_one
  map_mul' z w := Subtype.ext (embedding.map_mul z w)

theorem kernelMap_injective : Function.Injective kernelMap := by
  intro z w h
  exact embedding_injective (congrArg Subtype.val h)

theorem kernelMap_surjective : Function.Surjective kernelMap := by
  have hc : Nat.card (Multiplicative (ZMod 3)) = Nat.card oddMarkerSign.ker := by
    rw [oddMarker_kernel_card, Nat.card_congr Multiplicative.toAdd,
      Nat.card_eq_fintype_card]
    exact ZMod.card 3
  exact ((Nat.bijective_iff_injective_and_card kernelMap).mpr
    ⟨kernelMap_injective, hc⟩).surjective

/-- The range is exactly the original sign kernel, not an abstract C₃. -/
theorem embedding_range : embedding.range = oddMarkerSign.ker := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact embedding_mem_kernel z
  · intro g hg
    obtain ⟨z, hz⟩ := kernelMap_surjective ⟨g, hg⟩
    exact ⟨z, congrArg Subtype.val hz⟩

/-- Ternary coordinates on precisely the actual original A₃ kernel. -/
def chart : Multiplicative (ZMod 3) ≃* oddMarkerSign.ker :=
  MulEquiv.ofBijective kernelMap ⟨kernelMap_injective, kernelMap_surjective⟩

@[simp] theorem chart_coe (z : Multiplicative (ZMod 3)) :
    (chart z : OddMarkerGroup) = embedding z := rfl

private def transposition : OddMarkerGroup := Equiv.swap (0 : Fin 3) 1

private theorem transposition_square : transposition * transposition = 1 := by decide +kernel

private theorem transposition_sign :
    oddMarkerSign transposition = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel

private theorem transposition_conjugate :
    ∀ z : Multiplicative (ZMod 3), transposition * embedding z * transposition⁻¹ =
      embedding (Multiplicative.ofAdd (-z.toAdd)) := by decide +kernel

private theorem embedding_conjugate_checked (g : OddMarkerGroup)
    (z : Multiplicative (ZMod 3)) :
    g * embedding z * g⁻¹ =
      embedding (Multiplicative.ofAdd (signScalar (oddMarkerSign g) * z.toAdd)) := by
  have hcomm (u : Multiplicative (ZMod 3)) :
      embedding u * embedding z * (embedding u)⁻¹ = embedding z :=
    ((Commute.all u z).map embedding).mul_inv_cancel
  by_cases hg : oddMarkerSign g = 1
  · rw [hg, signScalar_one, one_mul, ofAdd_toAdd]
    obtain ⟨u, hu⟩ := kernelMap_surjective ⟨g, hg⟩
    have hu' : embedding u = g := congrArg Subtype.val hu
    rw [← hu']
    exact hcomm u
  · have hcases : ∀ s : Multiplicative (ZMod 2),
        s = 1 ∨ s = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel
    have hsign := (hcases (oddMarkerSign g)).resolve_left hg
    have htg : oddMarkerSign (transposition * g) = 1 := by
      rw [map_mul, transposition_sign, hsign]
      decide +kernel
    obtain ⟨u, hu⟩ := kernelMap_surjective ⟨transposition * g, htg⟩
    have hu' : embedding u = transposition * g := congrArg Subtype.val hu
    have hg' : g = transposition * embedding u := by
      rw [hu', ← mul_assoc, transposition_square, one_mul]
    calc
      g * embedding z * g⁻¹ =
          transposition * (embedding u * embedding z * (embedding u)⁻¹) *
            transposition⁻¹ := by
        rw [hg', mul_inv_rev]
        simp only [mul_assoc]
      _ = transposition * embedding z * transposition⁻¹ := by rw [hcomm]
      _ = embedding (Multiplicative.ofAdd (-z.toAdd)) := transposition_conjugate z
      _ = embedding (Multiplicative.ofAdd (signScalar (oddMarkerSign g) * z.toAdd)) := by
        rw [hsign, signScalar_nontrivial, neg_one_mul]

/-- The conjugating element is an original S₃ permutation, and the
coefficient is computed from its original sign on those same points. -/
theorem chart_conjugate_coe (g : OddMarkerGroup) (z : Multiplicative (ZMod 3)) :
    g * (chart z : OddMarkerGroup) * g⁻¹ =
      (chart (Multiplicative.ofAdd (signScalar (oddMarkerSign g) * z.toAdd)) :
        OddMarkerGroup) := by
  simpa only [chart_coe] using embedding_conjugate_checked g z

theorem chart_conjugate (g : OddMarkerGroup) (z : Multiplicative (ZMod 3)) :
    MulAut.conjNormal g (chart z) =
      chart (Multiplicative.ofAdd (signScalar (oddMarkerSign g) * z.toAdd)) := by
  apply Subtype.ext
  exact chart_conjugate_coe g z

/-- The inverse coordinate also records the same actual conjugation. -/
theorem chart_symm_conjugate (g : OddMarkerGroup) (u : oddMarkerSign.ker) :
    (chart.symm (MulAut.conjNormal g u)).toAdd =
      signScalar (oddMarkerSign g) * (chart.symm u).toAdd := by
  obtain ⟨z, rfl⟩ := chart.surjective u
  simp only [chart_conjugate, chart.symm_apply_apply, toAdd_ofAdd]

end SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

end
