import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes
import Mathlib.Tactic.FinCases

/-! Construct the physical sixteen-point gauge by actual order-three
transport. Only the fixed fibre and one moving fibre are labelled by hand;
the other two labels are transported by the original group element. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourCubicFibreTransportGauge
open BinaryFourBlockAugmentation BinaryFourCubicNormalizerPointShapes

variable {G X : Type} [Group G] [MulAction G X] [Finite X]
    (block : X → Fin 4) (s : G)
    (fixed : Local ≃ {x : X // block x = 0})
    (moving : Local ≃ {x : X // block x = 1})

def pointMap (z : Points) : X :=
  ![(fixed z.1).1, (moving z.1).1,
    s^2 • (moving z.1).1, s • (moving z.1).1] z.2

theorem pointMap_block
    (hs : ∀ x : X, block (s • x) = blockCycle (block x)) (z : Points) :
    block (pointMap block s fixed moving z) = z.2 := by
  rcases z with ⟨v,b⟩
  have h0 := (fixed v).2
  have h1 := (moving v).2
  fin_cases b <;>
    simp [pointMap, pow_two, mul_smul, hs, h0, h1,
      blockCycle, Equiv.swap_apply_def]

theorem pointMap_injective
    (hs : ∀ x : X, block (s • x) = blockCycle (block x)) :
    Function.Injective (pointMap block s fixed moving) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have hij := congrArg block h
  rw [pointMap_block block s fixed moving hs,
    pointMap_block block s fixed moving hs] at hij
  change i = j at hij
  subst j
  refine Prod.ext ?_ rfl
  fin_cases i
  · exact fixed.injective (Subtype.ext (by simpa [pointMap] using h))
  · exact moving.injective (Subtype.ext (by simpa [pointMap] using h))
  · apply moving.injective
    apply Subtype.ext
    exact (MulAction.injective (s^2)) (by simpa [pointMap] using h)
  · apply moving.injective
    apply Subtype.ext
    exact (MulAction.injective s) (by simpa [pointMap] using h)

def pointEquiv
    (hs : ∀ x : X, block (s • x) = blockCycle (block x))
    (hcard : Nat.card X = 16) : Points ≃ X :=
  Equiv.ofBijective (pointMap block s fixed moving)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨pointMap_injective block s fixed moving hs, by
        rw [hcard]
        change Nat.card (Local × Fin 4) = 16
        rw [Nat.card_prod]
        norm_num [Nat.card_eq_fintype_card, Local, Scalar]⟩)

theorem pointMap_rotation (hs3 : s^3 = 1)
    (hfixed : ∀ v : Local, (fixed (localCycle v)).1 = s • (fixed v).1)
    (z : Points) :
    pointMap block s fixed moving (BinaryFourCubicNormalizerPointShapes.rotation z) =
      s • pointMap block s fixed moving z := by
  have htriple (x : X) : s • (s • (s • x)) = x := by
    simpa [pow_succ, mul_smul] using congrArg (fun a : G => a • x) hs3
  rcases z with ⟨v,b⟩
  fin_cases b <;>
    simp [pointMap, BinaryFourCubicNormalizerPointShapes.rotation, rotate,
      blockCycle, Equiv.swap_apply_def, pow_two, mul_smul, hfixed, htriple]

theorem pointEquiv_rotation
    (hs : ∀ x : X, block (s • x) = blockCycle (block x))
    (hcard : Nat.card X = 16) (hs3 : s^3 = 1)
    (hfixed : ∀ v : Local, (fixed (localCycle v)).1 = s • (fixed v).1)
    (z : Points) :
    pointEquiv block s fixed moving hs hcard
        (BinaryFourCubicNormalizerPointShapes.rotation z) =
      s • pointEquiv block s fixed moving hs hcard z :=
  pointMap_rotation block s fixed moving hs3 hfixed z

theorem pointMap_translation (g : G) (v : Local)
    (hcommute : ∀ x : X, s • (g • x) = g • (s • x))
    (hfixed : ∀ u : Local, g • (fixed u).1 = (fixed u).1)
    (hmoving : ∀ u : Local, (moving (u+v)).1 = g • (moving u).1)
    (z : Points) :
    pointMap block s fixed moving (translation v z) =
      g • pointMap block s fixed moving z := by
  rcases z with ⟨u,b⟩
  fin_cases b <;>
    simp [pointMap, BinaryFourCubicNormalizerPointShapes.translation,
      BinaryFourCubicNormalizerPointShapes.translate, pow_two, mul_smul,
      hfixed, hmoving, hcommute]

theorem pointEquiv_translation
    (hs : ∀ x : X, block (s • x) = blockCycle (block x))
    (hcard : Nat.card X = 16) (g : G) (v : Local)
    (hcommute : ∀ x : X, s • (g • x) = g • (s • x))
    (hfixed : ∀ u : Local, g • (fixed u).1 = (fixed u).1)
    (hmoving : ∀ u : Local, (moving (u+v)).1 = g • (moving u).1)
    (z : Points) :
    pointEquiv block s fixed moving hs hcard (translation v z) =
      g • pointEquiv block s fixed moving hs hcard z :=
  pointMap_translation block s fixed moving g v hcommute hfixed hmoving z

theorem pointMap_reflection (g : G)
    (hflip : ∀ x : X, g • (s • x) = s^2 • (g • x))
    (hflip2 : ∀ x : X, g • (s^2 • x) = s • (g • x))
    (hfixed : ∀ u : Local,
      (fixed (fun i => u (Equiv.swap 0 1 i))).1 = g • (fixed u).1)
    (hmoving : ∀ u : Local,
      (moving (fun i => u (Equiv.swap 0 1 i))).1 = g • (moving u).1)
    (z : Points) :
    pointMap block s fixed moving
        (BinaryFourCubicNormalizerPointShapes.reflection z) =
      g • pointMap block s fixed moving z := by
  rcases z with ⟨u,b⟩
  simp only [Equiv.swap_apply_def] at hfixed hmoving
  fin_cases b <;>
    simp [pointMap, BinaryFourCubicNormalizerPointShapes.reflection, reflect,
      Equiv.swap_apply_def, hfixed, hmoving, hflip, hflip2]

theorem pointEquiv_reflection
    (hs : ∀ x : X, block (s • x) = blockCycle (block x))
    (hcard : Nat.card X = 16) (g : G)
    (hflip : ∀ x : X, g • (s • x) = s^2 • (g • x))
    (hflip2 : ∀ x : X, g • (s^2 • x) = s • (g • x))
    (hfixed : ∀ u : Local,
      (fixed (fun i => u (Equiv.swap 0 1 i))).1 = g • (fixed u).1)
    (hmoving : ∀ u : Local,
      (moving (fun i => u (Equiv.swap 0 1 i))).1 = g • (moving u).1)
    (z : Points) :
    pointEquiv block s fixed moving hs hcard
        (BinaryFourCubicNormalizerPointShapes.reflection z) =
      g • pointEquiv block s fixed moving hs hcard z :=
  pointMap_reflection block s fixed moving g hflip hflip2 hfixed hmoving z

end SymmetricSubgroupAsymptotics.BinaryFourCubicFibreTransportGauge
