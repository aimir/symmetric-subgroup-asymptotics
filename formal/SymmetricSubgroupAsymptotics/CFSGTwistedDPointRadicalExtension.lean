import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalHom
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleTailAction
import Mathlib.GroupTheory.SemidirectProduct

/-! The actual all-rank relative tail acts on the full point radical
through its same fixed-field natural action. Literal conjugation gives
an actual semidirect hom and its actual central-quotient projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalExtension

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeTailEmbedding
open CFSGTwistedDFixedPoleShear CFSGTwistedDFixedPoleTailAction
open CFSGTwistedDPointRadicalHom CFSGTwistedA2FixedField

def tailAction (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q →* MulAut (Multiplicative (fixedSpace n q)) where
  toFun g := {
    toFun z := Multiplicative.ofAdd (fixedLinearHom n q g z.toAdd)
    invFun z := Multiplicative.ofAdd ((fixedLinearHom n q g).symm z.toAdd)
    left_inv z := by
      apply Multiplicative.toAdd.injective
      exact (fixedLinearHom n q g).symm_apply_apply z.toAdd
    right_inv z := by
      apply Multiplicative.toAdd.injective
      exact (fixedLinearHom n q g).apply_symm_apply z.toAdd
    map_mul' z t := by
      apply Multiplicative.toAdd.injective
      exact (fixedLinearHom n q g).map_add z.toAdd t.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change fixedLinearHom n q 1 z.toAdd = z.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change fixedLinearHom n q (g * h) z.toAdd =
      fixedLinearHom n q g (fixedLinearHom n q h z.toAdd)
    rw [map_mul]
    rfl

@[simp] theorem tailAction_apply (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (z : Multiplicative (fixedSpace n q)) :
    tailAction n q g z = Multiplicative.ofAdd (fixedLinearHom n q g z.toAdd) := rfl

theorem radicalHom_tailAction (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (z : Multiplicative (fixedSpace n q)) :
    radicalHom n q (tailAction n q g z) =
      tailRelativeHom n q g * radicalHom n q z * (tailRelativeHom n q g)⁻¹ := by
  have he : tailRelativeHom n q g * radicalHom n q z =
      radicalHom n q (tailAction n q g z) * tailRelativeHom n q g := by
    apply fixedLinearHom_injective (n + 1) q
    apply LinearEquiv.ext
    intro v
    rw [map_mul, map_mul]
    change fixedLinearHom (n + 1) q (tailRelativeHom n q g)
        (fixedLinearHom (n + 1) q (radicalHom n q z) v) =
      fixedLinearHom (n + 1) q (radicalHom n q (tailAction n q g z))
        (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v)
    rw [radicalHom_apply, radicalHom_apply]
    exact tail_poleShear_intertwine n q g z.toAdd v
  have hh := congrArg (fun x : relativeRootGroup (n + 1) q =>
    x * (tailRelativeHom n q g)⁻¹) he
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh.symm

def extensionHom (n : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedSpace n q) ⋊[tailAction n q] relativeRootGroup n q →*
      relativeRootGroup (n + 1) q :=
  SemidirectProduct.lift (radicalHom n q) (tailRelativeHom n q)
    (fun g => MonoidHom.ext (fun z => radicalHom_tailAction n q g z))

@[simp] theorem extensionHom_inl (n : ℕ) (q : CFSG.PrimePower)
    (z : Multiplicative (fixedSpace n q)) :
    extensionHom n q (SemidirectProduct.inl z) = radicalHom n q z := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom (n : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedSpace n q) ⋊[tailAction n q] relativeRootGroup n q →*
      (relativeRootGroup (n + 1) q ⧸ Subgroup.center (relativeRootGroup (n + 1) q)) :=
  (QuotientGroup.mk' (Subgroup.center (relativeRootGroup (n + 1) q))).comp (extensionHom n q)

@[simp] theorem projectiveExtensionHom_inl (n : ℕ) (q : CFSG.PrimePower)
    (z : Multiplicative (fixedSpace n q)) :
    projectiveExtensionHom n q (SemidirectProduct.inl z) = projectiveRadicalHom n q z := by
  change QuotientGroup.mk' _ (extensionHom n q (SemidirectProduct.inl z)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalExtension
