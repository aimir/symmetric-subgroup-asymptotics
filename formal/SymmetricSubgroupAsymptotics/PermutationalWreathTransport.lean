import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-! Transport actual wreath coordinates along an equivariant block chart.
No independence of the base coordinates or splitting of a subgroup is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationalWreathProduct

variable {D Q R I J : Type*} [Group D] [Group Q] [Group R]
  [MulAction Q I] [MulAction R J]
variable (e : Q ≃* R) (c : I ≃ J)
  (hc : ∀ q i, c (q • i) = e q • c i)

include e c hc

private theorem chart_symm_smul (q : Q) (j : J) :
    c.symm (e q • j) = q • c.symm j := by
  apply c.injective
  simp only [Equiv.apply_symm_apply, hc]

/-- Relabel only the actual top and block coordinates. -/
def transportHom : PermutationalWreathProduct D Q I →*
    PermutationalWreathProduct D R J where
  toFun w := ⟨fun j => w.left (c.symm j), e w.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · rfl
    · exact e.map_one
  map_mul' a b := by
    apply PermutationalWreathProduct.ext
    · funext j
      change a.left (c.symm j) * b.left (a.right⁻¹ • c.symm j) =
        a.left (c.symm j) * b.left (c.symm ((e a.right)⁻¹ • j))
      rw [← e.map_inv, chart_symm_smul e c hc]
    · exact e.map_mul _ _

@[simp] theorem transportHom_left (w : PermutationalWreathProduct D Q I) (j : J) :
    (transportHom e c hc w).left j = w.left (c.symm j) := rfl

@[simp] theorem transportHom_right (w : PermutationalWreathProduct D Q I) :
    (transportHom e c hc w).right = e w.right := rfl

theorem transportHom_bijective : Function.Bijective (transportHom (D := D) e c hc) := by
  constructor
  · intro a b h
    apply PermutationalWreathProduct.ext
    · funext i
      have hh := congrArg (fun w : PermutationalWreathProduct D R J => w.left (c i)) h
      simpa only [transportHom_left, Equiv.symm_apply_apply] using hh
    · exact e.injective (congrArg PermutationalWreathProduct.right h)
  · intro w
    refine ⟨⟨fun i => w.left (c i), e.symm w.right⟩, ?_⟩
    apply PermutationalWreathProduct.ext
    · funext j
      exact congrArg w.left (c.apply_symm_apply j)
    · exact e.apply_symm_apply _

/-- An exact group chart, usable on every actual subgroup and original quotient. -/
def transport : PermutationalWreathProduct D Q I ≃*
    PermutationalWreathProduct D R J :=
  MulEquiv.ofBijective (transportHom e c hc) (transportHom_bijective e c hc)

section Action
variable {X : Type*} [MulAction D X]

theorem transport_smul (w : PermutationalWreathProduct D Q I) (x : X) (i : I) :
    transport e c hc w • (x, c i) =
      ((w • (x, i)).1, c ((w • (x, i)).2)) := by
  change ((transportHom e c hc w).left (e w.right • c i) • x,
      e w.right • c i) = (w.left (w.right • i) • x, c (w.right • i))
  rw [← hc]
  simp only [transportHom_left, Equiv.symm_apply_apply]
end Action
end SymmetricSubgroupAsymptotics.PermutationalWreathProduct
