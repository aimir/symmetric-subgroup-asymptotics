import SymmetricSubgroupAsymptotics.Statements

/-!
# Actual homomorphic lift fibres and crossed homomorphisms

A fixed source and quotient map are retained. Choosing one actual lift
identifies its entire fibre, including any survival predicate, with the
corresponding crossed homomorphisms into the original kernel. No splitting
of the extension or independence between quotient columns is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {J Q B : Type*} [Group J] [Group Q] [Group B]

/-- Literal homomorphisms above one fixed quotient map. -/
def HomomorphicLift (π : Q →* B) (β : J →* B) :=
  {f : J →* Q // π.comp f = β}

instance homomorphicLift_finite [Finite J] [Finite Q] (π : Q →* B) (β : J →* B) :
    Finite (HomomorphicLift π β) := by
  apply Finite.of_injective (fun f : HomomorphicLift π β ↦ (f.1 : J → Q))
  intro f g h
  exact Subtype.ext (DFunLike.coe_injective h)

/-- Crossed homomorphisms for the action induced by an actual origin lift.
The value lies in the original kernel, not in a chosen coordinate model. -/
def KernelCocycle (π : Q →* B) (f₀ : J →* Q) :=
  {z : J → π.ker // ∀ x y,
    (z (x*y) : Q) = (z x : Q)*f₀ x*(z y : Q)*(f₀ x)⁻¹}

@[simp] theorem homomorphicLift_above (π : Q →* B) (β : J →* B)
    (f : HomomorphicLift π β) (x : J) : π (f.1 x) = β x :=
  DFunLike.congr_fun f.2 x

private theorem kernelCocycle_one (π : Q →* B) (f₀ : J →* Q)
    (z : KernelCocycle π f₀) : (z.1 1 : Q) = 1 := by
  have h := z.2 1 1
  simp only [map_one,mul_one,inv_one] at h
  exact mul_left_cancel (show (z.1 1 : Q)*(z.1 1 : Q) = (z.1 1 : Q)*1 by
    simpa using h.symm)

/-- Twisting the chosen actual lift by a crossed homomorphism. -/
def kernelCocycleLift (π : Q →* B) (β : J →* B) (f₀ : HomomorphicLift π β)
    (z : KernelCocycle π f₀.1) : HomomorphicLift π β :=
  ⟨{ toFun := fun x ↦ (z.1 x : Q)*f₀.1 x
     map_one' := by simp [kernelCocycle_one]
     map_mul' := fun x y ↦ by rw [z.2,map_mul]; group }, by
    apply MonoidHom.ext
    intro x
    change π ((z.1 x : Q)*f₀.1 x) = β x
    rw [map_mul,show π (z.1 x : Q) = 1 from (z.1 x).2,one_mul]
    exact homomorphicLift_above π β f₀ x⟩

/-- The difference of two literal lifts is a crossed homomorphism on the
same source. -/
def homomorphicLiftDifference (π : Q →* B) (β : J →* B)
    (f₀ f : HomomorphicLift π β) : KernelCocycle π f₀.1 :=
  ⟨fun x ↦ ⟨f.1 x*(f₀.1 x)⁻¹,by
    change π (f.1 x*(f₀.1 x)⁻¹) = 1
    rw [map_mul,map_inv,homomorphicLift_above,homomorphicLift_above,mul_inv_cancel]⟩,
    fun x y ↦ by change f.1 (x*y)*(f₀.1 (x*y))⁻¹ = _; rw [map_mul,map_mul]; group⟩

/-- Exact lift--cocycle correspondence for an arbitrary extension.
No global splitting is required; only an origin inside the actual fibre. -/
def homomorphicLiftEquivCocycle (π : Q →* B) (β : J →* B)
    (f₀ : HomomorphicLift π β) : HomomorphicLift π β ≃ KernelCocycle π f₀.1 where
  toFun := homomorphicLiftDifference π β f₀
  invFun := kernelCocycleLift π β f₀
  left_inv f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change (f.1 x*(f₀.1 x)⁻¹)*f₀.1 x = f.1 x
    group
  right_inv z := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    change ((z.1 x : Q)*f₀.1 x)*(f₀.1 x)⁻¹ = (z.1 x : Q)
    group

/-- Any later survival or surjectivity condition is transported exactly. -/
def homomorphicLiftRestrictedEquiv (π : Q →* B) (β : J →* B)
    (f₀ : HomomorphicLift π β) (P : HomomorphicLift π β → Prop) :
    {f : HomomorphicLift π β // P f} ≃
      {z : KernelCocycle π f₀.1 // P (kernelCocycleLift π β f₀ z)} :=
  (homomorphicLiftEquivCocycle π β f₀).subtypeEquiv
    (fun f ↦ by
      change P f ↔ P ((homomorphicLiftEquivCocycle π β f₀).symm
        ((homomorphicLiftEquivCocycle π β f₀) f))
      rw [Equiv.symm_apply_apply])

/-- A fibre is empty, or has exactly the full cocycle cardinality. -/
theorem homomorphicLift_empty_or_cocycle (π : Q →* B) (β : J →* B) :
    IsEmpty (HomomorphicLift π β) ∨
      ∃ f₀ : HomomorphicLift π β,
        Nat.card (HomomorphicLift π β) = Nat.card (KernelCocycle π f₀.1) := by
  classical
  by_cases h : Nonempty (HomomorphicLift π β)
  · obtain ⟨f₀⟩ := h
    exact Or.inr ⟨f₀,Nat.card_congr (homomorphicLiftEquivCocycle π β f₀)⟩
  · exact Or.inl (not_nonempty_iff.mp h)

/-- Onto lifts are a literal subset of the same-source cocycle fibre. -/
theorem surjective_homomorphicLift_card_le [Finite J] [Finite Q]
    (π : Q →* B) (β : J →* B) (f₀ : HomomorphicLift π β) :
    Nat.card {f : HomomorphicLift π β // Function.Surjective f.1} ≤
      Nat.card (KernelCocycle π f₀.1) := by
  rw [← Nat.card_congr (homomorphicLiftEquivCocycle π β f₀)]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- If the actual kernel is abelian, its conjugation action depends only
on the quotient element. In particular the action above fixed beta does
not change when a different origin lift is chosen. -/
theorem kernel_conjugation_eq_of_same_quotient
    (π : Q →* B) (hcomm : ∀ a b : π.ker, Commute (a : Q) (b : Q))
    {q q' : Q} (h : π q = π q') (a : π.ker) :
    q*(a : Q)*q⁻¹ = q'*(a : Q)*q'⁻¹ := by
  let d : π.ker := ⟨q'⁻¹*q,by
    change π (q'⁻¹*q) = 1
    rw [map_mul,map_inv,h,inv_mul_cancel]⟩
  have hc := (hcomm d a).eq
  change (q'⁻¹*q)*(a : Q) = (a : Q)*(q'⁻¹*q) at hc
  have he := congrArg (fun z : Q ↦ q'*z*q⁻¹) hc
  group at he ⊢
  exact he

end SymmetricSubgroupAsymptotics
