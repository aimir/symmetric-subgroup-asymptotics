import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation

/-! Literal component transport along an original group element. The
fibre bijection is the original action, and a component element lifted
to a stabilizer is transported by g^-1*a*g. This yields an injective hom
into the chosen base component without supplying any new local profile. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBlockComponentConjugation

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (x y : X) (g : A) (hy : g • x = y)

def fibreConjEquiv : originalBlockFibre b x ≃ originalBlockFibre b y where
  toFun ω := ⟨g • ω.val, by rw [hb, ω.property, hy]⟩
  invFun ω := ⟨g⁻¹ • ω.val, by rw [hb, ω.property, ← hy, inv_smul_smul]⟩
  left_inv ω := Subtype.ext (inv_smul_smul g ω.val)
  right_inv ω := Subtype.ext (smul_inv_smul g ω.val)

theorem inverse_conjugate_mem (q : originalBlockComponent b hb y) :
    (fibreConjEquiv b hb x y g hy).symm.permCongrHom q.val ∈
      originalBlockComponent b hb x := by
  obtain ⟨a, ha⟩ := q.property
  let c : MulAction.stabilizer A x := ⟨g⁻¹ * a.val * g, by
    change (g⁻¹ * a.val * g) • x = x
    simp only [mul_smul]
    rw [hy, a.property, ← hy, inv_smul_smul]⟩
  refine ⟨c, ?_⟩
  apply Equiv.ext
  intro ω
  apply Subtype.ext
  let e := fibreConjEquiv b hb x y g hy
  have hw := congrArg (fun p : Equiv.Perm (originalBlockFibre b y) => (p (e ω)).val) ha
  change a.val • (g • ω.val) = (q.val (e ω)).val at hw
  change (g⁻¹ * a.val * g) • ω.val = g⁻¹ • (q.val (e ω)).val
  calc
    _ = g⁻¹ • (a.val • (g • ω.val)) := by simp only [mul_smul]
    _ = _ := congrArg (fun z : Ω => g⁻¹ • z) hw

def componentEmbedding : originalBlockComponent b hb y →* originalBlockComponent b hb x :=
  (((fibreConjEquiv b hb x y g hy).symm.permCongrHom.toMonoidHom).comp
    (originalBlockComponent b hb y).subtype).codRestrict
      (originalBlockComponent b hb x) (inverse_conjugate_mem b hb x y g hy)

theorem componentEmbedding_injective : Function.Injective (componentEmbedding b hb x y g hy) := by
  intro q r he
  apply Subtype.ext
  apply (fibreConjEquiv b hb x y g hy).symm.permCongrHom.injective
  exact congrArg Subtype.val he

end SymmetricSubgroupAsymptotics.OriginalBlockComponentConjugation
