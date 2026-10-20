import SymmetricSubgroupAsymptotics.AbelianSectionOmegaArithmetic

/-! The same prime-factor budget controls every abelian section through
actual subgroup embeddings and quotient maps. A quotient is never given
an unproved faithful permutation action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize

def SectionOmegaBound (M : ℕ) (G : Type) [Group G] : Prop :=
  ∀ (H A : Type) [Group H] [Finite H] [CommGroup A] [Finite A]
    (i : H →* G), Function.Injective i →
    ∀ (q : H →* A), Function.Surjective q → omega (Nat.card A) ≤ M

namespace SectionOmegaBound
variable {M : ℕ} {G Q : Type} [Group G] [Group Q]

theorem of_injective (h : SectionOmegaBound M G) (j : Q →* G)
    (hj : Function.Injective j) : SectionOmegaBound M Q := by
  intro H A _ _ _ _ i hi q hq
  exact h H A (j.comp i) (hj.comp hi) q hq

/-- The actual fibre product lifts sections of a quotient back to
subgroups of the original source. -/
theorem of_surjective [Finite G] (h : SectionOmegaBound M G) (f : G →* Q)
    (hf : Function.Surjective f) : SectionOmegaBound M Q := by
  intro H A _ _ _ _ j hj q hq
  let P : Subgroup (G × H) := {
    carrier := {z | f z.1 = j z.2}
    one_mem' := by change f 1 = j 1; simp only [map_one]
    mul_mem' := by
      intro a b ha hb
      change f (a.1*b.1) = j (a.2*b.2)
      rw [map_mul, map_mul, ha, hb]
    inv_mem' := by
      intro a ha
      change f a.1⁻¹ = j a.2⁻¹
      rw [map_inv, map_inv, ha] }
  let left : P →* G := {
    toFun z := z.val.1
    map_one' := rfl
    map_mul' _ _ := rfl }
  let right : P →* H := {
    toFun z := z.val.2
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hleft : Function.Injective left := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    apply hj
    exact a.property.symm.trans ((congrArg f hab).trans b.property)
  have hright : Function.Surjective right := by
    intro z
    obtain ⟨g, hg⟩ := hf (j z)
    exact ⟨⟨(g,z), hg⟩, rfl⟩
  exact h P A left hleft (q.comp right) (hq.comp hright)

/-- Every abelian section of the actual permutation source pays the same
2b budget, via its literal image in the original symmetric group. -/
theorem of_permutationGroup (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (G : Subgroup (Equiv.Perm (Fin b))) : SectionOmegaBound (2*b) G := by
  intro H A _ _ _ _ i hi q hq
  let f := G.subtype.comp i
  have hf : Function.Injective f := Subtype.val_injective.comp hi
  let e : H ≃* f.range := MonoidHom.ofInjective hf
  exact section_omega_le_twice_degree hKP f.range
    (q.comp e.symm.toMonoidHom) (hq.comp e.symm.surjective)

end SectionOmegaBound
end SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize
