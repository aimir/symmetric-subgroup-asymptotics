import Mathlib.Algebra.Group.Action.Pi
import SymmetricSubgroupAsymptotics.FiniteActionFibreBurnside

/-! Complete subset labels for a pointwise product of a singleton orbit
and one complementary orbit. All product orbits, not a chosen subfamily. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoOrbitProductSubsetLabels
variable {J G X : Type*} [Group G] [MulAction G X]

def orbitLabels (z w : X) (hw : w ≠ z)
    (hfix : ∀ g : G, g • z = z)
    (htrans : ∀ x y : X, x ≠ z → y ≠ z → ∃ g : G, g • y = x) :
    MulAction.orbitRel.Quotient (J → G) (J → X) ≃ Set J := by
  classical
  let f : (J → X) → Set J := fun x => {i | x i ≠ z}
  have hinv (g : G) (x : X) : g • x ≠ z ↔ x ≠ z := by
    constructor
    · intro h he
      exact h (he ▸ hfix g)
    · intro h he
      have hh := congrArg (fun y : X => g⁻¹ • y) he
      dsimp only at hh
      rw [inv_smul_smul,hfix] at hh
      exact h hh
  have hf : Function.Surjective f := by
    intro s
    refine ⟨fun i => if i ∈ s then w else z,?_⟩
    ext i
    by_cases hi : i ∈ s <;> simp [f,hi,hw]
  have hmap (g : J → G) (x : J → X) : f (g • x) = f x := by
    ext i
    exact hinv (g i) (x i)
  have hfibre (x y : J → X) (hxy : f x = f y) : ∃ g : J → G, g • y = x := by
    have hex (i : J) : ∃ g : G, g • y i = x i := by
      have he : (x i ≠ z) ↔ (y i ≠ z) := Set.ext_iff.mp hxy i
      by_cases hx : x i = z
      · have hy : y i = z := by
          by_contra hy
          exact (he.mpr hy) hx
        exact ⟨1,by rw [hy,hx,one_smul]⟩
      · exact htrans (x i) (y i) hx (he.mp hx)
    refine ⟨fun i => Classical.choose (hex i),?_⟩
    funext i
    exact Classical.choose_spec (hex i)
  exact FiniteActionFibreBurnside.orbitQuotientEquiv f hf hmap hfibre

end SymmetricSubgroupAsymptotics.TwoOrbitProductSubsetLabels
