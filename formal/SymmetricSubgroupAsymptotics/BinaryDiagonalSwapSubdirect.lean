import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapNormalCover

/-!
# A subdirect dichotomy in the common-linear two-block model

For a subgroup containing the diagonal translations and the actual pure
swap, surjectivity of its first block-stabilizer projection has only two
possibilities. The projection is injective, or the subgroup is the entire
common-linear model. The proof identifies its kernel with the second
translation fiber and applies irreducibility; no cocycle classification
or subgroup-order comparison is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwapSubdirect

open SemidirectProduct BinaryDiagonalSwap

variable {V R : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V) (G : Subgroup (Model φ))

def parity : G →* Binary :=
  ((MonoidHom.snd R Binary).comp (rightHom : Model φ →* R × Binary)).comp G.subtype

abbrev Even := (parity φ G).ker

def underlying : Even φ G →* Model φ := G.subtype.comp (Even φ G).subtype

theorem underlying_injective : Function.Injective (underlying φ G) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem underlying_mem (g : Even φ G) : underlying φ G g ∈ G := g.val.property

theorem even_right (g : Even φ G) : (underlying φ G g).right.2 = 1 := g.property

theorem even_right_pair (g : Even φ G) :
    (underlying φ G g).right = ((underlying φ G g).right.1, 1) :=
  Prod.ext rfl (even_right φ G g)

/-- The first local affine action of the actual block stabilizer. -/
def first : Even φ G →* Local φ where
  toFun g := ⟨(underlying φ G g).left.1, (underlying φ G g).right.1⟩
  map_one' := rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change ((underlying φ G g).left *
          action φ (underlying φ G g).right (underlying φ G h).left).1 =
        (underlying φ G g).left.1 *
          φ (underlying φ G g).right.1 (underlying φ G h).left.1
      rw [even_right_pair φ G g, action_one]
      rfl
    · rfl

def secondTranslation : V →* Model φ :=
  (inl : V × V →* Model φ).comp (MonoidHom.inr V V)

theorem secondTranslation_apply (v : V) : secondTranslation φ v = inl (1, v) := rfl

/-- The exact second-coordinate fiber inside the given subgroup. -/
def secondFiber : Subgroup V := G.comap (secondTranslation φ)

theorem mem_first_ker_iff (g : Even φ G) :
    g ∈ (first φ G).ker ↔
      underlying φ G g = secondTranslation φ (underlying φ G g).left.2 := by
  constructor
  · intro hg
    have he := MonoidHom.mem_ker.mp hg
    have hl : (underlying φ G g).left.1 = 1 :=
      congrArg (fun x : Local φ ↦ x.left) he
    have hr : (underlying φ G g).right.1 = 1 :=
      congrArg (fun x : Local φ ↦ x.right) he
    exact SemidirectProduct.ext (Prod.ext hl rfl)
      (Prod.ext hr (even_right φ G g))
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · exact congrArg (fun x : Model φ ↦ x.left.1) hg
    · exact congrArg (fun x : Model φ ↦ x.right.1) hg

/-- Every element of the second fiber is in the projection kernel. -/
def fiberToKernel (v : secondFiber φ G) : (first φ G).ker :=
  ⟨⟨⟨secondTranslation φ v, v.property⟩, by
    change (1 : Binary) = 1
    rfl⟩, by
    apply MonoidHom.mem_ker.mpr
    rfl⟩

theorem fiberToKernel_underlying (v : secondFiber φ G) :
    underlying φ G (fiberToKernel φ G v).val = secondTranslation φ v := rfl

/-- Conversely, the kernel has no coordinates beyond the second fiber. -/
theorem kernel_second_mem (g : (first φ G).ker) :
    (underlying φ G g.val).left.2 ∈ secondFiber φ G := by
  change secondTranslation φ (underlying φ G g.val).left.2 ∈ G
  rw [← (mem_first_ker_iff φ G g.val).mp g.property]
  exact underlying_mem φ G g.val

theorem secondFiber_invariant (hsurj : Function.Surjective (first φ G)) :
    ∀ r v, v ∈ secondFiber φ G → φ r v ∈ secondFiber φ G := by
  intro r v hv
  obtain ⟨g, hg⟩ := hsurj (inr r)
  have hr : (underlying φ G g).right.1 = r :=
    congrArg (fun x : Local φ ↦ x.right) hg
  have hc := G.mul_mem (G.mul_mem (underlying_mem φ G g) hv)
    (G.inv_mem (underlying_mem φ G g))
  change underlying φ G g * inl (1, v) * (underlying φ G g)⁻¹ ∈ G at hc
  rw [conj_inl, even_right_pair φ G g, hr, action_one, map_one] at hc
  exact hc

theorem first_injective_of_fiber_bot (hbot : secondFiber φ G = ⊥) :
    Function.Injective (first φ G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ (first φ G).ker := MonoidHom.mem_ker.mpr hg
  have hv : (underlying φ G g).left.2 = 1 :=
    Subgroup.mem_bot.mp (hbot ▸ kernel_second_mem φ G ⟨g, hmem⟩)
  apply underlying_injective φ G
  rw [(mem_first_ker_iff φ G g).mp hmem, hv, map_one, map_one]

theorem eq_top_of_fiber_top
    (hsurj : Function.Surjective (first φ G))
    (hdiag : ∀ v : V, (inl (v, v) : Model φ) ∈ G)
    (hswap : (inr (1, C2Wreath.gen) : Model φ) ∈ G)
    (htop : secondFiber φ G = ⊤) : G = ⊤ := by
  have hsecond (v : V) : (inl (1, v) : Model φ) ∈ G := by
    change v ∈ secondFiber φ G
    rw [htop]
    trivial
  have hfirst (v : V) : (inl (v, 1) : Model φ) ∈ G := by
    have h := G.mul_mem (hdiag v) (hsecond v⁻¹)
    rw [← map_mul] at h
    simpa only [Prod.mk_mul_mk, mul_one, mul_inv_cancel] using h
  have htranslations (v : V × V) : (inl v : Model φ) ∈ G := by
    have h := G.mul_mem (hfirst v.1) (hsecond v.2)
    rw [← map_mul] at h
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta] using h
  have hlinear (r : R) : (inr (r, 1) : Model φ) ∈ G := by
    obtain ⟨g, hg⟩ := hsurj (inr r)
    have hl : (underlying φ G g).left.1 = 1 :=
      congrArg (fun x : Local φ ↦ x.left) hg
    have hr : (underlying φ G g).right.1 = r :=
      congrArg (fun x : Local φ ↦ x.right) hg
    have he : (inl (1, (underlying φ G g).left.2⁻¹) : Model φ) *
        underlying φ G g = inr (r, 1) := by
      apply SemidirectProduct.ext
      · simp only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply, left_inr]
        apply Prod.ext
        · change 1 * (underlying φ G g).left.1 = 1
          exact (one_mul _).trans hl
        · change (underlying φ G g).left.2⁻¹ * (underlying φ G g).left.2 = 1
          exact inv_mul_cancel _
      · simp only [mul_right, right_inl, one_mul, right_inr]
        exact Prod.ext hr (even_right φ G g)
    exact he ▸ G.mul_mem (hsecond (underlying φ G g).left.2⁻¹) (underlying_mem φ G g)
  have hcomplement (r : R × Binary) : (inr r : Model φ) ∈ G := by
    rcases r with ⟨r, c⟩
    rcases C2Wreath.cases c with rfl | rfl
    · exact hlinear r
    · have h := G.mul_mem (hlinear r) hswap
      rw [← map_mul] at h
      simpa only [Prod.mk_mul_mk, mul_one, one_mul] using h
  apply le_antisymm le_top
  intro g _
  rw [← inl_left_mul_inr_right g]
  exact G.mul_mem (htranslations g.left) (hcomplement g.right)

/-- The graph branch and the full-fiber branch are both retained. -/
theorem first_injective_or_eq_top (hirr : Irreducible φ)
    (hsurj : Function.Surjective (first φ G))
    (hdiag : ∀ v : V, (inl (v, v) : Model φ) ∈ G)
    (hswap : (inr (1, C2Wreath.gen) : Model φ) ∈ G) :
    Function.Injective (first φ G) ∨ G = ⊤ := by
  rcases hirr (secondFiber φ G) (secondFiber_invariant φ G hsurj) with h | h
  · exact Or.inl (first_injective_of_fiber_bot φ G h)
  · exact Or.inr (eq_top_of_fiber_top φ G hsurj hdiag hswap h)

theorem parity_surjective
    (hswap : (inr (1, C2Wreath.gen) : Model φ) ∈ G) :
    Function.Surjective (parity φ G) := by
  intro c
  rcases C2Wreath.cases c with rfl | rfl
  · exact ⟨1, (parity φ G).map_one⟩
  · exact ⟨⟨inr (1, C2Wreath.gen), hswap⟩, rfl⟩

end BinaryDiagonalSwapSubdirect
end SymmetricSubgroupAsymptotics

end
