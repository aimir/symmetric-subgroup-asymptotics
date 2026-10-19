import SymmetricSubgroupAsymptotics.DerivedCubicTopEpiEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveInstances
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains

/-! Sharp cubic-character control for the actual cyclic and symmetric
three-point tops. The symmetric case uses the literal derived subgroup
of the same complete source, so no width restriction of an owner applies. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SharpThreePointTopEpiEnvelope
open Non2UnipotentPrefixFiniteMenu

/-- The existing literal D6 action is the full symmetric-three group. -/
def dihedralEquiv : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective NaturalFourNormalChains.dihedralThree
    ⟨by decide +kernel,NaturalFourNormalChains.dihedralThree_surjective⟩

private def epiTarget {J Q H : Type} [Group J] [Group Q] [Group H]
    (e : Q ≃* H) (phi : GroupEpimorphism J Q) : GroupEpimorphism J H :=
  ⟨e.toMonoidHom.comp phi.val,e.surjective.comp phi.property⟩

private theorem epiTarget_injective {J Q H : Type} [Group J] [Group Q] [Group H]
    (e : Q ≃* H) : Function.Injective (epiTarget (J := J) e) := by
  intro a b h
  apply Subtype.ext
  ext x
  apply e.injective
  exact DFunLike.congr_fun (congrArg Subtype.val h) x

def coefficient : ℝ := (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3) : ℝ)+1

variable {T : Type} [Group T] [Finite T]

 theorem cyclic_epi_card_le (e : T ≃* Multiplicative (ZMod 3))
    (hKP : KovacsPraegerAbelianizationBound) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J T) : ℝ)≤(3 : ℝ)^((b : ℝ)/3) := by
  letI : Finite (J →* Multiplicative (ZMod 3)) :=
    Finite.of_injective (fun f : J →* Multiplicative (ZMod 3) =>
      (f : J → Multiplicative (ZMod 3))) DFunLike.coe_injective
  let f : GroupEpimorphism J T → (J →* Multiplicative (ZMod 3)) :=
    fun phi => e.toMonoidHom.comp phi.val
  have hf : Function.Injective f := by
    intro a c h
    apply Subtype.ext
    ext x
    exact e.injective (DFunLike.congr_fun h x)
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := cyclicCharacter_card_le_abelianization J 3
  have h12 : (Nat.card (GroupEpimorphism J T) : ℝ)≤
      (Nat.card (Abelianization J) : ℝ) := by exact_mod_cast h1.trans h2
  exact h12.trans (hKP b J)

 theorem symmetric_epi_card_le (e : T ≃* Equiv.Perm (Fin 3))
    (hKP : KovacsPraegerAbelianizationBound) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J T) : ℝ)≤
      (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3) : ℝ)*(3 : ℝ)^((b : ℝ)/3) := by
  letI : Finite (J →* DihedralGroup 3) :=
    Finite.of_injective (fun f : J →* DihedralGroup 3 =>
      (f : J → DihedralGroup 3)) DFunLike.coe_injective
  let f := epiTarget (J := J) (e.trans dihedralEquiv.symm)
  have hf := epiTarget_injective (J := J) (e.trans dihedralEquiv.symm)
  have hn := Nat.card_le_card_of_injective f hf
  have hd := derived_cubic_top_epi_envelope
    (dihedralDerivedCyclicDual (ℓ := 3) (by decide)) hKP b J
  have hn' : (Nat.card (GroupEpimorphism J T) : ℝ)≤
      (Nat.card (GroupEpimorphism J (DihedralGroup 3)) : ℝ) := by exact_mod_cast hn
  exact hn'.trans hd

/-- An actual top equivalence is structural data, not a source count premise. -/
 theorem epi_card_le
    (e : (T ≃* Multiplicative (ZMod 3)) ⊕ (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J T) : ℝ)≤coefficient*(3 : ℝ)^((b : ℝ)/3) := by
  cases e with
  | inl e =>
    have h := cyclic_epi_card_le e hKP b J
    have hc : (1 : ℝ)≤coefficient := by
      unfold coefficient
      have hn := Nat.cast_nonneg (α := ℝ) (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3))
      linarith
    exact h.trans (by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<3) ((b : ℝ)/3)])
  | inr e =>
    have h := symmetric_epi_card_le e hKP b J
    have hc : (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3) : ℝ)≤coefficient := by
      unfold coefficient; linarith
    exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))

end SymmetricSubgroupAsymptotics.SharpThreePointTopEpiEnvelope
