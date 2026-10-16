import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricNaturalChart
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalEquiv
import SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassification

/-! Original S4 induced-plane chart, including the actual order-six
local epimorphism. Reflection generation excludes an order-three local
quotient, before local-plane uniqueness is applied. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourS4OriginalInducedChart

open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions
open BinaryFourCanonicalSymmetricInducedChart

local instance : Fintype Klein :=
  Fintype.ofEquiv Local (Multiplicative.ofAdd : Local ≃ Klein)
local instance : Fintype Ternary :=
  Fintype.ofEquiv (ZMod 3) (Multiplicative.ofAdd : ZMod 3 ≃ Ternary)
local instance : Fintype Binary :=
  Fintype.ofEquiv (ZMod 2) (Multiplicative.ofAdd : ZMod 2 ≃ Binary)

local instance : DecidableEq Klein := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))
local instance : DecidableEq Ternary := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))
local instance : DecidableEq Binary := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))

private def reflectionValue (z : Ternary) : SymmetricComplement :=
  ⟨SemidirectProduct.inr z, Multiplicative.ofAdd 1⟩

private def reflection (z : Ternary) : stabilizer :=
  ⟨reflectionValue z, by
    change blocks (reflectionValue z) 0 = 0
    revert z
    decide +kernel⟩

private theorem reflection_square (z : Ternary) : reflection z ^ 2 = 1 := by
  apply Subtype.ext
  have hs : ∀ z : Ternary,
      (reflectionValue z ^ 2).left.left = 1 ∧
      (reflectionValue z ^ 2).left.right = 1 ∧
      (reflectionValue z ^ 2).right = 1 := by decide +kernel
  exact SemidirectProduct.ext
    (SemidirectProduct.ext (hs z).1 (hs z).2.1) (hs z).2.2

private theorem reflection_decomposition (h : stabilizer) :
    ∃ z : Ternary, h = reflection z ∨ h = reflection z * reflection 1 := by
  rcases h with ⟨⟨⟨p, z⟩, b⟩, hh⟩
  have hd : ∀ (p : Klein) (z : Ternary) (b : Binary),
      blocks ⟨⟨p, z⟩, b⟩ 0 = 0 →
      (p = (reflectionValue z).left.left ∧ z = (reflectionValue z).left.right ∧
        b = (reflectionValue z).right) ∨
      (p = (reflectionValue z * reflectionValue 1).left.left ∧
        z = (reflectionValue z * reflectionValue 1).left.right ∧
        b = (reflectionValue z * reflectionValue 1).right) := by
    decide +kernel
  refine ⟨z, ?_⟩
  rcases hd p z b hh with h | h
  · exact Or.inl (Subtype.ext (SemidirectProduct.ext
      (SemidirectProduct.ext h.1 h.2.1) h.2.2))
  · exact Or.inr (Subtype.ext (SemidirectProduct.ext
      (SemidirectProduct.ext h.1 h.2.1) h.2.2))

private theorem involution_eq_one_of_card_three
    {L : Type} [Group L] [Finite L] (hL : Nat.card L = 3)
    (x : L) (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h3 : orderOf x ∣ 3 := by simpa only [hL] using orderOf_dvd_natCard x
  have h1 : orderOf x ∣ 1 := by
    simpa only [show Nat.gcd 2 3 = 1 from by decide] using Nat.dvd_gcd h2 h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem canonicalLocal_no_card_three_quotient
    {L : Type} [Group L] [Finite L]
    (f : stabilizer →* L) (hf : Function.Surjective f) (hL : Nat.card L = 3) : False := by
  have hrefl (z : Ternary) : f (reflection z) = 1 := by
    apply involution_eq_one_of_card_three hL
    rw [← map_pow, reflection_square, map_one]
  have hall (h : stabilizer) : f h = 1 := by
    obtain ⟨z, hz | hz⟩ := reflection_decomposition h
    · rw [hz, hrefl]
    · rw [hz, map_mul, hrefl, hrefl, one_mul]
  have hsub : Subsingleton L := ⟨by
    intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [hall, hall]⟩
  have hsmall : Nat.card L ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

variable {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [_root_.Module Scalar V] [FiniteDimensional Scalar V]
    (H : Subgroup G) (eG : G ≃* SymmetricComplement) (eH : H ≃* stabilizer)
    (commutes : ∀ h : H, eG (h : G) = (eH h : SymmetricComplement))
    (hdim : _root_.Module.finrank Scalar V = 2)

/-- The same local epimorphism and faithful plane give the complete
original coinduced-to-canonical chart, retaining the full S4 reflection. -/
def originalCoinducedChart_of_local_epi
    {L : Type} [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (theta : Representation Scalar L V) (htheta : Function.Injective theta) :
    Representation.Equiv (Representation.coind H.subtype (theta.comp f))
      (fullCoordinatesRepresentation.comp eG.toMonoidHom) := by
  have htarget : Nat.card L = 6 := by
    rcases hL with h3 | h6
    · exact False.elim (canonicalLocal_no_card_three_quotient
        (f.comp eH.symm.toMonoidHom) (hf.comp eH.symm.surjective) h3)
    · exact h6
  have hH : Nat.card H = 6 := (Nat.card_congr eH.toEquiv).trans stabilizer_card
  have hfi : Function.Injective f :=
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, hH.trans htarget.symm⟩).1
  let eV := BinaryPlaneKernelClassification.representationEquiv_of_card_six
    (theta.comp f) (localRepresentation.comp eH.toMonoidHom) hH hdim
    (by rw [_root_.Module.finrank_pi]; simp) (htheta.comp hfi)
    (localRepresentation_injective.comp eH.injective)
  let e₁ := CoinducedGroupLocalTransport.equivalence
    H stabilizer eG eH commutes (theta.comp f) localRepresentation eV
  let e₂ : Representation.Equiv
      ((Representation.coind stabilizer.subtype localRepresentation).comp eG.toMonoidHom)
      (fullCoordinatesRepresentation.comp eG.toMonoidHom) := {
    toLinearEquiv := fullCoinducedChart.symm.toLinearEquiv
    isIntertwining' := fun g => fullCoinducedChart.symm.isIntertwining' (eG g) }
  exact e₁.trans e₂

end SymmetricSubgroupAsymptotics.BinaryFourS4OriginalInducedChart

end
