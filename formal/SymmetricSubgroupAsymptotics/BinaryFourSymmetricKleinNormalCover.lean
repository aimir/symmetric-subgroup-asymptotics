import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart
import SymmetricSubgroupAsymptotics.BinaryKleinTernaryNormalChain

/-! Every nontrivial normal subgroup of the actual S4 complement contains
its literal Klein subgroup. Only the retained small action is inspected. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourSymmetricKleinNormalCover

open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions SemidirectProduct

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

def klein : Subgroup SymmetricComplement :=
  BinaryFourCanonicalSymmetricInducedChart.localLinear.ker

theorem mem_klein (g : SymmetricComplement) :
    g ∈ klein ↔ g.left.right = 1 ∧ g.right = 1 := by
  have detect : ∀ (p : Klein) (z : Ternary) (b : Binary),
      (∀ x : Local, BinaryFourCanonicalSymmetricInducedChart.localLinear
        ⟨⟨p, z⟩, b⟩ x = x) ↔ z = 1 ∧ b = 1 := by decide +kernel
  change BinaryFourCanonicalSymmetricInducedChart.localLinear g = 1 ↔ _
  constructor
  · intro h
    apply (detect g.left.left g.left.right g.right).mp
    intro x
    rw [h]
    rfl
  · intro h
    apply LinearEquiv.ext
    exact (detect g.left.left g.left.right g.right).mpr h

instance : klein.Normal := inferInstanceAs
  BinaryFourCanonicalSymmetricInducedChart.localLinear.ker.Normal

theorem inl_mem_klein (g : Complement) :
    (inl g : SymmetricComplement) ∈ klein ↔
      g ∈ BinaryKleinTernaryNormalChain.kleinKernel := by
  rw [mem_klein]
  exact and_iff_left rfl

theorem minimal (W : Subgroup SymmetricComplement) (hW : W.Normal)
    (hWK : W ≤ klein) : W = ⊥ ∨ W = klein := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  let L : Subgroup Complement := W.comap inl
  have hL : L.Normal := by
    letI := hW
    exact inferInstance
  have hLK : L ≤ BinaryKleinTernaryNormalChain.kleinKernel := by
    intro x hx
    exact (inl_mem_klein x).mp (hWK hx)
  have hLb : L ≠ ⊥ := by
    intro hzero
    apply hb
    apply le_antisymm
    · intro x hx
      obtain ⟨_, hxright⟩ := (mem_klein x).mp (hWK hx)
      have hxform : (inl x.left : SymmetricComplement) = x :=
        SemidirectProduct.ext rfl hxright.symm
      have hxl : x.left ∈ L := hxform.symm ▸ hx
      rw [hzero] at hxl
      have hleft : x.left = 1 := hxl
      have hone : x = 1 := SemidirectProduct.ext hleft hxright
      exact hone
    · exact bot_le
  have hfull : L = BinaryKleinTernaryNormalChain.kleinKernel :=
    (BinaryKleinTernaryNormalChain.kleinKernel_minimal L hL hLK).resolve_left hLb
  apply le_antisymm hWK
  intro x hx
  obtain ⟨hxternary, hxright⟩ := (mem_klein x).mp hx
  have hxform : (inl x.left : SymmetricComplement) = x :=
    SemidirectProduct.ext rfl hxright.symm
  have hxl : x.left ∈ L := by
    rw [hfull]
    exact hxternary
  exact hxform ▸ hxl

theorem selfCentralizing (g : SymmetricComplement)
    (hg : ∀ v ∈ klein, g * v = v * g) : g ∈ klein := by
  have detect : ∀ (p : Klein) (z : Ternary) (b : Binary),
      (∀ q : Klein,
        ((⟨⟨p, z⟩, b⟩ : SymmetricComplement) * inl (inl q)).left.left =
        (inl (inl q) * (⟨⟨p, z⟩, b⟩ : SymmetricComplement)).left.left) →
      z = 1 ∧ b = 1 := by decide +kernel
  apply (mem_klein g).mpr
  apply detect g.left.left g.left.right g.right
  intro q
  exact congrArg (fun x : SymmetricComplement => x.left.left)
    (hg (inl (inl q)) ((mem_klein _).mpr ⟨rfl, rfl⟩))

theorem le_normal (N : Subgroup SymmetricComplement) (hN : N.Normal) (hNb : N ≠ ⊥) :
    klein ≤ N := by
  letI := hN
  exact le_of_minimal_selfCentralizing klein minimal selfCentralizing N hNb

end SymmetricSubgroupAsymptotics.BinaryFourSymmetricKleinNormalCover

end
