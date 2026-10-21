import SymmetricSubgroupAsymptotics.FourByTwoAutomorphismBinary
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T2
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum

/-! Actual C4×C2 coordinates for original regular8T2. The original two
generators and all eight original points remain literal. Its automorphism
2-group theorem is transported through this checked explicit chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RegularFourByTwoSeedCoordinates
open FourByTwoAutomorphismBinary
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T2.generators)

def element (v : Model) : Ambient :=
  BinaryMenuCayley8T2.generators 0 ^ v.toAdd.1.val *
    BinaryMenuCayley8T2.generators 1 ^ v.toAdd.2.val

theorem element_mem (v : Model) : element v ∈ H :=
  H.mul_mem (H.pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) _)
    (H.pow_mem (Subgroup.subset_closure (Set.mem_range_self 1)) _)

def hom : Model →* H where
  toFun v := ⟨element v,element_mem v⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    revert x
    decide +kernel
  map_mul' v w := by
    have h : ∀ (v w : Model) (x : Fin 8),element (v*w) x = (element v*element w) x := by
      decide +kernel
    apply Subtype.ext
    exact Equiv.ext (h v w)

theorem hom_injective : Function.Injective hom := by
  have h : ∀ (v w : Model),element v 0 = element w 0 → v = w := by decide +kernel
  intro v w he
  exact h v w (congrArg (fun g : H => g.val 0) he)

theorem hom_bijective : Function.Bijective hom := by
  letI : Fintype H := Fintype.ofFinite H
  apply (Fintype.bijective_iff_injective_and_card hom).mpr
  refine ⟨hom_injective,?_⟩
  have hH : Fintype.card H = 8 := by
    simpa only [Nat.card_eq_fintype_card] using BinaryMenuCayley8T2.exact_card
  rw [hH]
  norm_num [Model]

def chart : Model ≃* H := MulEquiv.ofBijective hom hom_bijective

theorem automorphisms_isPGroup : IsPGroup 2 (MulAut H) :=
  FourByTwoAutomorphismBinary.automorphisms_isPGroup.of_equiv (MulAut.congr chart)

theorem commutative : IsMulCommutative H := by
  refine ⟨⟨?_⟩⟩
  intro u v
  obtain ⟨a,rfl⟩ := chart.surjective u
  obtain ⟨b,rfl⟩ := chart.surjective v
  rw [←map_mul,←map_mul,mul_comm]

end SymmetricSubgroupAsymptotics.RegularFourByTwoSeedCoordinates
end
