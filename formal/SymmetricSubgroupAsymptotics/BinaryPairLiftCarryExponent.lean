import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergSquareCarries
import SymmetricSubgroupAsymptotics.AbelianizationExponentFromLiftCarries
import SymmetricSubgroupAsymptotics.AbelianizationSaturationRelativeRadical

/-! The five sparse square-carry certificates force exponent two in the
full original abelianization whenever the exact relative-head extension
bound saturates. The original lifts are arbitrary, and the original top
need not be elementary or split off from the pair kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

/-- Original top generators generate the retained top subtype as well. -/
theorem top_lift_tuple_full {J : Type} (u : J → U)
    (hgen : Subgroup.closure (Set.range fun j => F.top (u j)) = F.top.range) :
    Subgroup.closure (Set.range fun j => F.top.rangeRestrict (u j)) = ⊤ := by
  let S := Subgroup.closure (Set.range fun j => F.top.rangeRestrict (u j))
  have hs : Subgroup.closure (Set.range fun j => F.top (u j)) ≤
      S.map F.top.range.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨F.top.rangeRestrict (u j), Subgroup.subset_closure ⟨j, rfl⟩, rfl⟩
  apply top_unique
  intro t _
  have ht : (t : Equiv.Perm (Fin w)) ∈
      Subgroup.closure (Set.range fun j => F.top (u j)) := by
    rw [hgen]
    exact t.property
  obtain ⟨a, ha, he⟩ := hs ht
  exact (Subtype.ext he : a = t) ▸ ha

/-- The faithful physical pair kernel has exponent two. -/
theorem physical_kernel_pow_two (k : F.top.ker) : (k : U) ^ 2 = 1 := by
  have he : k ^ 2 = 1 := by
    apply F.bitsHom_injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    change F.bits k + F.bits k = 0
    funext i
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val he

/-- Squares placed in the actual relative radical become trivial in the
full original abelianization under saturation. -/
theorem abelianization_pow_two_of_radical_square_carries
    {J : Type} (u : J → U)
    (hgen : Subgroup.closure (Set.range fun j => F.top (u j)) = F.top.range)
    (hsquare : ∀ j, (F.top (u j)) ^ 2 = 1)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hR : ∀ k : F.top.ker, F.bits k ∈ R ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker)
    (hcarry : ∀ j, F.bits (F.carrySquare (u j) (hsquare j)) ∈ R) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  apply abelianization_pow_eq_one_of_actual_lift_carries 2 F.top.rangeRestrict u
    (F.top_lift_tuple_full u hgen)
  · intro k
    exact F.physical_kernel_pow_two ⟨k.val, by
      simpa only [MonoidHom.ker_rangeRestrict] using k.property⟩
  · intro j
    have hr := (hR _).mp (hcarry j)
    rw [hrad] at hr
    exact hr.2

/-- Saturation supplies both directions of the derived-kernel test. -/
theorem bits_mem_radical_of_derived
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hR : ∀ k : F.top.ker, F.bits k ∈ R ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R := by
  intro k hk
  apply (hR k).mpr
  rw [hrad]
  exact ⟨k.property, hk⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8))

theorem regular45_abelianization_pow_two
    (u : Fin 3 → U)
    (hp : ∀ i j, F.top (u i) j = BinaryRegularEightSquareCarry.generatorImages i j)
    (hgen : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K45)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (hR : ∀ k : F.top.ker, F.bits k ∈ BinaryRegularEightSquareCarry.R45 ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have he : (fun i => F.top (u i)) = BinaryMenuCayley8T3.generators := by
    funext i
    apply Equiv.ext
    intro j
    exact (hp i j).trans (BinaryRegularEightSquareCarry.generatorImages_eq_original i j)
  exact F.abelianization_pow_two_of_radical_square_carries u
    (by rw [he, ← hgen])
    (RegularEightCarries.lift_top_square F u hp) hrad _ hR
    (RegularEightCarries.square_carries45 F u hp hK
      (F.bits_mem_radical_of_derived hrad _ hR))

theorem regular46_abelianization_pow_two
    (u : Fin 3 → U)
    (hp : ∀ i j, F.top (u i) j = BinaryRegularEightSquareCarry.generatorImages i j)
    (hgen : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (hR : ∀ k : F.top.ker, F.bits k ∈ BinaryRegularEightSquareCarry.R46 ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have he : (fun i => F.top (u i)) = BinaryMenuCayley8T3.generators := by
    funext i
    apply Equiv.ext
    intro j
    exact (hp i j).trans (BinaryRegularEightSquareCarry.generatorImages_eq_original i j)
  exact F.abelianization_pow_two_of_radical_square_carries u
    (by rw [he, ← hgen])
    (RegularEightCarries.lift_top_square F u hp) hrad _ hR
    (RegularEightCarries.square_carries46 F u hp hK
      (F.bits_mem_radical_of_derived hrad _ hR))

theorem heisenberg12_abelianization_pow_two
    (u : Fin 4 → U)
    (hp : ∀ i, F.top (u i) = BinaryHeisenbergEightSquareCarry.originalSelected i)
    (hgen : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K12)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (hR : ∀ k : F.top.ker, F.bits k ∈ BinaryHeisenbergEightSquareCarry.R12 ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have he : (fun i => F.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected :=
    funext hp
  exact F.abelianization_pow_two_of_radical_square_carries u
    (by rw [he, BinaryHeisenbergEightSquareCarry.selected_closure_eq_original, ← hgen])
    (HeisenbergCarries.lift_top_square F u hp) hrad _ hR
    (HeisenbergCarries.square_carries12 F u hp hK
      (F.bits_mem_radical_of_derived hrad _ hR))

theorem heisenberg13_abelianization_pow_two
    (u : Fin 4 → U)
    (hp : ∀ i, F.top (u i) = BinaryHeisenbergEightSquareCarry.originalSelected i)
    (hgen : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K13)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (hR : ∀ k : F.top.ker, F.bits k ∈ BinaryHeisenbergEightSquareCarry.R13 ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have he : (fun i => F.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected :=
    funext hp
  exact F.abelianization_pow_two_of_radical_square_carries u
    (by rw [he, BinaryHeisenbergEightSquareCarry.selected_closure_eq_original, ← hgen])
    (HeisenbergCarries.lift_top_square F u hp) hrad _ hR
    (HeisenbergCarries.square_carries13 F u hp hK
      (F.bits_mem_radical_of_derived hrad _ hR))

theorem heisenberg14_abelianization_pow_two
    (u : Fin 4 → U)
    (hp : ∀ i, F.top (u i) = BinaryHeisenbergEightSquareCarry.originalSelected i)
    (hgen : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hrad : primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U)
    (hR : ∀ k : F.top.ker, F.bits k ∈ BinaryHeisenbergEightSquareCarry.R14 ↔
      (k : U) ∈ primeRelativeRadical 2 F.top.ker) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have he : (fun i => F.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected :=
    funext hp
  exact F.abelianization_pow_two_of_radical_square_carries u
    (by rw [he, BinaryHeisenbergEightSquareCarry.selected_closure_eq_original, ← hgen])
    (HeisenbergCarries.lift_top_square F u hp) hrad _ hR
    (HeisenbergCarries.square_carries14 F u hp hK
      (F.bits_mem_radical_of_derived hrad _ hR))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
