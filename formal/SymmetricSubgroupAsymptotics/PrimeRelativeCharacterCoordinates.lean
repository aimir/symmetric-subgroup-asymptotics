import SymmetricSubgroupAsymptotics.PrimeRelativeRadical

/-! Original-generator coordinates on the whole-ambient invariant
character space. Word relations are checked modulo the actual relative
radical. Exact dimension is used only for surjectivity of the resulting
coordinate map; no extendibility of these characters is asserted. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G ι : Type*} [Group G]
    (N : Subgroup G) [N.Normal]

theorem primeRelativeCharacter_eq_of_mul_inv_mem_radical
    (χ : primeRelativeCharacters p N) (x y : N)
    (h : ((x * y⁻¹ : N) : G) ∈ primeRelativeRadical p N) :
    χ.1 (Additive.ofMul x) = χ.1 (Additive.ofMul y) := by
  have hz := (mem_primeRelativeRadicalKernel_iff p N (x * y⁻¹)).mp
    ((coe_mem_primeRelativeRadical_iff p N _).mp h) χ
  change χ.1 (Additive.ofMul x + -Additive.ofMul y) = 0 at hz
  rw [map_add, map_neg] at hz
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)

theorem primeRelativeCharacter_word (χ : primeRelativeCharacters p N)
    (g : ι → N) (w : List ι) :
    χ.1 (Additive.ofMul ((w.map g).prod)) =
      (w.map (fun i => χ.1 (Additive.ofMul (g i)))).sum := by
  induction w with
  | nil => exact χ.1.map_zero
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    change χ.1 (Additive.ofMul (g i) + Additive.ofMul ((w.map g).prod)) = _
    rw [map_add, ih]

def primeRelativeCharacterCoordinates {r : ℕ} (g : ι → N) (select : Fin r → ι) :
    primeRelativeCharacters p N →ₗ[ZMod p] (Fin r → ZMod p) where
  toFun χ i := χ.1 (Additive.ofMul (g (select i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primeRelativeCharacter_generator_values {r : ℕ}
    (g : ι → N) (select : Fin r → ι) (words : ι → List (Fin r))
    (hwords : ∀ j, ((g j * (((words j).map (g ∘ select)).prod)⁻¹ : N) : G) ∈
      primeRelativeRadical p N)
    (χ : primeRelativeCharacters p N) (j : ι) :
    χ.1 (Additive.ofMul (g j)) =
      ((words j).map (primeRelativeCharacterCoordinates p N g select χ)).sum := by
  rw [primeRelativeCharacter_eq_of_mul_inv_mem_radical p N χ _ _ (hwords j),
    primeRelativeCharacter_word]
  rfl

theorem primeRelativeCharacterCoordinates_injective {r : ℕ}
    (g : ι → N) (hgen : Subgroup.closure (Set.range g) = ⊤)
    (select : Fin r → ι) (words : ι → List (Fin r))
    (hwords : ∀ j, ((g j * (((words j).map (g ∘ select)).prod)⁻¹ : N) : G) ∈
      primeRelativeRadical p N) :
    Function.Injective (primeRelativeCharacterCoordinates p N g select) := by
  intro χ ψ he
  apply Subtype.ext
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply MonoidHom.eq_of_eqOn_dense hgen
  rintro _ ⟨j, rfl⟩
  apply congrArg Multiplicative.ofAdd
  rw [primeRelativeCharacter_generator_values p N g select words hwords,
    primeRelativeCharacter_generator_values p N g select words hwords, he]

def primeRelativeCharacterCoordinateEquiv [Finite G] {r : ℕ}
    (g : ι → N) (hgen : Subgroup.closure (Set.range g) = ⊤)
    (select : Fin r → ι) (words : ι → List (Fin r))
    (hwords : ∀ j, ((g j * (((words j).map (g ∘ select)).prod)⁻¹ : N) : G) ∈
      primeRelativeRadical p N)
    (hdim : Module.finrank (ZMod p) (primeRelativeCharacters p N) = r) :
    primeRelativeCharacters p N ≃ₗ[ZMod p] (Fin r → ZMod p) :=
  LinearEquiv.ofBijective (primeRelativeCharacterCoordinates p N g select)
    ⟨primeRelativeCharacterCoordinates_injective p N g hgen select words hwords,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdim]; simp)).mp
        (primeRelativeCharacterCoordinates_injective p N g hgen select words hwords)⟩

end SymmetricSubgroupAsymptotics
