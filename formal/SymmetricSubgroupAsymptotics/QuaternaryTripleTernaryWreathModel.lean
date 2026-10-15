import SymmetricSubgroupAsymptotics.QuaternaryTripleTernaryNormalGenerators

/-! The regular three-block `C4` wreath model is the literal image of the
fixed-coordinate plus augmentation-plane model. The coordinate change
uses `3 = 3⁻¹` modulo four; its conjugation formula is checked on the
displayed ternary matrices, without enumerating the wreath group. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace QuaternaryTripleTernaryWreathModel

open QuaternaryTernaryInvariantPlane QuaternaryTernaryCyclicSubmodules SemidirectProduct

abbrev Block := Multiplicative (ZMod 3)
abbrev Vector := Block → Scalar
abbrev Points := Block × Scalar

def linearAction : Block →* (Vector ≃ₗ[Scalar] Vector) where
  toFun c :=
    { toFun := fun v i => v (c⁻¹ * i)
      invFun := fun v i => v (c * i)
      left_inv := by intro v; funext i; simp
      right_inv := by intro v; funext i; simp
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  map_one' := by apply LinearEquiv.ext; intro v; funext i; simp
  map_mul' c d := by
    apply LinearEquiv.ext
    intro v
    funext i
    simp [mul_inv_rev, mul_assoc]

def rotation : Block →* MulAut (Multiplicative Vector) where
  toFun c := (linearAction c).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun linearAction.map_one v.toAdd)
  map_mul' c d := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun (linearAction.map_mul c d) v.toAdd)

abbrev Model := Multiplicative Vector ⋊[rotation] Block

instance : Finite Model := Finite.of_equiv _ SemidirectProduct.equivProd.symm

def encode (x : Coordinates) : Vector := fun i =>
  ![x.1 + x.2 0, x.1 + x.2 1, x.1 - x.2 0 - x.2 1]
    (⟨i.toAdd.val, i.toAdd.val_lt⟩ : Fin 3)

theorem block_cases (i : Block) : i = Multiplicative.ofAdd 0 ∨
    i = Multiplicative.ofAdd 1 ∨ i = Multiplicative.ofAdd 2 := by
  have h : ∀ i : Block, i = Multiplicative.ofAdd 0 ∨
      i = Multiplicative.ofAdd 1 ∨ i = Multiplicative.ofAdd 2 := by decide +kernel
  exact h i

@[simp] theorem encode_zero (x : Coordinates) :
    encode x (Multiplicative.ofAdd 0) = x.1 + x.2 0 := rfl

@[simp] theorem encode_identity (x : Coordinates) :
    encode x 1 = x.1 + x.2 0 := rfl

@[simp] theorem encode_one (x : Coordinates) :
    encode x (Multiplicative.ofAdd 1) = x.1 + x.2 1 := rfl

@[simp] theorem encode_two (x : Coordinates) :
    encode x (Multiplicative.ofAdd 2) = x.1 - x.2 0 - x.2 1 := rfl

def diagonal (v : Vector) : Scalar :=
  3 * (v (Multiplicative.ofAdd 0) + v (Multiplicative.ofAdd 1) + v (Multiplicative.ofAdd 2))

def decode (v : Vector) : Coordinates :=
  (diagonal v, ![v (Multiplicative.ofAdd 0) - diagonal v,
    v (Multiplicative.ofAdd 1) - diagonal v])

def coordinateChart : Coordinates ≃ₗ[Scalar] Vector where
  toFun := encode
  invFun := decode
  left_inv x := by
    apply Prod.ext
    · change 3 * ((x.1 + x.2 0) + (x.1 + x.2 1) + (x.1 - x.2 0 - x.2 1)) = x.1
      ring_nf;
        simp only [show (9 : Scalar) = 1 from by decide +kernel, mul_one]
    · ext i
      fin_cases i
      · change (x.1 + x.2 0) -
          3 * ((x.1 + x.2 0) + (x.1 + x.2 1) + (x.1 - x.2 0 - x.2 1)) = x.2 0
        ring_nf; simp only [show (8 : Scalar) = 0 from by decide +kernel,
          mul_zero, neg_zero, zero_add]
      · change (x.1 + x.2 1) -
          3 * ((x.1 + x.2 0) + (x.1 + x.2 1) + (x.1 - x.2 0 - x.2 1)) = x.2 1
        ring_nf; simp only [show (8 : Scalar) = 0 from by decide +kernel,
          mul_zero, neg_zero, zero_add]
  right_inv v := by
    funext i
    rcases block_cases i with rfl | rfl | rfl
    · change diagonal v + (v (Multiplicative.ofAdd 0) - diagonal v) = v (Multiplicative.ofAdd 0)
      ring
    · change diagonal v + (v (Multiplicative.ofAdd 1) - diagonal v) = v (Multiplicative.ofAdd 1)
      ring
    · change diagonal v - (v (Multiplicative.ofAdd 0) - diagonal v) -
        (v (Multiplicative.ofAdd 1) - diagonal v) = v (Multiplicative.ofAdd 2)
      dsimp only [diagonal]
      ring_nf; simp only [show (8 : Scalar) = 0 from by decide +kernel,
        show (9 : Scalar) = 1 from by decide +kernel,
        mul_zero, mul_one, add_zero, zero_add]
  map_add' x y := by
    funext i
    rcases block_cases i with rfl | rfl | rfl
    · change (x.1 + y.1) + (x.2 0 + y.2 0) = (x.1 + x.2 0) + (y.1 + y.2 0)
      ring
    · change (x.1 + y.1) + (x.2 1 + y.2 1) = (x.1 + x.2 1) + (y.1 + y.2 1)
      ring
    · change (x.1 + y.1) - (x.2 0 + y.2 0) - (x.2 1 + y.2 1) =
        (x.1 - x.2 0 - x.2 1) + (y.1 - y.2 0 - y.2 1)
      ring
  map_smul' a x := by
    funext i
    rcases block_cases i with rfl | rfl | rfl
    · change a * x.1 + a * x.2 0 = a * (x.1 + x.2 0)
      ring
    · change a * x.1 + a * x.2 1 = a * (x.1 + x.2 1)
      ring
    · change a * x.1 - a * x.2 0 - a * x.2 1 = a * (x.1 - x.2 0 - x.2 1)
      ring

theorem encode_action (d : Scalar) (x : Plane) (z : Block) :
    encode (d, (QuaternaryTernaryNormalChain.action z (Multiplicative.ofAdd x)).toAdd) =
      linearAction z (encode (d, x)) := by
  funext i
  change encode (d, (QuaternaryTernaryNormalChain.action z (Multiplicative.ofAdd x)).toAdd) i =
    encode (d, x) (z⁻¹ * i)
  rcases block_cases z with rfl | rfl | rfl
  · change encode (d, (QuaternaryTernaryNormalChain.action 1 (Multiplicative.ofAdd x)).toAdd) i =
      encode (d, x) (1⁻¹ * i)
    simp
  · rw [QuaternaryTernaryNormalChain.action_generator]
    rcases block_cases i with rfl | rfl | rfl
    · change d + (-x 0 - x 1) = d - x 0 - x 1
      ring
    · change d + x 0 = d + x 0
      rfl
    · change d - (-x 0 - x 1) - x 0 = d + x 1
      ring
  · have htwo : (QuaternaryTernaryNormalChain.action (Multiplicative.ofAdd 2)
        (Multiplicative.ofAdd x)).toAdd = cycle (cycle x) := by
      change (QuaternaryTernaryNormalChain.action
        (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1) (Multiplicative.ofAdd x)).toAdd = _
      rw [map_mul]
      change (QuaternaryTernaryNormalChain.action (Multiplicative.ofAdd 1)
        (QuaternaryTernaryNormalChain.action (Multiplicative.ofAdd 1)
          (Multiplicative.ofAdd x))).toAdd = _
      rw [QuaternaryTernaryNormalChain.action_generator,
        QuaternaryTernaryNormalChain.action_generator]
      rfl
    rw [htwo]
    rcases block_cases i with rfl | rfl | rfl
    · change d + (-(-x 0 - x 1) - x 0) = d + x 1
      ring
    · change d + (-x 0 - x 1) = d - x 0 - x 1
      ring
    · change d - (-(-x 0 - x 1) - x 0) - (-x 0 - x 1) = d + x 0
      ring

def sourceMap : QuaternaryTripleTernaryNormalGenerators.Model →* Model where
  toFun g := ⟨Multiplicative.ofAdd (encode (g.1.toAdd, g.2.left.toAdd)), g.2.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      exact coordinateChart.map_zero
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change encode (g.1.toAdd + h.1.toAdd,
          g.2.left.toAdd +
            (QuaternaryTernaryNormalChain.action g.2.right h.2.left).toAdd) =
        encode (g.1.toAdd, g.2.left.toAdd) +
          linearAction g.2.right (encode (h.1.toAdd, h.2.left.toAdd))
      calc
        _ = encode (g.1.toAdd, g.2.left.toAdd) +
            encode (h.1.toAdd,
              (QuaternaryTernaryNormalChain.action g.2.right h.2.left).toAdd) :=
          coordinateChart.map_add _ _
        _ = _ := congrArg (encode (g.1.toAdd, g.2.left.toAdd) + ·)
          (encode_action h.1.toAdd h.2.left.toAdd g.2.right)
    · rfl

theorem sourceMap_surjective : Function.Surjective sourceMap := by
  intro g
  let x := coordinateChart.symm g.left.toAdd
  refine ⟨(Multiplicative.ofAdd x.1, ⟨Multiplicative.ofAdd x.2, g.right⟩), ?_⟩
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact coordinateChart.apply_symm_apply g.left.toAdd
  · rfl

theorem socle_of_surjective {Q : Type} [Group Q] (pi : Model →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  QuaternaryTripleTernaryNormalGenerators.socle_of_surjective
    (pi.comp sourceMap) (hpi.comp sourceMap_surjective)

def translations : Multiplicative Vector →* Equiv.Perm Points where
  toFun v :=
    { toFun := fun p => (p.1, v.toAdd p.1 + p.2)
      invFun := fun p => (p.1, -v.toAdd p.1 + p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' v w := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · rfl
    · exact add_assoc _ _ _

def blockShifts : Block →* Equiv.Perm Points where
  toFun c :=
    { toFun := fun p => (c * p.1, p.2)
      invFun := fun p => (c⁻¹ * p.1, p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' c d := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact mul_assoc c d p.1
    · rfl

def modelAction : Model →* Equiv.Perm Points :=
  SemidirectProduct.lift translations blockShifts (by
    intro c
    apply MonoidHom.ext
    intro v
    apply Equiv.ext
    intro p
    apply Prod.ext <;>
      simp [translations, blockShifts, rotation, linearAction, mul_assoc])

def modelGenerators : Fin 2 → Model :=
  ![inl (Multiplicative.ofAdd (Pi.single (1 : Block) (1 : Scalar))),
    inr (Multiplicative.ofAdd 1)]

private abbrev Generated : Subgroup Model := Subgroup.closure (Set.range modelGenerators)

private theorem inr_mem_generated (c : Block) : (inr c : Model) ∈ Generated := by
  have hc : (Multiplicative.ofAdd (1 : ZMod 3)) ^ c.toAdd.val = c := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul]
  rw [← hc, map_pow]
  exact Generated.pow_mem (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 2))) _

private theorem inl_single_mem_generated (c : Block) :
    (inl (Multiplicative.ofAdd (Pi.single c (1 : Scalar))) : Model) ∈ Generated := by
  have hconj := Generated.mul_mem
    (Generated.mul_mem (inr_mem_generated c)
      (Subgroup.subset_closure (Set.mem_range_self (0 : Fin 2))))
    (Generated.inv_mem (inr_mem_generated c))
  have hid : (inr c : Model) * inl (Multiplicative.ofAdd (Pi.single (1 : Block) (1 : Scalar))) *
      (inr c)⁻¹ = inl (Multiplicative.ofAdd (Pi.single c (1 : Scalar))) := by
    rw [← map_inv, ← inl_aut]
    congr 1
    apply Multiplicative.toAdd.injective
    funext i
    change (Pi.single (1 : Block) (1 : Scalar) : Vector) (c⁻¹ * i) =
      (Pi.single c (1 : Scalar) : Vector) i
    by_cases hi : i = c
    · subst i
      have h1 : (Pi.single (1 : Block) (1 : Scalar) : Vector) (1 : Block) = 1 :=
        Pi.single_eq_same _ _
      have h2 : (Pi.single c (1 : Scalar) : Vector) c = 1 := Pi.single_eq_same _ _
      exact (congrArg (fun z : Block ↦ (Pi.single (1 : Block) (1 : Scalar) : Vector) z)
        (inv_mul_cancel c)).trans (h1.trans h2.symm)
    · have hh : c⁻¹ * i ≠ 1 := by
        intro h
        apply hi
        calc
          i = c * (c⁻¹ * i) := by simp
          _ = c := by rw [h, mul_one]
      simp only [Pi.single_eq_of_ne hh, Pi.single_eq_of_ne hi]
  exact hid ▸ hconj

private theorem vector_word (v : Vector) :
    Multiplicative.ofAdd v =
      Multiplicative.ofAdd (Pi.single (Multiplicative.ofAdd 0 : Block) (1 : Scalar)) ^
        (v (Multiplicative.ofAdd 0)).val *
      Multiplicative.ofAdd (Pi.single (Multiplicative.ofAdd 1 : Block) (1 : Scalar)) ^
        (v (Multiplicative.ofAdd 1)).val *
      Multiplicative.ofAdd (Pi.single (Multiplicative.ofAdd 2 : Block) (1 : Scalar)) ^
        (v (Multiplicative.ofAdd 2)).val := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, Pi.add_apply, Pi.smul_apply]
  have h01 : (Multiplicative.ofAdd 0 : Block) ≠ Multiplicative.ofAdd 1 := by decide +kernel
  have h02 : (Multiplicative.ofAdd 0 : Block) ≠ Multiplicative.ofAdd 2 := by decide +kernel
  have h12 : (Multiplicative.ofAdd 1 : Block) ≠ Multiplicative.ofAdd 2 := by decide +kernel
  rcases block_cases i with rfl | rfl | rfl <;>
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne h01, Pi.single_eq_of_ne h01.symm,
      Pi.single_eq_of_ne h02, Pi.single_eq_of_ne h02.symm,
      Pi.single_eq_of_ne h12, Pi.single_eq_of_ne h12.symm,
      nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one, mul_zero, add_zero, zero_add]

private theorem inl_mem_generated (v : Multiplicative Vector) : (inl v : Model) ∈ Generated := by
  have hv := vector_word v.toAdd
  rw [ofAdd_toAdd] at hv
  rw [hv, map_mul, map_mul, map_pow, map_pow, map_pow]
  exact Generated.mul_mem
    (Generated.mul_mem (Generated.pow_mem (inl_single_mem_generated _) _)
      (Generated.pow_mem (inl_single_mem_generated _) _))
    (Generated.pow_mem (inl_single_mem_generated _) _)

theorem model_generated : Subgroup.closure (Set.range modelGenerators) = ⊤ := by
  apply top_unique
  intro g _
  rw [← inl_left_mul_inr_right g]
  exact Generated.mul_mem (inl_mem_generated _) (inr_mem_generated _)

end QuaternaryTripleTernaryWreathModel
end SymmetricSubgroupAsymptotics

end
