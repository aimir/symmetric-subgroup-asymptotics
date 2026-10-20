import SymmetricSubgroupAsymptotics.BinaryPairAffineChart
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite

/-! # The full three-pair wreath group as `S4 × C2`

Only the 48 elements of the full wreath group and its action on four
points occur in the finite checks. No subgroups are enumerated. The
four-point action comes from the even plane in the three-bit space;
the remaining central coordinate is the sum of the three bits.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.DegreeSixThreePairWreathChart

abbrev C2 := Multiplicative (ZMod 2)
abbrev Plane := ZMod 2 × ZMod 2
abbrev W := PermutationalWreathProduct C2 (Equiv.Perm (Fin 3)) (Fin 3)

instance : Fintype W :=
  Fintype.ofEquiv ((Fin 3 → C2) × Equiv.Perm (Fin 3))
    PermutationalWreathProduct.equivProd.symm

instance : DecidableEq W := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => PermutationalWreathProduct.ext h.1 h.2,
      fun h => ⟨congrArg PermutationalWreathProduct.left h,
        congrArg PermutationalWreathProduct.right h⟩⟩

def evenVector (v : Plane) : Fin 3 → ZMod 2 := ![v.1, v.2, v.1 + v.2]

def parity (w : W) : ZMod 2 :=
  (w.left 0).toAdd + (w.left 1).toAdd + (w.left 2).toAdd

def planeAction (w : W) (v : Plane) : Plane :=
  (evenVector v (w.right⁻¹ 0) + (w.left 0).toAdd + parity w,
   evenVector v (w.right⁻¹ 1) + (w.left 1).toAdd + parity w)

private theorem planeAction_bijective :
    ∀ w : W, Function.Bijective (planeAction w) := by decide +kernel

private theorem planeAction_one : ∀ v : Plane, planeAction 1 v = v := by
  decide +kernel

private theorem planeAction_mul : ∀ a b : W, ∀ v : Plane,
    planeAction (a * b) v = planeAction a (planeAction b v) := by
  decide +kernel

private theorem parity_one : parity 1 = 0 := by decide +kernel

private theorem parity_mul : ∀ a b : W, parity (a * b) = parity a + parity b := by
  decide +kernel

private theorem joint_kernel : ∀ w : W,
    (∀ v : Plane, planeAction w v = v) → parity w = 0 → w = 1 := by
  decide +kernel

def planeHom : W →* Equiv.Perm Plane where
  toFun w := Equiv.ofBijective (planeAction w) (planeAction_bijective w)
  map_one' := Equiv.ext planeAction_one
  map_mul' a b := Equiv.ext (planeAction_mul a b)

def parityHom : W →* C2 where
  toFun w := Multiplicative.ofAdd (parity w)
  map_one' := congrArg Multiplicative.ofAdd parity_one
  map_mul' a b := congrArg Multiplicative.ofAdd (parity_mul a b)

def jointHom : W →* Equiv.Perm Plane × C2 := planeHom.prod parityHom

theorem jointHom_injective : Function.Injective jointHom := by
  rw [injective_iff_map_eq_one]
  intro w hw
  apply joint_kernel w
  · intro v
    exact congrArg (fun g : Equiv.Perm Plane × C2 => g.1 v) hw
  · exact congrArg (fun g : Equiv.Perm Plane × C2 => g.2.toAdd) hw

theorem card_wreath : Nat.card W = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem card_product : Nat.card (Equiv.Perm Plane × C2) = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def fullEquiv : W ≃* Equiv.Perm (Fin 4) × C2 :=
  (MulEquiv.ofBijective jointHom
    ((Nat.bijective_iff_injective_and_card jointHom).2
      ⟨jointHom_injective, card_wreath.trans card_product.symm⟩)).trans
    (MulEquiv.prodCongr
      (Fintype.equivFinOfCardEq (show Fintype.card Plane = 4 by decide)).permCongrHom
      (MulEquiv.refl C2))

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 3))

/-- The original physical pair frame supplies its faithful full-wreath
coordinates. This retains its complete correlated flip kernel. -/
def pairEmbedding : U →* W where
  toFun u := ⟨fun i => Multiplicative.ofAdd (F.affineTranslation u i), F.top u⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact congrArg Multiplicative.ofAdd (congrFun F.affineTranslation_one i)
    · exact F.top.map_one
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · funext i
      have h := congrFun (F.affineTranslation_mul u v) i
      simpa only [PermutationalWreathProduct.mul_left, Pi.mul_apply,
        permutationFunctionRepresentation_apply, add_comm] using
        congrArg Multiplicative.ofAdd h
    · exact F.top.map_mul u v

theorem pairEmbedding_injective : Function.Injective (pairEmbedding F) := by
  intro u v huv
  apply F.affineCoordinates_injective
  apply Prod.ext
  · exact Subtype.ext (congrArg PermutationalWreathProduct.right huv)
  · exact congrArg (fun w : W => fun i => (w.left i).toAdd) huv

/-- An actual three-pair group embeds into `S4 × C2` without a finite
classification premise. -/
def productEmbedding : U →* Equiv.Perm (Fin 4) × C2 :=
  fullEquiv.toMonoidHom.comp (pairEmbedding F)

theorem productEmbedding_injective : Function.Injective (productEmbedding F) :=
  fullEquiv.injective.comp (pairEmbedding_injective F)

end SymmetricSubgroupAsymptotics.DegreeSixThreePairWreathChart

end
