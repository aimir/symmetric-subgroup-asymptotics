import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource

/-!
# The full two-pair preserving group is dihedral

For any chart `Fin 2 × ZMod 2 ≃ X`, the full subgroup of permutations of
`X` preserving the two displayed pairs is the order-eight wreath product
`C₂ ≀ C₂`.  The construction below is chart-natural: the literal dihedral
action is relabelled through the supplied chart, and a coordinate signature
bounds the full pair-preserving group by eight.  Injectivity of the dihedral
action therefore upgrades to an isomorphism.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev D8 := DegreeSixS3Wreath.D8

/-- The regular action of one binary coordinate on its two points. -/
def binaryBitAction : C2 →* Equiv.Perm (ZMod 2) :=
  Multiplicative.toAdd.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom C2 C2)

theorem binaryBitAction_injective : Function.Injective binaryBitAction :=
  Multiplicative.toAdd.permCongrHom.injective.comp MulAction.toPerm_injective

/-- Identify two copies of the binary point with two displayed pairs. -/
def twoBlockPairEquiv : (ZMod 2 ⊕ ZMod 2) ≃ (Fin 2 × ZMod 2) where
  toFun
    | Sum.inl z => (0, z)
    | Sum.inr z => (1, z)
  invFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  left_inv x := by
    rcases x with z | z <;> simp
  right_inv x := by
    rcases x with ⟨i, z⟩
    fin_cases i <;> simp

@[simp] theorem twoBlockPairEquiv_inl (z : ZMod 2) :
    twoBlockPairEquiv (Sum.inl z) = ((0 : Fin 2), z) := rfl

@[simp] theorem twoBlockPairEquiv_inr (z : ZMod 2) :
    twoBlockPairEquiv (Sum.inr z) = ((1 : Fin 2), z) := rfl

/-- The block swap on the two pair labels. -/
def binaryBlockAction : C2 →* Equiv.Perm (Fin 2) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp
    (C2Wreath.blockSwap (Fin 1))

/-- The standard faithful `D₈` action on two binary pairs. -/
def d8PairAction : D8 →* Equiv.Perm (Fin 2 × ZMod 2) :=
  twoBlockPairEquiv.permCongrHom.toMonoidHom.comp
    (C2Wreath.action binaryBitAction)

theorem d8PairAction_injective : Function.Injective d8PairAction :=
  twoBlockPairEquiv.permCongrHom.injective.comp
    (C2Wreath.action_injective binaryBitAction binaryBitAction_injective)

/-- The standard dihedral action preserves the two displayed pairs, and
its induced action on the pair labels is the block-swap coordinate. -/
theorem d8PairAction_preserves (g : D8) :
    Preserves (Equiv.refl (Fin 2 × ZMod 2)) (d8PairAction g)
      (binaryBlockAction g.right) := by
  intro x
  rcases x with ⟨i, z⟩
  change
    (twoBlockPairEquiv
      (C2Wreath.action binaryBitAction g
        (twoBlockPairEquiv.symm (i, z)))).1 =
      binaryBlockAction g.right i
  rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul,
    C2Wreath.action_inl]
  rcases C2Wreath.cases g.right with h | h
  · rw [h]
    fin_cases i <;>
      simp [binaryBlockAction, twoBlockPairEquiv, C2Wreath.blockSwap]
  · rw [h, C2Wreath.action_inr_gen]
    fin_cases i <;>
      simp [binaryBlockAction, twoBlockPairEquiv,
        C2Wreath.blockSwap, C2Wreath.gen_ne_one]

/-- Relabel the standard dihedral pair action through an arbitrary pair
chart. -/
def d8PairActionOnFrame {X : Type*}
    (frame : Fin 2 × ZMod 2 ≃ X) : D8 →* Equiv.Perm X :=
  frame.permCongrHom.toMonoidHom.comp d8PairAction

theorem d8PairActionOnFrame_preserves {X : Type*}
    (frame : Fin 2 × ZMod 2 ≃ X) (g : D8) :
    Preserves frame (d8PairActionOnFrame frame g)
      (binaryBlockAction g.right) := by
  intro x
  simpa only [d8PairActionOnFrame, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, Equiv.permCongr_apply,
    frame.symm_apply_apply, frame.apply_symm_apply] using
      d8PairAction_preserves g x

/-- The standard dihedral action, codomain-restricted to the full group
preserving the supplied pair chart. -/
def d8ToPairPreserving {X : Type*}
    (frame : Fin 2 × ZMod 2 ≃ X) :
    D8 →* pairPreserving frame where
  toFun g := ⟨d8PairActionOnFrame frame g,
    ⟨binaryBlockAction g.right, d8PairActionOnFrame_preserves frame g⟩⟩
  map_one' := Subtype.ext (map_one (d8PairActionOnFrame frame))
  map_mul' g h := Subtype.ext (map_mul (d8PairActionOnFrame frame) g h)

theorem d8ToPairPreserving_injective {X : Type*}
    (frame : Fin 2 × ZMod 2 ≃ X) :
    Function.Injective (d8ToPairPreserving frame) := by
  intro g h he
  apply d8PairAction_injective
  apply frame.permCongrHom.injective
  exact congrArg (fun u : pairPreserving frame => (u.1 : Equiv.Perm X)) he

/-- Coordinates determining a pair-preserving permutation: its action on
the two pair labels and the image of the zero point in each pair. -/
def pairPreservingSignature {X : Type*}
    (frame : Fin 2 × ZMod 2 ≃ X) :
    pairPreserving frame →
      Equiv.Perm (Fin 2) × (Fin 2 → ZMod 2) :=
  fun u => (pairTop frame u,
    fun i => (frame.symm ((u.1 : Equiv.Perm X) (frame (i, 0)))).2)

private theorem binary_other_unique (a b c : ZMod 2)
    (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

theorem pairPreservingSignature_injective {X : Type*}
    (frame : Fin 2 × ZMod 2 ≃ X) :
    Function.Injective (pairPreservingSignature frame) := by
  intro u v huv
  have htop : pairTop frame u = pairTop frame v :=
    congrArg Prod.fst huv
  have hzero :
      (fun i => (frame.symm ((u.1 : Equiv.Perm X) (frame (i, 0)))).2) =
        fun i => (frame.symm ((v.1 : Equiv.Perm X) (frame (i, 0)))).2 :=
    congrArg Prod.snd huv
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨i, z⟩
  apply frame.symm.injective
  have huFirst (b : ZMod 2) :
      (frame.symm ((u.1 : Equiv.Perm X) (frame (i, b)))).1 =
        pairTop frame u i :=
    pairTop_spec frame u (i, b)
  have hvFirst (b : ZMod 2) :
      (frame.symm ((v.1 : Equiv.Perm X) (frame (i, b)))).1 =
        pairTop frame v i :=
    pairTop_spec frame v (i, b)
  apply Prod.ext
  · exact (huFirst z).trans
      ((congrArg (fun p : Equiv.Perm (Fin 2) => p i) htop).trans
        (hvFirst z).symm)
  · rcases (show z = 0 ∨ z = 1 by decide) with rfl | rfl
    · exact DFunLike.congr_fun hzero i
    · have huNe :
          (frame.symm ((u.1 : Equiv.Perm X) (frame (i, 1)))).2 ≠
            (frame.symm ((u.1 : Equiv.Perm X) (frame (i, 0)))).2 := by
        intro he
        have hout :
            (u.1 : Equiv.Perm X) (frame (i, 1)) =
              (u.1 : Equiv.Perm X) (frame (i, 0)) := by
          apply frame.symm.injective
          exact Prod.ext ((huFirst 1).trans (huFirst 0).symm) he
        have hin := (u.1 : Equiv.Perm X).injective hout
        have hpair := frame.injective hin
        exact one_ne_zero (congrArg Prod.snd hpair)
      have hvNe :
          (frame.symm ((v.1 : Equiv.Perm X) (frame (i, 1)))).2 ≠
            (frame.symm ((v.1 : Equiv.Perm X) (frame (i, 0)))).2 := by
        intro he
        have hout :
            (v.1 : Equiv.Perm X) (frame (i, 1)) =
              (v.1 : Equiv.Perm X) (frame (i, 0)) := by
          apply frame.symm.injective
          exact Prod.ext ((hvFirst 1).trans (hvFirst 0).symm) he
        have hin := (v.1 : Equiv.Perm X).injective hout
        have hpair := frame.injective hin
        exact one_ne_zero (congrArg Prod.snd hpair)
      exact binary_other_unique _ _ _ huNe
        (by rwa [← DFunLike.congr_fun hzero i] at hvNe)

/-- There are at most eight permutations preserving two displayed pairs. -/
theorem pairPreserving_card_le_eight {X : Type*} [Finite X]
    (frame : Fin 2 × ZMod 2 ≃ X) :
    Nat.card (pairPreserving frame) ≤ 8 := by
  calc
    Nat.card (pairPreserving frame) ≤
        Nat.card (Equiv.Perm (Fin 2) × (Fin 2 → ZMod 2)) :=
      Nat.card_le_card_of_injective (pairPreservingSignature frame)
        (pairPreservingSignature_injective frame)
    _ = 8 := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_fun, Nat.card_fin,
        Nat.card_fin, Nat.card_zmod]
      norm_num

theorem d8ToPairPreserving_surjective {X : Type*} [Finite X]
    (frame : Fin 2 × ZMod 2 ≃ X) :
    Function.Surjective (d8ToPairPreserving frame) := by
  have hD8 : Nat.card D8 = 8 := by
    rw [SemidirectProduct.card, Nat.card_prod]
    norm_num [D8, C2, Nat.card_zmod]
  have hcard : Nat.card (pairPreserving frame) ≤ Nat.card D8 := by
    rw [hD8]
    exact pairPreserving_card_le_eight frame
  exact (d8ToPairPreserving_injective frame).bijective_of_nat_card_le hcard |>.2

/-- The full group preserving any two-pair chart is the literal `D₈`. -/
noncomputable def pairPreservingEquivD8 {X : Type*} [Finite X]
    (frame : Fin 2 × ZMod 2 ≃ X) :
    pairPreserving frame ≃* D8 :=
  (MulEquiv.ofBijective (d8ToPairPreserving frame)
    ⟨d8ToPairPreserving_injective frame,
      d8ToPairPreserving_surjective frame⟩).symm

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
