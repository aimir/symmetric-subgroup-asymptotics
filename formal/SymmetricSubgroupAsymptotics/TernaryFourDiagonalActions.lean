import SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction
import SymmetricSubgroupAsymptotics.TernaryFourScalarDiagonalQuotient

/-! A common diagonal ternary line with an actual block/scalar action.
The sign-twisted model keeps its semidirect multiplication. Trivial scalar
actions and independent global signs receive explicit surjective maps
from H times C3 and H times D3 respectively. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourDiagonalActions

open SemidirectProduct

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev D3 := DihedralGroup 3

variable {R : Type} [Group R]

def scalarLinear (s : R →* (ZMod 3)ˣ) : R →* ((ZMod 3) ≃ₗ[ZMod 3] (ZMod 3)) where
  toFun r := LinearEquiv.smulOfUnit (s r)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (s 1 : ZMod 3)*v = v
    rw [map_one,Units.val_one,one_mul]
  map_mul' r t := by
    apply LinearEquiv.ext
    intro v
    change (s (r*t) : ZMod 3)*v = (s r : ZMod 3)*((s t : ZMod 3)*v)
    rw [s.map_mul,Units.val_mul,mul_assoc]

abbrev Model (s : R →* (ZMod 3)ˣ) :=
  LinearSemidirectCoprimeSocleBounds.Model (scalarLinear s)

def constantLinear : ZMod 3 →ₗ[ZMod 3] (Fin 4 → ZMod 3) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toFull (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ) :
    Model s →* TernaryFourScalarFullProjection.Model b s :=
  SemidirectProduct.map constantLinear.toAddMonoidHom.toMultiplicative (MonoidHom.id R) (by
    intro r
    apply MonoidHom.ext
    intro a
    rfl)

def action (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ) :
    Model s →* Equiv.Perm (Fin 12) :=
  (TernaryFourScalarFullAction.action b s).comp (toFull b s)

theorem action_inl (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ) (z : C3) :
    action b s (inl z) = TernaryFourFullModuleCoordinates.diagonalPerm z := by
  change TernaryFourScalarFullAction.action b s
    (inl (constantLinear.toAddMonoidHom.toMultiplicative z)) = _
  rw [TernaryFourScalarFullAction.action_inl]
  exact (TernaryFourFullModuleCoordinates.diagonal_translation z).symm

theorem action_inr (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ) (r : R) :
    action b s (inr r) = TernaryFourScalarAugmentation.blockPerm b s r := by
  change TernaryFourScalarFullAction.action b s (inr r) = _
  exact TernaryFourScalarFullAction.action_inr b s r

def kernelValue (s : R →* (ZMod 3)ˣ) : (rightHom : Model s →* R).ker →* C3 where
  toFun g := g.1.left
  map_one' := rfl
  map_mul' g h := by
    have hg : g.1.right = 1 := MonoidHom.mem_ker.mp g.2
    apply Multiplicative.toAdd.injective
    change g.1.left.toAdd + scalarLinear s g.1.right h.1.left.toAdd =
      g.1.left.toAdd + h.1.left.toAdd
    rw [hg,map_one]
    rfl

theorem kernelValue_injective (s : R →* (ZMod 3)ˣ) :
    Function.Injective (kernelValue s) := by
  intro g h he
  apply Subtype.ext
  apply SemidirectProduct.ext he
  exact (MonoidHom.mem_ker.mp g.2).trans (MonoidHom.mem_ker.mp h.2).symm

instance rightKernel_isCyclic (s : R →* (ZMod 3)ˣ) :
    IsCyclic (rightHom : Model s →* R).ker :=
  isCyclic_of_injective (kernelValue s) (kernelValue_injective s)

theorem socle_two_of_normal_total [Finite R] (s : R →* (ZMod 3)ˣ)
    (hchain : ∀ A B : Subgroup R, A.Normal → B.Normal → A ≤ B ∨ B ≤ A)
    {X : Type} [Group X] (rho : Model s →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 2 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective rho hrho)
    (quotientSocle_two_of_cyclic_kernel_normal_total
      (rightHom : Model s →* R) rightHom_surjective hchain rho.ker)

def productToModel : R × C3 →* Model (1 : R →* (ZMod 3)ˣ) where
  toFun g := ⟨g.2,g.1⟩
  map_one' := rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change g.2.toAdd + h.2.toAdd = g.2.toAdd + (1 : ZMod 3)*h.2.toAdd
      rw [one_mul]
    · rfl

theorem productToModel_surjective : Function.Surjective (productToModel (R := R)) :=
  fun g => ⟨(g.right,g.left),rfl⟩

def dihedralToModel : D3 →* Model TernaryFourScalarDiagonalQuotient.bitScalar where
  toFun
    | .r a => ⟨Multiplicative.ofAdd a,1⟩
    | .sr a => ⟨Multiplicative.ofAdd (-a),Multiplicative.ofAdd 1⟩
  map_one' := rfl
  map_mul' := by decide +kernel

theorem dihedralToModel_surjective : Function.Surjective dihedralToModel := by
  intro g
  have hr : g.right = 1 ∨ g.right = Multiplicative.ofAdd 1 :=
    (show ∀ z : C2, z = 1 ∨ z = Multiplicative.ofAdd 1 by decide +kernel) g.right
  rcases hr with hr | hr
  · exact ⟨DihedralGroup.r g.left.toAdd,SemidirectProduct.ext rfl hr.symm⟩
  · refine ⟨DihedralGroup.sr (-g.left.toAdd),?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      exact neg_neg g.left.toAdd
    · exact hr.symm

def productDihedralToModel : R × D3 →*
    Model (TernaryFourScalarDiagonalQuotient.scalars (H := R)) where
  toFun g := ⟨(dihedralToModel g.2).left,(g.1,(dihedralToModel g.2).right)⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact congrArg
        (fun z : Model TernaryFourScalarDiagonalQuotient.bitScalar => z.left)
        dihedralToModel.map_one
    · exact Prod.ext rfl (congrArg
        (fun z : Model TernaryFourScalarDiagonalQuotient.bitScalar => z.right)
        dihedralToModel.map_one)
  map_mul' g h := by
    apply SemidirectProduct.ext
    · exact congrArg
        (fun z : Model TernaryFourScalarDiagonalQuotient.bitScalar => z.left)
        (dihedralToModel.map_mul g.2 h.2)
    · exact Prod.ext rfl (congrArg
        (fun z : Model TernaryFourScalarDiagonalQuotient.bitScalar => z.right)
        (dihedralToModel.map_mul g.2 h.2))

theorem productDihedralToModel_surjective :
    Function.Surjective (productDihedralToModel (R := R)) := by
  intro g
  obtain ⟨d,hd⟩ := dihedralToModel_surjective ⟨g.left,g.right.2⟩
  refine ⟨(g.right.1,d),?_⟩
  apply SemidirectProduct.ext
  · exact congrArg
      (fun z : Model TernaryFourScalarDiagonalQuotient.bitScalar => z.left) hd
  · exact Prod.ext rfl (congrArg
      (fun z : Model TernaryFourScalarDiagonalQuotient.bitScalar => z.right) hd)

theorem diagonal_mem_of_one (T : Subgroup (Equiv.Perm (Fin 12)))
    (h : TernaryFourFullModuleCoordinates.diagonalPerm (Multiplicative.ofAdd 1) ∈ T)
    (z : C3) : TernaryFourFullModuleCoordinates.diagonalPerm z ∈ T := by
  have hz : z = 1 ∨ z = Multiplicative.ofAdd 1 ∨ z = (Multiplicative.ofAdd 1)^2 :=
    (show ∀ z : C3, z = 1 ∨ z = Multiplicative.ofAdd 1 ∨
      z = (Multiplicative.ofAdd 1)^2 by decide +kernel) z
  rcases hz with rfl | rfl | rfl
  · rw [map_one]
    exact T.one_mem
  · exact h
  · rw [map_pow]
    exact T.pow_mem h 2

theorem action_range_le (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ)
    (T : Subgroup (Equiv.Perm (Fin 12)))
    (ht : TernaryFourFullModuleCoordinates.diagonalPerm (Multiplicative.ofAdd 1) ∈ T)
    (hb : ∀ r, TernaryFourScalarAugmentation.blockPerm b s r ∈ T) :
    (action b s).range ≤ T := by
  rintro _ ⟨g,rfl⟩
  rw [← inl_left_mul_inr_right g,map_mul,action_inl,action_inr]
  exact T.mul_mem (diagonal_mem_of_one T ht g.left) (hb g.right)

theorem hom_mem_of_pair (f : R →* Equiv.Perm (Fin 12))
    (T : Subgroup (Equiv.Perm (Fin 12))) (x y : R)
    (hgen : Subgroup.closure ({x,y} : Set R) = ⊤)
    (hx : f x ∈ T) (hy : f y ∈ T) (r : R) : f r ∈ T := by
  have hr : r ∈ Subgroup.closure ({x,y} : Set R) := by
    rw [hgen]
    exact Subgroup.mem_top _
  induction hr using Subgroup.closure_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  | one => simpa only [map_one] using T.one_mem
  | mul u v _ _ hu hv => simpa only [map_mul] using T.mul_mem hu hv
  | inv u _ hu => simpa only [map_inv] using T.inv_mem hu

theorem literal_range (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ)
    {n : ℕ} (generators : Fin n → Equiv.Perm (Fin 12)) (lifts : Fin n → Model s)
    (hbind : ∀ i, action b s (lifts i) = generators i)
    (ht : TernaryFourFullModuleCoordinates.diagonalPerm (Multiplicative.ofAdd 1) ∈
      Subgroup.closure (Set.range generators))
    (hb : ∀ r, TernaryFourScalarAugmentation.blockPerm b s r ∈
      Subgroup.closure (Set.range generators)) :
    (action b s).range = Subgroup.closure (Set.range generators) := by
  apply le_antisymm (action_range_le b s _ ht hb)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨lifts i,hbind i⟩

end SymmetricSubgroupAsymptotics.TernaryFourDiagonalActions

end
