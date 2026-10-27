import SymmetricSubgroupAsymptotics.MatrixModelSelectedPointPeriodTwo

/-! Row periods in the SAME literal matrix model. The contragredient
action on functions sends g•f to (w ↦ f(g⁻¹•w)). Thus g⁻¹ acts on the
functional r⬝w by the POSITIVE first matrix rᵥ*A. No inverse-coordinate
certificate, primality, full operator identity, finiteness or simplicity
premise is needed. Noncommutativity supplies the genuine generator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.MatrixModelSelectedRowPeriodTwo

abbrev Model (p n : ℕ) (a b : Array String) := CFSG.Models.MatrixData.Model p n a b
abbrev Vector (p n : ℕ) := Fin n → ZMod p

def inversePrecompAction (G X R : Type*) [Group G] [MulAction G X] :
    MulAction G (X → R) where
  smul g f x := f (g⁻¹ • x)
  one_smul f := by
    funext x
    change f ((1 : G)⁻¹ • x) = f x
    rw [inv_one,one_smul]
  mul_smul g h f := by
    funext x
    change f ((g*h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev,mul_smul]

def rowFunctional (p n : ℕ) (r : Vector p n) : Vector p n → ZMod p :=
  fun w => dotProduct r w

theorem rowFunctional_injective (p n : ℕ) : Function.Injective (rowFunctional p n) := by
  intro r s h
  funext i
  have hi := congrFun h (Pi.single i 1)
  simpa only [rowFunctional,dotProduct_single_one] using hi

theorem exists_two_dvd_orderOf (p n : ℕ) (a b : Array String) (v : Vector p n)
    (hreturn : (v ᵥ* CFSG.Models.MatrixData.matrix p n a) ᵥ*
      CFSG.Models.MatrixData.matrix p n a = v)
    (hmoved : v ᵥ* CFSG.Models.MatrixData.matrix p n a ≠ v)
    (hn : ¬IsMulCommutative (Model p n a b)) :
    ∃ g : Model p n a b, 2 ∣ orderOf g := by
  obtain ⟨x,hx,y,hy,hxa,hyb,_⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let g : Model p n a b := ⟨x,Subgroup.subset_closure hx⟩
  have hraw : MatrixModelSelectedPointPeriodTwo.unitEnd p n a b g =
      MatrixModelSelectedPointPeriodTwo.firstEnd p n a := by
    apply LinearMap.ext
    intro w
    change (x : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w =
      MatrixModelSelectedPointPeriodTwo.firstEnd p n a w
    rw [hxa]
    rfl
  letI : MulAction (Model p n a b) (Vector p n) :=
    MulAction.compHom (Vector p n) (MatrixModelSelectedPointPeriodTwo.unitAction p n a b)
  letI : MulAction (Model p n a b) (Vector p n → ZMod p) :=
    inversePrecompAction (Model p n a b) (Vector p n) (ZMod p)
  have hstep (r : Vector p n) :
      g⁻¹ • rowFunctional p n r =
        rowFunctional p n (r ᵥ* CFSG.Models.MatrixData.matrix p n a) := by
    funext w
    change dotProduct r (((g⁻¹)⁻¹ : Model p n a b) • w) = _
    rw [inv_inv]
    change dotProduct r (MatrixModelSelectedPointPeriodTwo.unitEnd p n a b g w) = _
    rw [hraw]
    change dotProduct r (CFSG.Models.MatrixData.matrix p n a *ᵥ w) = _
    exact Matrix.dotProduct_mulVec r (CFSG.Models.MatrixData.matrix p n a) w
  have htwo : (g⁻¹)^2 • rowFunctional p n v = rowFunctional p n v := by
    rw [pow_two,mul_smul,hstep,hstep,hreturn]
  have hne : g⁻¹ • rowFunctional p n v ≠ rowFunctional p n v := by
    intro h
    exact hmoved (rowFunctional_injective p n ((hstep v).symm.trans h))
  have hd : MulAction.period (g⁻¹) (rowFunctional p n v) ∣ 2 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp htwo
  have hperiod : MulAction.period (g⁻¹) (rowFunctional p n v) ≠ 1 := by
    intro h
    exact hne (MulAction.period_eq_one_iff.mp h)
  have he : MulAction.period (g⁻¹) (rowFunctional p n v) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hperiod
  exact ⟨g⁻¹,by simpa only [he] using
    MulAction.period_dvd_orderOf (g⁻¹) (rowFunctional p n v)⟩

theorem even_card_of_row_period_two (p n : ℕ) (a b : Array String) (v : Vector p n)
    (hreturn : (v ᵥ* CFSG.Models.MatrixData.matrix p n a) ᵥ*
      CFSG.Models.MatrixData.matrix p n a = v)
    (hmoved : v ᵥ* CFSG.Models.MatrixData.matrix p n a ≠ v)
    (hn : ¬IsMulCommutative (Model p n a b)) : Even (Nat.card (Model p n a b)) := by
  obtain ⟨g,hg⟩ := exists_two_dvd_orderOf p n a b v hreturn hmoved hn
  exact even_iff_two_dvd.mpr (hg.trans (orderOf_dvd_natCard g))

end SymmetricSubgroupAsymptotics.MatrixModelSelectedRowPeriodTwo
