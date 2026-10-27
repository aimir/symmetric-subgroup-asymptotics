import SymmetricSubgroupAsymptotics.MatrixModelSelectedPointPeriodTwo
import SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod

/-! A selected PRIME vector period for the positive original product AB
supplies a genuine element order divisor in the SAME matrix model.
Packed vector steps retain original coefficient bindings separately.
No full matrix order, inverse, finite group order or identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.MatrixModelSelectedProductPrimePeriod
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo

theorem packed_vector_step (p n bits : ℕ) (rows : Array String)
    (rowCode : ℕ → ℕ) (inputCode nextCode : ℕ)
    (hrow : ∀ i j : Fin n, rawDigit rows i.val j.val=packedDigit bits (rowCode i.val) j.val)
    (hcheck : ∀ i : Fin n, packedDot bits (rowCode i.val) inputCode n % p=
      packedDigit bits nextCode i.val % p) :
    CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j : Fin n => (packedDigit bits inputCode j.val : ZMod p))=
      fun i : Fin n => (packedDigit bits nextCode i.val : ZMod p) := by
  funext i
  change (∑ j : Fin n, (rawDigit rows i.val j.val : ZMod p)*
    (packedDigit bits inputCode j.val : ZMod p))=_
  calc
    _ = ∑ j : Fin n, (packedDigit bits (rowCode i.val) j.val : ZMod p)*
        (packedDigit bits inputCode j.val : ZMod p) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrow i j]
    _ = (packedDot bits (rowCode i.val) inputCode n : ZMod p) :=
      (cast_natDot p n (packedDigit bits (rowCode i.val)) (packedDigit bits inputCode)).symm
    _ = _ := (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hcheck i)

def productEnd (p n : ℕ) (a b : Array String) : Module.End (ZMod p) (Vector p n) :=
  (firstEnd p n a).comp (firstEnd p n b)

theorem exists_prime_dvd_orderOf (p n : ℕ) (a b : Array String)
    (r : ℕ) (hr : r.Prime) (v : Vector p n)
    (hreturn : (productEnd p n a b ^ r) v=v)
    (hmoved : productEnd p n a b v≠v)
    (hn : ¬IsMulCommutative (Model p n a b)) :
    ∃ g : Model p n a b, r ∣ orderOf g := by
  obtain ⟨x,hx,y,hy,hxa,hyb,_⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let xm : Model p n a b := ⟨x,Subgroup.subset_closure hx⟩
  let ym : Model p n a b := ⟨y,Subgroup.subset_closure hy⟩
  let g : Model p n a b := xm*ym
  have hraw : unitEnd p n a b g=productEnd p n a b := by
    apply LinearMap.ext
    intro w
    change ((x : Matrix (Fin n) (Fin n) (ZMod p))*
      (y : Matrix (Fin n) (Fin n) (ZMod p))) *ᵥ w=
        CFSG.Models.MatrixData.matrix p n a *ᵥ (CFSG.Models.MatrixData.matrix p n b *ᵥ w)
    rw [hxa,hyb]
    exact (Matrix.mulVec_mulVec w _ _).symm
  letI : MulAction (Model p n a b) (Vector p n) :=
    MulAction.compHom (Vector p n) (unitAction p n a b)
  have hpow (k : ℕ) : g^k • v=(productEnd p n a b ^ k) v := by
    change unitEnd p n a b (g^k) v=(productEnd p n a b ^ k) v
    rw [map_pow,hraw]
  have hd : MulAction.period g v ∣ r :=
    MulAction.pow_smul_eq_iff_period_dvd.mp ((hpow r).trans hreturn)
  have hone : g • v=productEnd p n a b v := by simpa only [pow_one] using hpow 1
  have hne : MulAction.period g v≠1 := by
    intro he
    exact hmoved (hone.symm.trans (MulAction.period_eq_one_iff.mp he))
  have he : MulAction.period g v=r := (Nat.dvd_prime hr).mp hd |>.resolve_left hne
  exact ⟨g,by simpa only [he] using MulAction.period_dvd_orderOf g v⟩

theorem prime_dvd_card (p n : ℕ) (a b : Array String)
    (r : ℕ) (hr : r.Prime) (v : Vector p n)
    (hreturn : (productEnd p n a b ^ r) v=v)
    (hmoved : productEnd p n a b v≠v)
    (hn : ¬IsMulCommutative (Model p n a b)) : r ∣ Nat.card (Model p n a b) := by
  obtain ⟨g,hg⟩ := exists_prime_dvd_orderOf p n a b r hr v hreturn hmoved hn
  exact hg.trans (orderOf_dvd_natCard g)

end SymmetricSubgroupAsymptotics.MatrixModelSelectedProductPrimePeriod
