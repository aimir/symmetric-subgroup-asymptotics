import SymmetricSubgroupAsymptotics.MatrixModelSelectedProductPrimePeriod

/-! Selected prime periods for ANY fixed positive two-matrix word.
Letters true/false denote the original A/B fibres. The word remains a
literal list; no whole operator order or model identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
open MatrixModelSelectedPointPeriodTwo
open scoped Matrix

def letterEnd (p n : ℕ) (a b : Array String) (letter : Bool) : Module.End (ZMod p) (Vector p n) :=
  if letter then firstEnd p n a else firstEnd p n b

def wordEnd (p n : ℕ) (a b : Array String) (word : List Bool) : Module.End (ZMod p) (Vector p n) :=
  (word.map (letterEnd p n a b)).prod

theorem exists_prime_dvd_orderOf (p n : ℕ) (a b : Array String)
    (word : List Bool) (r : ℕ) (hr : r.Prime) (v : Vector p n)
    (hreturn : (wordEnd p n a b word ^ r) v=v)
    (hmoved : wordEnd p n a b word v≠v)
    (hn : ¬IsMulCommutative (Model p n a b)) :
    ∃ g : Model p n a b, r ∣ orderOf g := by
  obtain ⟨x,hx,y,hy,hxa,hyb,_⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let xm : Model p n a b := ⟨x,Subgroup.subset_closure hx⟩
  let ym : Model p n a b := ⟨y,Subgroup.subset_closure hy⟩
  let letter : Bool → Model p n a b := fun s => if s then xm else ym
  have hxraw : unitEnd p n a b xm=firstEnd p n a := by
    apply LinearMap.ext
    intro w
    change (x : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w=firstEnd p n a w
    rw [hxa]
    rfl
  have hyraw : unitEnd p n a b ym=firstEnd p n b := by
    apply LinearMap.ext
    intro w
    change (y : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w=firstEnd p n b w
    rw [hyb]
    rfl
  have hword : ∀ w : List Bool,
      unitEnd p n a b (w.map letter).prod=wordEnd p n a b w := by
    intro w
    induction w with
    | nil => exact (unitEnd p n a b).map_one
    | cons s w ih =>
      change unitEnd p n a b (letter s*(w.map letter).prod)=
        letterEnd p n a b s*wordEnd p n a b w
      rw [map_mul,ih]
      cases s
      · exact congrArg (fun z => z*wordEnd p n a b w) hyraw
      · exact congrArg (fun z => z*wordEnd p n a b w) hxraw
  let g : Model p n a b := (word.map letter).prod
  letI : MulAction (Model p n a b) (Vector p n) :=
    MulAction.compHom (Vector p n) (unitAction p n a b)
  have hpow (k : ℕ) : g^k • v=(wordEnd p n a b word ^ k) v := by
    change unitEnd p n a b (g^k) v=(wordEnd p n a b word ^ k) v
    rw [map_pow,show unitEnd p n a b g=wordEnd p n a b word from hword word]
  have hd : MulAction.period g v ∣ r :=
    MulAction.pow_smul_eq_iff_period_dvd.mp ((hpow r).trans hreturn)
  have hone : g • v=wordEnd p n a b word v := by simpa only [pow_one] using hpow 1
  have hne : MulAction.period g v≠1 := by
    intro he
    exact hmoved (hone.symm.trans (MulAction.period_eq_one_iff.mp he))
  have he : MulAction.period g v=r := (Nat.dvd_prime hr).mp hd |>.resolve_left hne
  exact ⟨g,by simpa only [he] using MulAction.period_dvd_orderOf g v⟩

theorem prime_dvd_card (p n : ℕ) (a b : Array String)
    (word : List Bool) (r : ℕ) (hr : r.Prime) (v : Vector p n)
    (hreturn : (wordEnd p n a b word ^ r) v=v)
    (hmoved : wordEnd p n a b word v≠v)
    (hn : ¬IsMulCommutative (Model p n a b)) : r ∣ Nat.card (Model p n a b) := by
  obtain ⟨g,hg⟩ := exists_prime_dvd_orderOf p n a b word r hr v hreturn hmoved hn
  exact hg.trans (orderOf_dvd_natCard g)

end SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
