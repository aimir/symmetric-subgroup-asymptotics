import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.CFSGSuzukiOriginalTorusAction
import SymmetricSubgroupAsymptotics.CFSGSuzukiLeastIndexOrder
import Mathlib.Data.Finite.Card

/-! The literal central root subgroup has order q and all its nonidentity
members are conjugate by original torus matrices. Burnside's fixed-point
formula therefore forces every faithful Suzuki permutation action to
have degree at least q. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiCentralPermutationDegree
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiTorus
open CFSGConjugateSubgroupDegree PrimitiveSocleRawStructure

def centralModelHom (m : ℕ) : Multiplicative (Field m) →* CFSG.Models.Suzuki m where
  toFun b := ⟨unipotentElement m 0 b.toAdd,unipotentElement_mem_model m 0 b.toAdd⟩
  map_one' := Subtype.ext (unipotentElement_zero m)
  map_mul' b d := by
    apply Subtype.ext
    change unipotentElement m 0 (b.toAdd+d.toAdd)=
      unipotentElement m 0 b.toAdd*unipotentElement m 0 d.toAdd
    rw [unipotentElement_mul]
    simp only [map_zero,zero_mul,add_zero]

theorem centralModelHom_injective (m : ℕ) : Function.Injective (centralModelHom m) := by
  intro b d he
  exact congrArg (fun g : CFSG.Models.Suzuki m =>
    (g.val : CFSG.Models.SuzukiConstruction.Mat m) 2 0) he

def centralModelSubgroup (m : ℕ) : Subgroup (CFSG.Models.Suzuki m) :=
  (centralModelHom m).range

theorem centralModelSubgroup_card (m : ℕ) :
    Nat.card (centralModelSubgroup m)=Nat.card (Field m) :=
  (Nat.card_congr (MonoidHom.ofInjective (centralModelHom_injective m)).toEquiv).symm

def modelTorus (m : ℕ) (c : (Field m)ˣ) : CFSG.Models.Suzuki m :=
  ⟨torusElement m c,torusElement_mem_model m c⟩

theorem centralModelHom_conjugate (m : ℕ) (c : (Field m)ˣ) (b : Field m) :
    modelTorus m c*centralModelHom m (Multiplicative.ofAdd b)*(modelTorus m c)⁻¹=
      centralModelHom m (Multiplicative.ofAdd (((c : Field m)*theta m (c : Field m))⁻¹*b)) := by
  apply Subtype.ext
  change torusElement m c*unipotentElement m 0 b*(torusElement m c)⁻¹=_
  simpa only [mul_zero] using original_torus_conjugation m c 0 b

theorem nonidentity_central_conjugate (m : ℕ)
    (a b : centralModelSubgroup m) (ha : a≠1) (hb : b≠1) :
    ∃ g : CFSG.Models.Suzuki m,g*(a : CFSG.Models.Suzuki m)*g⁻¹=(b : CFSG.Models.Suzuki m) := by
  obtain ⟨x,hx⟩ := a.property
  obtain ⟨y,hy⟩ := b.property
  have hx0 : x.toAdd≠0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [←hx]
    change (centralModelHom m) (Multiplicative.ofAdd x.toAdd)=1
    rw [he]
    exact (centralModelHom m).map_one
  have hy0 : y.toAdd≠0 := by
    intro he
    apply hb
    apply Subtype.ext
    rw [←hy]
    change (centralModelHom m) (Multiplicative.ofAdd y.toAdd)=1
    rw [he]
    exact (centralModelHom m).map_one
  obtain ⟨c,hc⟩ := (thetaProduct_bijective m).surjective (x.toAdd/y.toAdd)
  have hc0 : c≠0 := by
    intro he
    rw [he,thetaProduct,map_zero,mul_zero] at hc
    exact div_ne_zero hx0 hy0 hc.symm
  let u : (Field m)ˣ := Units.mk0 c hc0
  refine ⟨modelTorus m u,?_⟩
  rw [←hx,←hy]
  change modelTorus m u*centralModelHom m (Multiplicative.ofAdd x.toAdd)*(modelTorus m u)⁻¹=
    centralModelHom m (Multiplicative.ofAdd y.toAdd)
  rw [centralModelHom_conjugate]
  apply congrArg (centralModelHom m)
  apply congrArg Multiplicative.ofAdd
  change (thetaProduct m c)⁻¹*x.toAdd=y.toAdd
  rw [hc]
  field_simp [hx0,hy0]

theorem field_card_le_proper_index (m : ℕ) [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (H : Subgroup (CFSG.Models.Suzuki m)) (hH : H≠⊤) : Nat.card (Field m)≤H.index := by
  letI : Nontrivial (centralModelSubgroup m) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [centralModelSubgroup_card]
    exact Finite.one_lt_card)
  rw [←centralModelSubgroup_card]
  exact card_le_index_of_nonidentity_conjugate (centralModelSubgroup m)
    (nonidentity_central_conjugate m) H hH

theorem field_card_le_leastProperIndex (m ell : ℕ)
    [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (hell : LeastProperIndex (CFSG.Models.Suzuki m) ell) : Nat.card (Field m)≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact field_card_le_proper_index m H hH

end SymmetricSubgroupAsymptotics.CFSGSuzukiCentralPermutationDegree
