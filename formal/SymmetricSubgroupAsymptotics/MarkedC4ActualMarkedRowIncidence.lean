import SymmetricSubgroupAsymptotics.MarkedC4ActualPrefixOrders
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedHallFibre

/-! Literal marked row incidence. There is ONE global marking homomorphism
on each actual subgroup. Its values on recovering generators encode it;
independent marking homomorphisms on physical factors are never assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedRowIncidence
open ActualSubdirectFiltration ActualEfficientLiftRecovery
open ActualEfficientRowIncidence ActualPrefixOrders

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (D : ∀ i,Subgroup (F i)) (M : Type) [Group M] [Finite M]

local instance : Fintype (Family F D) := Fintype.ofFinite _
local instance finiteHom (H : Family F D) : Finite (H.val →* M) :=
  Finite.of_injective (fun f : H.val →* M => (f : H.val → M)) DFunLike.coe_injective

abbrev Positions := Σ i : Fin t,Fin (normalGen (D i))
abbrev Source := Σ H : Family F D,
  LiftArray F H.val H.property.1 × (H.val →* M)

def code (z : Source F D M) : Target F D × (Positions F D → M) :=
  (ActualEfficientRowIncidence.code F D ⟨z.1,z.2.1⟩,
    fun p => z.2.2 (z.2.1 p.1 ((labels F D z.1 p.1).symm p.2)).val)

/-- Physical recovery identifies H and its lift array; ordinary generation
then identifies the SAME global marking homomorphism. -/
theorem code_injective : Function.Injective (code F D M) := by
  rintro ⟨H,a,f⟩ ⟨K,b,g⟩ he
  have hz : (⟨H,a⟩ : Σ H : Family F D,LiftArray F H.val H.property.1)=⟨K,b⟩ :=
    ActualEfficientRowIncidence.code_injective F D (congrArg Prod.fst he)
  have hHK : H=K := congrArg Sigma.fst hz
  cases hHK
  have hab : a=b := eq_of_heq (Sigma.mk.inj_iff.mp hz).2
  cases hab
  have hfg : f=g := by
    letI : Group.IsNilpotent H.val := H.property.2.1
    apply MonoidHom.eq_of_eqOn_dense (closure_eq_top F H.val H.property.1 a)
    rintro _ ⟨⟨i,q⟩,rfl⟩
    have h := congrFun (congrArg Prod.snd he) ⟨i,labels F D H i q⟩
    have hq := (labels F D H i).symm_apply_apply q
    exact (congrArg (fun q' => f (a i q').val) hq).symm.trans
      (h.trans (congrArg (fun q' => g (a i q').val) hq))
  cases hfg
  rfl

/-- Marked enumeration with the exact recovering-array multiplicities.
The target annotations are values of a global mark, counted permissively. -/
theorem weighted_card_le :
    (∑ H : Family F D,
      multiplicity F D H*Nat.card (H.val →* M)) ≤
      Nat.card (Target F D)*Nat.card M^(∑ i : Fin t,normalGen (D i)) := by
  have h := Nat.card_le_card_of_injective (code F D M) (code_injective F D M)
  have hs : Nat.card (Source F D M)=
      ∑ H : Family F D,multiplicity F D H*Nat.card (H.val →* M) := by
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro H _
    rw [Nat.card_prod,ActualEfficientLiftMultiplicity.card_liftArray]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [H.property.2.2 i]
  have hp : Nat.card (Positions F D)=∑ i : Fin t,normalGen (D i) := by
    simp only [Positions,Nat.card_sigma,Nat.card_fin]
  rw [hs,Nat.card_prod,Nat.card_fun,hp] at h
  exact h

/-- Fixed actual diagonals make the marked incidence multiplicity constant. -/
theorem multiplicity_mul_moment_le (H : Family F D) :
    multiplicity F D H*(∑ K : Family F D,Nat.card (K.val →* M)) ≤
      Nat.card (Target F D)*Nat.card M^(∑ i : Fin t,normalGen (D i)) := by
  have h := weighted_card_le F D M
  have hs : (∑ K : Family F D,multiplicity F D K*Nat.card (K.val →* M))=
      multiplicity F D H*(∑ K : Family F D,Nat.card (K.val →* M)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun K _ => by rw [multiplicity_eq F D K H])
  rw [hs] at h
  exact h

/-- The multiplicity is positive because every actual prefix is a finite
group, including trivial prefixes and empty generator sets. -/
theorem multiplicity_pos (H : Family F D) : 0<multiplicity F D H := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos Nat.card_pos _

/-- Explicit real division for the genuine global-mark moment. -/
theorem moment_real_le (H : Family F D) :
    (∑ K : Family F D,(Nat.card (K.val →* M) : ℝ)) ≤
      ((Nat.card (Target F D) : ℝ)*(Nat.card M : ℝ)^(∑ i : Fin t,normalGen (D i)))/
        (multiplicity F D H : ℝ) := by
  have hp : (0 : ℝ)<multiplicity F D H := by
    exact_mod_cast multiplicity_pos F D H
  apply (le_div_iff₀ hp).mpr
  have h := multiplicity_mul_moment_le F D M H
  have hr : (multiplicity F D H : ℝ)*
      (∑ K : Family F D,(Nat.card (K.val →* M) : ℝ)) ≤
        (Nat.card (Target F D) : ℝ)*(Nat.card M : ℝ)^(∑ i : Fin t,normalGen (D i)) := by
    exact_mod_cast h
  simpa only [mul_comm] using hr

/-- A tuple of original C4 characters is exactly ONE homomorphism to the
global C4^r mark group, without a character-extension premise. -/
def globalHomEquiv (E : Type) [Group E] (r : ℕ) :
    (Fin r → (E →* Multiplicative (ZMod 4))) ≃
      (E →* Multiplicative (Fin r → ZMod 4)) where
  toFun := ActualMarkedHallFibre.tupleHom r
  invFun f i :=
    { toFun := fun x => Multiplicative.ofAdd ((f x).toAdd i)
      map_one' := by
        exact congrArg (fun z : Multiplicative (Fin r → ZMod 4) =>
          Multiplicative.ofAdd (z.toAdd i)) f.map_one
      map_mul' := fun x y => by
        exact congrArg (fun z : Multiplicative (Fin r → ZMod 4) =>
          Multiplicative.ofAdd (z.toAdd i)) (f.map_mul x y) }
  left_inv f := by funext i; apply MonoidHom.ext; intro x; rfl
  right_inv f := by
    apply MonoidHom.ext
    intro x
    apply Multiplicative.toAdd.injective
    funext i
    rfl

theorem globalHom_card (E : Type) [Group E] (r : ℕ) :
    Nat.card (E →* Multiplicative (Fin r → ZMod 4))=
      Nat.card (E →* Multiplicative (ZMod 4))^r := by
  rw [← Nat.card_congr (globalHomEquiv E r),Nat.card_fun,Nat.card_fin]

/-- The original marked moment admits real multiplicity cancellation on
the actual fixed-diagonal nilpotent family. This coarse row still counts
all generator mark values; sharper correlated Hall optimization is separate. -/
theorem cyclicFour_moment_real_le (H : Family F D) (r : ℕ) :
    (∑ K : Family F D,(Nat.card (K.val →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      ((Nat.card (Target F D) : ℝ)*(4 : ℝ)^(r*(∑ i : Fin t,normalGen (D i))))/
        (multiplicity F D H : ℝ) := by
  have h := moment_real_le F D (Multiplicative (Fin r → ZMod 4)) H
  have hM : Nat.card (Multiplicative (Fin r → ZMod 4))=4^r := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  simp only [globalHom_card,Nat.cast_pow,hM,Nat.cast_ofNat,← pow_mul] at h
  exact h

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedRowIncidence
