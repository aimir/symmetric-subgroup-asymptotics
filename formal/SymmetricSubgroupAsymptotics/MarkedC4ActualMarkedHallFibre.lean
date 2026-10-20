import SymmetricSubgroupAsymptotics.MarkedC4MarkedFullSecondGraph
import SymmetricSubgroupAsymptotics.MarkedC4ActualHallColumnCompression

/-! An actual marked Hall fibre: a subgroup and r original C4 characters
are injected into the literal full-second family with C4^r coordinates.
The finite moment bound and its two-column estimate are derived here; no
marked enumeration, encoding or character-extension premise is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedHallFibre
open AbelianProductGraphClassification

variable {H : Type} [Group H]

def tupleHom (r : ℕ) (f : Fin r → (H →* Multiplicative (ZMod 4))) :
    H →* Multiplicative (Fin r → ZMod 4) where
  toFun x := Multiplicative.ofAdd (fun i => (f i x).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd ((f i).map_one)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd ((f i).map_mul x y)

theorem tupleHom_injective (r : ℕ) : Function.Injective (@tupleHom H _ r) := by
  intro f g he
  funext i
  apply MonoidHom.ext
  intro x
  apply Multiplicative.toAdd.injective
  exact congrArg (fun q : H →* Multiplicative (Fin r → ZMod 4) => (q x).toAdd i) he

variable {A E : Type} [Group A] [Group E]
local instance fullSecondFintype [Finite A] [Finite E] : Fintype (FullSecond A E) :=
  Fintype.ofFinite _
abbrev Object (r : ℕ) := Σ K : FullSecond A E,Fin r → (K.val →* Multiplicative (ZMod 4))

local instance finiteCharacters [Finite A] [Finite E] (K : FullSecond A E) :
    Finite (K.val →* Multiplicative (ZMod 4)) :=
  Finite.of_injective (fun f : K.val →* Multiplicative (ZMod 4) => (f : K.val → Multiplicative (ZMod 4)))
    DFunLike.coe_injective

def graph (r : ℕ) : Object (A := A) (E := E) r →
    FullSecond (A × Multiplicative (Fin r → ZMod 4)) E :=
  fun z => MarkedFullSecondGraph.graph z.1 (tupleHom r z.2)

theorem graph_injective (r : ℕ) : Function.Injective (@graph A E _ _ r) := by
  rintro ⟨K,f⟩ ⟨L,g⟩ he
  have hh : (⟨K,tupleHom r f⟩ :
      Σ J : FullSecond A E,J.val →* Multiplicative (Fin r → ZMod 4))=
      ⟨L,tupleHom r g⟩ := by
    apply MarkedFullSecondGraph.code_injective
    exact he
  have hKL : K=L := congrArg Sigma.fst hh
  cases hKL
  have hc : HEq (tupleHom r f) (tupleHom r g) := (Sigma.mk.inj_iff.mp hh).2
  have hfg := tupleHom_injective r (eq_of_heq hc)
  cases hfg
  rfl

/-- Exact weighted counting: every r-tuple of original C4 characters is
counted, even when the projection to the second factor has nontrivial kernel. -/
theorem moment_nat_le [Finite A] [Finite E] (r : ℕ) :
    (∑ K : FullSecond A E,Nat.card (K.val →* Multiplicative (ZMod 4))^r) ≤
      Nat.card (FullSecond (A × Multiplicative (Fin r → ZMod 4)) E) := by
  have h := Nat.card_le_card_of_injective (graph (A := A) (E := E) r) (graph_injective r)
  rw [Nat.card_sigma] at h
  simpa only [Nat.card_fun,Nat.card_fin] using h

/-- The genuine full marked fibre now has the two simultaneous source
columns required by the existing Case-I splice, for arbitrary abelian A. -/
theorem moment_le (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    [Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4)))]
    (hA : HasExp2 A (2+m)) (E : Type) [Group E] [Finite E]
    {a : ℝ} (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2)) :
    (∑ K : AbelianProductGraphClassification.FullSecond A E,
      (Nat.card (K.val →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      (∏ k ∈ Finset.range (2+m),
        ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m)*
      (2 : ℝ)^(psi (a/2+r) (col (Abelianization E) 0)+
        psi r (col (Abelianization E) 1)) := by
  have hreal : (∑ K : AbelianProductGraphClassification.FullSecond A E,
      (Nat.card (K.val →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      (Nat.card (AbelianProductGraphClassification.FullSecond
        (A × Multiplicative (Fin r → ZMod 4)) E) : ℝ) := by
    exact_mod_cast moment_nat_le (A := A) (E := E) r
  exact hreal.trans (ActualHallColumnCompression.fullSecond_le m r A hA E hcard)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedHallFibre
