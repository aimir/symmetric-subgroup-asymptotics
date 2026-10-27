import SymmetricSubgroupAsymptotics.ActualFullWreathPreimage

/-! Exact finite bookkeeping over the actual quotient-image family. Each
fibre retains an original subgroup; kernel/image pairs are never treated
as determining a subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ActualFullWreathFamilyFibreSum
open PermutationalWreathProduct ActualFullWreathFamily ActualFullWreathPreimage

variable {R R' Q I : Type} [Group R] [Group R'] [Group Q] [MulAction Q I]
    (phi : R →* R') (hphi : Function.Surjective phi)

instance familyFinite [Finite R] [Finite Q] [Finite I] : Finite (Family R Q I) := by
  letI : Finite (PermutationalWreathProduct R Q I) :=
    Finite.of_injective (fun w : PermutationalWreathProduct R Q I => (w.left,w.right))
      (by
        intro a b h
        apply PermutationalWreathProduct.ext
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h)
  exact Finite.of_injective (fun L : Family R Q I => (L.val : Set
    (PermutationalWreathProduct R Q I))) (by
      intro L M h
      exact Subtype.ext (SetLike.coe_injective h))

def fibreEquiv : Family R Q I ≃ Σ H : Family R' Q I,Fibre phi hphi H where
  toFun L := ⟨localImage phi hphi L,L,rfl⟩
  invFun a := a.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨H,L,hL⟩
    cases hL
    rfl

theorem card_eq_sum [Finite (Family R Q I)] [Finite (Family R' Q I)] :
    letI : Fintype (Family R' Q I) := Fintype.ofFinite _
    Nat.card (Family R Q I)=∑ H : Family R' Q I,Nat.card (Fibre phi hphi H) := by
  letI : Fintype (Family R' Q I) := Fintype.ofFinite _
  rw [Nat.card_congr (fibreEquiv phi hphi),Nat.card_sigma]

theorem card_le_mul [Finite (Family R Q I)] [Finite (Family R' Q I)] (B : ℕ)
    (hB : ∀ H : Family R' Q I,Nat.card (Fibre phi hphi H)≤B) :
    Nat.card (Family R Q I)≤Nat.card (Family R' Q I)*B := by
  letI : Fintype (Family R' Q I) := Fintype.ofFinite _
  rw [card_eq_sum phi hphi]
  calc
    ∑ H : Family R' Q I,Nat.card (Fibre phi hphi H) ≤ ∑ _H : Family R' Q I,B :=
      Finset.sum_le_sum (fun H _ => hB H)
    _=Nat.card (Family R' Q I)*B := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.ActualFullWreathFamilyFibreSum
