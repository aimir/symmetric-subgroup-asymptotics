import SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleWholeCount
import SymmetricSubgroupAsymptotics.PrimitiveSocleIsotypicOrdinaryCompression

/-! Whole-family installation for the SAME actual primitive-local data.
The full socle chart and its common simple type are discharged internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualPrimitiveSocleWreathWholeCount
open PrimitiveSocleRawStructure PrimitiveSocleONanScottHelpers
variable {R X Q I : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
    [Group Q] [Finite Q] [MulAction Q I] [Finite I] (D : NonaffineData R X)

include D in
theorem card_family_le (a : ℕ) (ha : Nat.card (R ⧸ finiteGroupSocle R)≤2^a)
    {q : ℕ} (fQ : Fin q → Q) (hfQ : Subgroup.closure (Set.range fQ)=⊤) :
    Nat.card (ActualFullWreathFamily.Family R Q I)≤
      (2^((Nat.card I*a)*(Nat.card I*a))*
        Nat.card (R ⧸ finiteGroupSocle R)^(Nat.card I*q))*
      ((2^(Nat.card I*D.factorCount)*
        (2*(1+(Nat.card I*D.factorCount)*Nat.card (D.Simple ≃* D.Simple)))^
          (Nat.card I*D.factorCount))*
        Nat.card D.Simple^((Nat.card I*D.factorCount)*(Nat.card I*a+q))) := by
  have hh := ActualFullWreathSemisimpleWholeCount.card_family_le
    (Q := Q) (I := I)
    (finiteGroupSocle R) D.socleEquiv
    (centerless_of_nonabelian_simple D.Simple D.noncommutative) a ha fQ hfQ
  simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.ActualPrimitiveSocleWreathWholeCount
