import SymmetricSubgroupAsymptotics.SecondPairChartSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Original joint twelve-point actions in the shared second physical pair
chart. Each literal certificate checks only its original generator images.
The generic structural theorem retains both actual kernels and images.
Historical profiles remain unchanged for alternate capacity-three exports. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue SecondPairChartSocles

/-- Original row52, zero-based index51, joint branch; historical (2,1). -/
def row52Codes : Fin 4 → Fin 5 := ![0,4,1,2]

theorem row52_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row52Generators i) (pairImage (row52Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row52AtThree_quotientSocle (N : Subgroup Row52Top) [N.Normal] :
    SocleNormalGeneratorBound (Row52Top ⧸ N) 3 :=
  quotientSocle_of_codes row52Generators row52Codes row52_preserves 1 2
    (Or.inr rfl) rfl (Or.inl ⟨3,rfl⟩) N

def row52AtThree_family : row52Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row52AtThree_quotientSocle N.1)

/-- Original row53, zero-based index52, joint branch; historical (2,1). -/
def row53Codes : Fin 4 → Fin 5 := ![0,4,1,2]

theorem row53_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row53Generators i) (pairImage (row53Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row53AtThree_quotientSocle (N : Subgroup Row53Top) [N.Normal] :
    SocleNormalGeneratorBound (Row53Top ⧸ N) 3 :=
  quotientSocle_of_codes row53Generators row53Codes row53_preserves 1 2
    (Or.inr rfl) rfl (Or.inl ⟨3,rfl⟩) N

def row53AtThree_family : row53Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row53AtThree_quotientSocle N.1)

/-- Original row86, zero-based index85, joint branch; historical (3,1). -/
def row86Codes : Fin 5 → Fin 5 := ![0,4,0,1,2]

theorem row86_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row86Generators i) (pairImage (row86Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row86_quotientSocle (N : Subgroup Row86Top) [N.Normal] :
    SocleNormalGeneratorBound (Row86Top ⧸ N) 3 :=
  quotientSocle_of_codes row86Generators row86Codes row86_preserves 1 3
    (Or.inr rfl) rfl (Or.inl ⟨4,rfl⟩) N

def row86_family : row86Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row86_quotientSocle N.1)

/-- Original row150, zero-based index149, joint branch; historical (2,1). -/
def row150Codes : Fin 3 → Fin 5 := ![3,1,2]

theorem row150_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row150Generators i) (pairImage (row150Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row150AtThree_quotientSocle (N : Subgroup Row150Top) [N.Normal] :
    SocleNormalGeneratorBound (Row150Top ⧸ N) 3 :=
  quotientSocle_of_codes row150Generators row150Codes row150_preserves 0 1
    (Or.inl rfl) rfl (Or.inl ⟨2,rfl⟩) N

def row150AtThree_family : row150Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row150AtThree_quotientSocle N.1)

/-- Original row151, zero-based index150, joint branch; historical (2,1). -/
def row151Codes : Fin 3 → Fin 5 := ![3,1,2]

theorem row151_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row151Generators i) (pairImage (row151Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row151AtThree_quotientSocle (N : Subgroup Row151Top) [N.Normal] :
    SocleNormalGeneratorBound (Row151Top ⧸ N) 3 :=
  quotientSocle_of_codes row151Generators row151Codes row151_preserves 0 1
    (Or.inl rfl) rfl (Or.inl ⟨2,rfl⟩) N

def row151AtThree_family : row151Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row151AtThree_quotientSocle N.1)

/-- Original row185, zero-based index184, joint branch; historical (3,1). -/
def row185Codes : Fin 4 → Fin 5 := ![3,0,1,2]

theorem row185_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row185Generators i) (pairImage (row185Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row185_quotientSocle (N : Subgroup Row185Top) [N.Normal] :
    SocleNormalGeneratorBound (Row185Top ⧸ N) 3 :=
  quotientSocle_of_codes row185Generators row185Codes row185_preserves 0 2
    (Or.inl rfl) rfl (Or.inl ⟨3,rfl⟩) N

def row185_family : row185Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row185_quotientSocle N.1)

/-- Original row186, zero-based index185, joint branch; historical (3,1). -/
def row186Codes : Fin 5 → Fin 5 := ![3,0,0,1,2]

theorem row186_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row186Generators i) (pairImage (row186Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row186_quotientSocle (N : Subgroup Row186Top) [N.Normal] :
    SocleNormalGeneratorBound (Row186Top ⧸ N) 3 :=
  quotientSocle_of_codes row186Generators row186Codes row186_preserves 0 3
    (Or.inl rfl) rfl (Or.inl ⟨4,rfl⟩) N

def row186_family : row186Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row186_quotientSocle N.1)

/-- Original row221, zero-based index220, joint branch; historical (2,1). -/
def row221Codes : Fin 4 → Fin 5 := ![3,0,1,2]

theorem row221_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row221Generators i) (pairImage (row221Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row221AtThree_quotientSocle (N : Subgroup Row221Top) [N.Normal] :
    SocleNormalGeneratorBound (Row221Top ⧸ N) 3 :=
  quotientSocle_of_codes row221Generators row221Codes row221_preserves 0 2
    (Or.inl rfl) rfl (Or.inl ⟨3,rfl⟩) N

def row221AtThree_family : row221Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row221AtThree_quotientSocle N.1)

/-- Original row223, zero-based index222, joint branch; historical (2,1). -/
def row223Codes : Fin 5 → Fin 5 := ![3,0,0,1,2]

theorem row223_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row223Generators i) (pairImage (row223Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row223AtThree_quotientSocle (N : Subgroup Row223Top) [N.Normal] :
    SocleNormalGeneratorBound (Row223Top ⧸ N) 3 :=
  quotientSocle_of_codes row223Generators row223Codes row223_preserves 0 3
    (Or.inl rfl) rfl (Or.inl ⟨4,rfl⟩) N

def row223AtThree_family : row223Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row223AtThree_quotientSocle N.1)

/-- Original row225, zero-based index224, joint branch; historical (2,1). -/
def row225Codes : Fin 4 → Fin 5 := ![3,0,1,2]

theorem row225_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row225Generators i) (pairImage (row225Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row225AtThree_quotientSocle (N : Subgroup Row225Top) [N.Normal] :
    SocleNormalGeneratorBound (Row225Top ⧸ N) 3 :=
  quotientSocle_of_codes row225Generators row225Codes row225_preserves 0 2
    (Or.inl rfl) rfl (Or.inl ⟨3,rfl⟩) N

def row225AtThree_family : row225Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row225AtThree_quotientSocle N.1)

/-- Original row250, zero-based index249, joint branch; historical (3,1). -/
def row250Codes : Fin 4 → Fin 5 := ![3,0,1,2]

theorem row250_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row250Generators i) (pairImage (row250Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row250_quotientSocle (N : Subgroup Row250Top) [N.Normal] :
    SocleNormalGeneratorBound (Row250Top ⧸ N) 3 :=
  quotientSocle_of_codes row250Generators row250Codes row250_preserves 0 2
    (Or.inl rfl) rfl (Or.inl ⟨3,rfl⟩) N

def row250_family : row250Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row250_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles

end
