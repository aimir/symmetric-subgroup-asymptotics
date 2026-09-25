import SymmetricSubgroupAsymptotics.BinaryPairCertificateCapacity
import SymmetricSubgroupAsymptotics.GeneratedPair8.Local8T19

/-! Every pair record for 8T19, installed on the literal original
permutation subgroup with its retained original normal and physical width.
The residual character/transport indices remain an explicit branch. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairInstalled8T19
local instance : Group BinaryNormal8T19.Source := BinaryMenuCayley8T19.group
abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T19.generators)
abbrev frame := BinaryPair8T19.Frame0.physicalFrame

def generators (j : Fin 4) : Original :=
  BinaryMenuCayley8T19.originalEquiv (BinaryNormal8T19.generators j)
theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  have h := congrArg (Subgroup.map BinaryMenuCayley8T19.originalEquiv.toMonoidHom)
    BinaryNormal8T19.generators_full
  rw [MonoidHom.map_closure] at h
  have ht := Subgroup.map_top_of_surjective BinaryMenuCayley8T19.originalEquiv.toMonoidHom
    BinaryMenuCayley8T19.originalEquiv.surjective
  have he : BinaryMenuCayley8T19.originalEquiv.toMonoidHom '' Set.range BinaryNormal8T19.generators=
      Set.range generators := by ext x; simp [generators]
  rw [he] at h
  exact h.trans ht
theorem original_isPGroup : IsPGroup 2 Original :=
  BinaryNormal8T19.source_isPGroup.of_surjective
    BinaryMenuCayley8T19.originalEquiv.toMonoidHom BinaryMenuCayley8T19.originalEquiv.surjective

def pairIndices : Fin 11 → Fin 12 := (Fin.cases (1 : Fin 12) (Fin.cases (2 : Fin 12) (Fin.cases (3 : Fin 12) (Fin.cases (4 : Fin 12) (Fin.cases (5 : Fin 12) (Fin.cases (6 : Fin 12) (Fin.cases (7 : Fin 12) (Fin.cases (8 : Fin 12) (Fin.cases (9 : Fin 12) (Fin.cases (10 : Fin 12) (Fin.cases (11 : Fin 12) Fin.elim0)))))))))))
def residualIndices : List (Fin 12) := [0]
theorem index_coverage (i : Fin 12) :
    i∈residualIndices ∨ ∃ j, pairIndices j=i := by revert i; decide +kernel

def physicalNormal (j : Fin 11) : Subgroup Original :=
  (BinaryNormal8T19.states (pairIndices j)).kernel.map BinaryMenuCayley8T19.originalEquiv.toMonoidHom
instance physicalNormal_normal (j : Fin 11) : (physicalNormal j).Normal :=
  Subgroup.Normal.map inferInstance _ BinaryMenuCayley8T19.originalEquiv.surjective

def physicalCertificates : (j : Fin 11) →
    BinaryPairLocalCertificate generators frame.top (physicalNormal j) :=
  (Fin.cases (BinaryPairLocal8T19.N1.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N2.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N3.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N4.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N5.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N6.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N7.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N8.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N9.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N10.certificate.transport BinaryMenuCayley8T19.originalEquiv) (Fin.cases (BinaryPairLocal8T19.N11.certificate.transport BinaryMenuCayley8T19.originalEquiv) (fun i => Fin.elim0 i))))))))))))

theorem physical_width (j : Fin 11) :
    (physicalCertificates j).width=Nat.card (Fin 8) := by
  rw [Nat.card_fin]
  fin_cases j <;> rfl

def physicalCut (j : Fin 11) := sectionSubgroupImage (p := 2)
  (V := frame.kernelSpace ⧸ frame.normalSpace (physicalNormal j))
  (frame.sectionMap (physicalNormal j)) ((physicalCertificates j).kernelCut frame)

theorem physical_cutDimension (j : Fin 11) :
    Module.finrank (ZMod 2) (physicalCut j)=(physicalCertificates j).cutDimension :=
  (physicalCertificates j).cutDimension_eq frame (physicalNormal j)

/-- The exact capacity is for the retained original quotient action after
its retained actual central cut. -/
theorem physical_capacity (j : Fin 11) :
    representationSchurCapacity ((physicalCertificates j).physicalRepresentation
      frame (physicalNormal j) generators generators_full)=
        ((physicalCertificates j).fixedDimension:ℝ) :=
  (physicalCertificates j).capacity_eq frame (physicalNormal j) generators
    generators_full original_isPGroup

/-- The numerical gap is now tied to the actual eight physical points. -/
theorem physical_gap (j : Fin 11) :
    ((physicalCertificates j).coverDegree:ℝ)+2*(physicalCertificates j).cutDimension+
      4*representationSchurCapacity ((physicalCertificates j).physicalRepresentation
        frame (physicalNormal j) generators generators_full)<8 := by
  have h := (physicalCertificates j).physical_gap frame (physicalNormal j) generators
    generators_full original_isPGroup (physical_width j)
  simpa only [Nat.card_fin] using h

theorem physical_gap_actual (j : Fin 11) :
    ((physicalCertificates j).coverDegree:ℝ)+2*Module.finrank (ZMod 2) (physicalCut j)+
      4*representationSchurCapacity ((physicalCertificates j).physicalRepresentation
        frame (physicalNormal j) generators generators_full)<8 := by
  rw [physical_cutDimension]
  exact physical_gap j

/-- Every original normal enters a fully installed pair certificate or one
of the explicitly retained character/transport normal rows. -/
theorem normal_coverage (N : Subgroup Original) [N.Normal] :
    (∃ j, physicalNormal j=N) ∨
      ∃ i∈residualIndices, (BinaryNormal8T19.states i).kernel.map
        BinaryMenuCayley8T19.originalEquiv.toMonoidHom=N := by
  obtain ⟨i,hi⟩ := BinaryNormal8T19.registry.complete_map_of_equiv
    BinaryNormal8T19.source_isPGroup BinaryMenuCayley8T19.originalEquiv N
  rcases index_coverage i with hr|⟨j,hj⟩
  · exact Or.inr ⟨i,hr,hi⟩
  · exact Or.inl ⟨j,by simpa only [physicalNormal,hj] using hi⟩
end SymmetricSubgroupAsymptotics.BinaryPairInstalled8T19
