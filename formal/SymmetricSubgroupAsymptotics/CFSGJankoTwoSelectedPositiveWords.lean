import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Exactly100 selected positive products. Generic monoid words and naturality; no model claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
def node000 {G : Type*} [Monoid G] (a b : G) : G := a
def node001 {G : Type*} [Monoid G] (a b : G) : G := b
def node002 {G : Type*} [Monoid G] (a b : G) : G := 1

theorem map_node000 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node000 a b)=(node000 (f a) (f b)) := rfl

theorem map_node001 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node001 a b)=(node001 (f a) (f b)) := rfl

theorem map_node002 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node002 a b)=(node002 (f a) (f b)) := map_one f

def node003 {G : Type*} [Monoid G] (a b : G) : G := (node000 a b)*(node001 a b)

theorem map_node003 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node003 a b)=(node003 (f a) (f b)) := by
  change f ((node000 a b)*(node001 a b))=(node000 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node000,map_node001]

def node004 {G : Type*} [Monoid G] (a b : G) : G := (node003 a b)*(node001 a b)

theorem map_node004 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node004 a b)=(node004 (f a) (f b)) := by
  change f ((node003 a b)*(node001 a b))=(node003 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node003,map_node001]

def node005 {G : Type*} [Monoid G] (a b : G) : G := (node003 a b)*(node004 a b)

theorem map_node005 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node005 a b)=(node005 (f a) (f b)) := by
  change f ((node003 a b)*(node004 a b))=(node003 (f a) (f b))*(node004 (f a) (f b))
  simp only [map_mul,map_node003,map_node004]

def node006 {G : Type*} [Monoid G] (a b : G) : G := (node003 a b)*(node005 a b)

theorem map_node006 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node006 a b)=(node006 (f a) (f b)) := by
  change f ((node003 a b)*(node005 a b))=(node003 (f a) (f b))*(node005 (f a) (f b))
  simp only [map_mul,map_node003,map_node005]

def node007 {G : Type*} [Monoid G] (a b : G) : G := (node005 a b)*(node005 a b)

theorem map_node007 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node007 a b)=(node007 (f a) (f b)) := by
  change f ((node005 a b)*(node005 a b))=(node005 (f a) (f b))*(node005 (f a) (f b))
  simp only [map_mul,map_node005]

def node008 {G : Type*} [Monoid G] (a b : G) : G := (node007 a b)*(node003 a b)

theorem map_node008 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node008 a b)=(node008 (f a) (f b)) := by
  change f ((node007 a b)*(node003 a b))=(node007 (f a) (f b))*(node003 (f a) (f b))
  simp only [map_mul,map_node007,map_node003]

def node009 {G : Type*} [Monoid G] (a b : G) : G := (node006 a b)*(node006 a b)

theorem map_node009 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node009 a b)=(node009 (f a) (f b)) := by
  change f ((node006 a b)*(node006 a b))=(node006 (f a) (f b))*(node006 (f a) (f b))
  simp only [map_mul,map_node006]

def node010 {G : Type*} [Monoid G] (a b : G) : G := (node006 a b)*(node009 a b)

theorem map_node010 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node010 a b)=(node010 (f a) (f b)) := by
  change f ((node006 a b)*(node009 a b))=(node006 (f a) (f b))*(node009 (f a) (f b))
  simp only [map_mul,map_node006,map_node009]

def node011 {G : Type*} [Monoid G] (a b : G) : G := (node008 a b)*(node008 a b)

theorem map_node011 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node011 a b)=(node011 (f a) (f b)) := by
  change f ((node008 a b)*(node008 a b))=(node008 (f a) (f b))*(node008 (f a) (f b))
  simp only [map_mul,map_node008]

def node012 {G : Type*} [Monoid G] (a b : G) : G := (node011 a b)*(node011 a b)

theorem map_node012 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node012 a b)=(node012 (f a) (f b)) := by
  change f ((node011 a b)*(node011 a b))=(node011 (f a) (f b))*(node011 (f a) (f b))
  simp only [map_mul,map_node011]

def node013 {G : Type*} [Monoid G] (a b : G) : G := (node008 a b)*(node012 a b)

theorem map_node013 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node013 a b)=(node013 (f a) (f b)) := by
  change f ((node008 a b)*(node012 a b))=(node008 (f a) (f b))*(node012 (f a) (f b))
  simp only [map_mul,map_node008,map_node012]

def node014 {G : Type*} [Monoid G] (a b : G) : G := (node013 a b)*(node010 a b)

theorem map_node014 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node014 a b)=(node014 (f a) (f b)) := by
  change f ((node013 a b)*(node010 a b))=(node013 (f a) (f b))*(node010 (f a) (f b))
  simp only [map_mul,map_node013,map_node010]

def node015 {G : Type*} [Monoid G] (a b : G) : G := (node014 a b)*(node008 a b)

theorem map_node015 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node015 a b)=(node015 (f a) (f b)) := by
  change f ((node014 a b)*(node008 a b))=(node014 (f a) (f b))*(node008 (f a) (f b))
  simp only [map_mul,map_node014,map_node008]

def node016 {G : Type*} [Monoid G] (a b : G) : G := (node015 a b)*(node015 a b)

theorem map_node016 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node016 a b)=(node016 (f a) (f b)) := by
  change f ((node015 a b)*(node015 a b))=(node015 (f a) (f b))*(node015 (f a) (f b))
  simp only [map_mul,map_node015]

def node017 {G : Type*} [Monoid G] (a b : G) : G := (node015 a b)*(node016 a b)

theorem map_node017 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node017 a b)=(node017 (f a) (f b)) := by
  change f ((node015 a b)*(node016 a b))=(node015 (f a) (f b))*(node016 (f a) (f b))
  simp only [map_mul,map_node015,map_node016]

def node018 {G : Type*} [Monoid G] (a b : G) : G := (node017 a b)*(node000 a b)

theorem map_node018 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node018 a b)=(node018 (f a) (f b)) := by
  change f ((node017 a b)*(node000 a b))=(node017 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node017,map_node000]

def node019 {G : Type*} [Monoid G] (a b : G) : G := (node018 a b)*(node015 a b)

theorem map_node019 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node019 a b)=(node019 (f a) (f b)) := by
  change f ((node018 a b)*(node015 a b))=(node018 (f a) (f b))*(node015 (f a) (f b))
  simp only [map_mul,map_node018,map_node015]

def node020 {G : Type*} [Monoid G] (a b : G) : G := (node019 a b)*(node000 a b)

theorem map_node020 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node020 a b)=(node020 (f a) (f b)) := by
  change f ((node019 a b)*(node000 a b))=(node019 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node019,map_node000]

def node021 {G : Type*} [Monoid G] (a b : G) : G := (node020 a b)*(node017 a b)

theorem map_node021 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node021 a b)=(node021 (f a) (f b)) := by
  change f ((node020 a b)*(node017 a b))=(node020 (f a) (f b))*(node017 (f a) (f b))
  simp only [map_mul,map_node020,map_node017]

def node022 {G : Type*} [Monoid G] (a b : G) : G := (node000 a b)*(node015 a b)

theorem map_node022 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node022 a b)=(node022 (f a) (f b)) := by
  change f ((node000 a b)*(node015 a b))=(node000 (f a) (f b))*(node015 (f a) (f b))
  simp only [map_mul,map_node000,map_node015]

def node023 {G : Type*} [Monoid G] (a b : G) : G := (node022 a b)*(node000 a b)

theorem map_node023 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node023 a b)=(node023 (f a) (f b)) := by
  change f ((node022 a b)*(node000 a b))=(node022 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node022,map_node000]

def node024 {G : Type*} [Monoid G] (a b : G) : G := (node023 a b)*(node015 a b)

theorem map_node024 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node024 a b)=(node024 (f a) (f b)) := by
  change f ((node023 a b)*(node015 a b))=(node023 (f a) (f b))*(node015 (f a) (f b))
  simp only [map_mul,map_node023,map_node015]

def node025 {G : Type*} [Monoid G] (a b : G) : G := (node024 a b)*(node000 a b)

theorem map_node025 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node025 a b)=(node025 (f a) (f b)) := by
  change f ((node024 a b)*(node000 a b))=(node024 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node024,map_node000]

def node026 {G : Type*} [Monoid G] (a b : G) : G := (node025 a b)*(node015 a b)

theorem map_node026 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node026 a b)=(node026 (f a) (f b)) := by
  change f ((node025 a b)*(node015 a b))=(node025 (f a) (f b))*(node015 (f a) (f b))
  simp only [map_mul,map_node025,map_node015]

def node027 {G : Type*} [Monoid G] (a b : G) : G := (node026 a b)*(node000 a b)

theorem map_node027 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node027 a b)=(node027 (f a) (f b)) := by
  change f ((node026 a b)*(node000 a b))=(node026 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node026,map_node000]

def node028 {G : Type*} [Monoid G] (a b : G) : G := (node015 a b)*(node015 a b)

theorem map_node028 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node028 a b)=(node028 (f a) (f b)) := by
  change f ((node015 a b)*(node015 a b))=(node015 (f a) (f b))*(node015 (f a) (f b))
  simp only [map_mul,map_node015]

def node029 {G : Type*} [Monoid G] (a b : G) : G := (node028 a b)*(node000 a b)

theorem map_node029 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node029 a b)=(node029 (f a) (f b)) := by
  change f ((node028 a b)*(node000 a b))=(node028 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node028,map_node000]

def node030 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node021 a b)

theorem map_node030 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node030 a b)=(node030 (f a) (f b)) := by
  change f ((node021 a b)*(node021 a b))=(node021 (f a) (f b))*(node021 (f a) (f b))
  simp only [map_mul,map_node021]

def node031 {G : Type*} [Monoid G] (a b : G) : G := (node027 a b)*(node027 a b)

theorem map_node031 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node031 a b)=(node031 (f a) (f b)) := by
  change f ((node027 a b)*(node027 a b))=(node027 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node027]

def node032 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node027 a b)

theorem map_node032 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node032 a b)=(node032 (f a) (f b)) := by
  change f ((node021 a b)*(node027 a b))=(node021 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node021,map_node027]

def node033 {G : Type*} [Monoid G] (a b : G) : G := (node032 a b)*(node030 a b)

theorem map_node033 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node033 a b)=(node033 (f a) (f b)) := by
  change f ((node032 a b)*(node030 a b))=(node032 (f a) (f b))*(node030 (f a) (f b))
  simp only [map_mul,map_node032,map_node030]

def node034 {G : Type*} [Monoid G] (a b : G) : G := (node033 a b)*(node031 a b)

theorem map_node034 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node034 a b)=(node034 (f a) (f b)) := by
  change f ((node033 a b)*(node031 a b))=(node033 (f a) (f b))*(node031 (f a) (f b))
  simp only [map_mul,map_node033,map_node031]

def node035 {G : Type*} [Monoid G] (a b : G) : G := (node034 a b)*(node034 a b)

theorem map_node035 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node035 a b)=(node035 (f a) (f b)) := by
  change f ((node034 a b)*(node034 a b))=(node034 (f a) (f b))*(node034 (f a) (f b))
  simp only [map_mul,map_node034]

def node036 {G : Type*} [Monoid G] (a b : G) : G := (node035 a b)*(node035 a b)

theorem map_node036 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node036 a b)=(node036 (f a) (f b)) := by
  change f ((node035 a b)*(node035 a b))=(node035 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node035]

def node037 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node021 a b)

theorem map_node037 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node037 a b)=(node037 (f a) (f b)) := by
  change f ((node021 a b)*(node021 a b))=(node021 (f a) (f b))*(node021 (f a) (f b))
  simp only [map_mul,map_node021]

def node038 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node037 a b)

theorem map_node038 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node038 a b)=(node038 (f a) (f b)) := by
  change f ((node021 a b)*(node037 a b))=(node021 (f a) (f b))*(node037 (f a) (f b))
  simp only [map_mul,map_node021,map_node037]

def node039 {G : Type*} [Monoid G] (a b : G) : G := (node027 a b)*(node027 a b)

theorem map_node039 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node039 a b)=(node039 (f a) (f b)) := by
  change f ((node027 a b)*(node027 a b))=(node027 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node027]

def node040 {G : Type*} [Monoid G] (a b : G) : G := (node027 a b)*(node039 a b)

theorem map_node040 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node040 a b)=(node040 (f a) (f b)) := by
  change f ((node027 a b)*(node039 a b))=(node027 (f a) (f b))*(node039 (f a) (f b))
  simp only [map_mul,map_node027,map_node039]

def node041 {G : Type*} [Monoid G] (a b : G) : G := (node035 a b)*(node035 a b)

theorem map_node041 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node041 a b)=(node041 (f a) (f b)) := by
  change f ((node035 a b)*(node035 a b))=(node035 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node035]

def node042 {G : Type*} [Monoid G] (a b : G) : G := (node035 a b)*(node041 a b)

theorem map_node042 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node042 a b)=(node042 (f a) (f b)) := by
  change f ((node035 a b)*(node041 a b))=(node035 (f a) (f b))*(node041 (f a) (f b))
  simp only [map_mul,map_node035,map_node041]

def node043 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node035 a b)

theorem map_node043 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node043 a b)=(node043 (f a) (f b)) := by
  change f ((node021 a b)*(node035 a b))=(node021 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node021,map_node035]

def node044 {G : Type*} [Monoid G] (a b : G) : G := (node035 a b)*(node021 a b)

theorem map_node044 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node044 a b)=(node044 (f a) (f b)) := by
  change f ((node035 a b)*(node021 a b))=(node035 (f a) (f b))*(node021 (f a) (f b))
  simp only [map_mul,map_node035,map_node021]

def node045 {G : Type*} [Monoid G] (a b : G) : G := (node027 a b)*(node035 a b)

theorem map_node045 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node045 a b)=(node045 (f a) (f b)) := by
  change f ((node027 a b)*(node035 a b))=(node027 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node027,map_node035]

def node046 {G : Type*} [Monoid G] (a b : G) : G := (node035 a b)*(node027 a b)

theorem map_node046 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node046 a b)=(node046 (f a) (f b)) := by
  change f ((node035 a b)*(node027 a b))=(node035 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node035,map_node027]

def node047 {G : Type*} [Monoid G] (a b : G) : G := (node027 a b)*(node021 a b)

theorem map_node047 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node047 a b)=(node047 (f a) (f b)) := by
  change f ((node027 a b)*(node021 a b))=(node027 (f a) (f b))*(node021 (f a) (f b))
  simp only [map_mul,map_node027,map_node021]

def node048 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node027 a b)

theorem map_node048 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node048 a b)=(node048 (f a) (f b)) := by
  change f ((node021 a b)*(node027 a b))=(node021 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node021,map_node027]

def node049 {G : Type*} [Monoid G] (a b : G) : G := (node048 a b)*(node035 a b)

theorem map_node049 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node049 a b)=(node049 (f a) (f b)) := by
  change f ((node048 a b)*(node035 a b))=(node048 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node048,map_node035]

def node050 {G : Type*} [Monoid G] (a b : G) : G := (node029 a b)*(node021 a b)

theorem map_node050 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node050 a b)=(node050 (f a) (f b)) := by
  change f ((node029 a b)*(node021 a b))=(node029 (f a) (f b))*(node021 (f a) (f b))
  simp only [map_mul,map_node029,map_node021]

def node051 {G : Type*} [Monoid G] (a b : G) : G := (node030 a b)*(node027 a b)

theorem map_node051 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node051 a b)=(node051 (f a) (f b)) := by
  change f ((node030 a b)*(node027 a b))=(node030 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node030,map_node027]

def node052 {G : Type*} [Monoid G] (a b : G) : G := (node051 a b)*(node035 a b)

theorem map_node052 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node052 a b)=(node052 (f a) (f b)) := by
  change f ((node051 a b)*(node035 a b))=(node051 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node051,map_node035]

def node053 {G : Type*} [Monoid G] (a b : G) : G := (node052 a b)*(node029 a b)

theorem map_node053 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node053 a b)=(node053 (f a) (f b)) := by
  change f ((node052 a b)*(node029 a b))=(node052 (f a) (f b))*(node029 (f a) (f b))
  simp only [map_mul,map_node052,map_node029]

def node054 {G : Type*} [Monoid G] (a b : G) : G := (node029 a b)*(node027 a b)

theorem map_node054 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node054 a b)=(node054 (f a) (f b)) := by
  change f ((node029 a b)*(node027 a b))=(node029 (f a) (f b))*(node027 (f a) (f b))
  simp only [map_mul,map_node029,map_node027]

def node055 {G : Type*} [Monoid G] (a b : G) : G := (node021 a b)*(node029 a b)

theorem map_node055 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node055 a b)=(node055 (f a) (f b)) := by
  change f ((node021 a b)*(node029 a b))=(node021 (f a) (f b))*(node029 (f a) (f b))
  simp only [map_mul,map_node021,map_node029]

def node056 {G : Type*} [Monoid G] (a b : G) : G := (node029 a b)*(node035 a b)

theorem map_node056 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node056 a b)=(node056 (f a) (f b)) := by
  change f ((node029 a b)*(node035 a b))=(node029 (f a) (f b))*(node035 (f a) (f b))
  simp only [map_mul,map_node029,map_node035]

def node057 {G : Type*} [Monoid G] (a b : G) : G := (node036 a b)*(node029 a b)

theorem map_node057 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node057 a b)=(node057 (f a) (f b)) := by
  change f ((node036 a b)*(node029 a b))=(node036 (f a) (f b))*(node029 (f a) (f b))
  simp only [map_mul,map_node036,map_node029]

def node058 {G : Type*} [Monoid G] (a b : G) : G := (node000 a b)*(node000 a b)

theorem map_node058 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node058 a b)=(node058 (f a) (f b)) := by
  change f ((node000 a b)*(node000 a b))=(node000 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node000]

def node059 {G : Type*} [Monoid G] (a b : G) : G := (node001 a b)*(node001 a b)

theorem map_node059 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node059 a b)=(node059 (f a) (f b)) := by
  change f ((node001 a b)*(node001 a b))=(node001 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node001]

def node060 {G : Type*} [Monoid G] (a b : G) : G := (node059 a b)*(node001 a b)

theorem map_node060 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node060 a b)=(node060 (f a) (f b)) := by
  change f ((node059 a b)*(node001 a b))=(node059 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node059,map_node001]

def node061 {G : Type*} [Monoid G] (a b : G) : G := (node000 a b)*(node001 a b)

theorem map_node061 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node061 a b)=(node061 (f a) (f b)) := by
  change f ((node000 a b)*(node001 a b))=(node000 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node000,map_node001]

def node062 {G : Type*} [Monoid G] (a b : G) : G := (node002 a b)*(node061 a b)

theorem map_node062 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node062 a b)=(node062 (f a) (f b)) := by
  change f ((node002 a b)*(node061 a b))=(node002 (f a) (f b))*(node061 (f a) (f b))
  simp only [map_mul,map_node002,map_node061]

def node063 {G : Type*} [Monoid G] (a b : G) : G := (node061 a b)*(node061 a b)

theorem map_node063 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node063 a b)=(node063 (f a) (f b)) := by
  change f ((node061 a b)*(node061 a b))=(node061 (f a) (f b))*(node061 (f a) (f b))
  simp only [map_mul,map_node061]

def node064 {G : Type*} [Monoid G] (a b : G) : G := (node062 a b)*(node063 a b)

theorem map_node064 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node064 a b)=(node064 (f a) (f b)) := by
  change f ((node062 a b)*(node063 a b))=(node062 (f a) (f b))*(node063 (f a) (f b))
  simp only [map_mul,map_node062,map_node063]

def node065 {G : Type*} [Monoid G] (a b : G) : G := (node063 a b)*(node063 a b)

theorem map_node065 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node065 a b)=(node065 (f a) (f b)) := by
  change f ((node063 a b)*(node063 a b))=(node063 (f a) (f b))*(node063 (f a) (f b))
  simp only [map_mul,map_node063]

def node066 {G : Type*} [Monoid G] (a b : G) : G := (node064 a b)*(node065 a b)

theorem map_node066 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node066 a b)=(node066 (f a) (f b)) := by
  change f ((node064 a b)*(node065 a b))=(node064 (f a) (f b))*(node065 (f a) (f b))
  simp only [map_mul,map_node064,map_node065]

def node067 {G : Type*} [Monoid G] (a b : G) : G := (node002 a b)*(node000 a b)

theorem map_node067 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node067 a b)=(node067 (f a) (f b)) := by
  change f ((node002 a b)*(node000 a b))=(node002 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node002,map_node000]

def node068 {G : Type*} [Monoid G] (a b : G) : G := (node067 a b)*(node059 a b)

theorem map_node068 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node068 a b)=(node068 (f a) (f b)) := by
  change f ((node067 a b)*(node059 a b))=(node067 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node067,map_node059]

def node069 {G : Type*} [Monoid G] (a b : G) : G := (node068 a b)*(node000 a b)

theorem map_node069 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node069 a b)=(node069 (f a) (f b)) := by
  change f ((node068 a b)*(node000 a b))=(node068 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node068,map_node000]

def node070 {G : Type*} [Monoid G] (a b : G) : G := (node069 a b)*(node001 a b)

theorem map_node070 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node070 a b)=(node070 (f a) (f b)) := by
  change f ((node069 a b)*(node001 a b))=(node069 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node069,map_node001]

def node071 {G : Type*} [Monoid G] (a b : G) : G := (node002 a b)*(node000 a b)

theorem map_node071 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node071 a b)=(node071 (f a) (f b)) := by
  change f ((node002 a b)*(node000 a b))=(node002 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node002,map_node000]

def node072 {G : Type*} [Monoid G] (a b : G) : G := (node071 a b)*(node001 a b)

theorem map_node072 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node072 a b)=(node072 (f a) (f b)) := by
  change f ((node071 a b)*(node001 a b))=(node071 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node071,map_node001]

def node073 {G : Type*} [Monoid G] (a b : G) : G := (node072 a b)*(node000 a b)

theorem map_node073 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node073 a b)=(node073 (f a) (f b)) := by
  change f ((node072 a b)*(node000 a b))=(node072 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node072,map_node000]

def node074 {G : Type*} [Monoid G] (a b : G) : G := (node073 a b)*(node001 a b)

theorem map_node074 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node074 a b)=(node074 (f a) (f b)) := by
  change f ((node073 a b)*(node001 a b))=(node073 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node073,map_node001]

def node075 {G : Type*} [Monoid G] (a b : G) : G := (node074 a b)*(node000 a b)

theorem map_node075 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node075 a b)=(node075 (f a) (f b)) := by
  change f ((node074 a b)*(node000 a b))=(node074 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node074,map_node000]

def node076 {G : Type*} [Monoid G] (a b : G) : G := (node075 a b)*(node059 a b)

theorem map_node076 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node076 a b)=(node076 (f a) (f b)) := by
  change f ((node075 a b)*(node059 a b))=(node075 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node075,map_node059]

def node077 {G : Type*} [Monoid G] (a b : G) : G := (node076 a b)*(node000 a b)

theorem map_node077 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node077 a b)=(node077 (f a) (f b)) := by
  change f ((node076 a b)*(node000 a b))=(node076 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node076,map_node000]

def node078 {G : Type*} [Monoid G] (a b : G) : G := (node077 a b)*(node001 a b)

theorem map_node078 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node078 a b)=(node078 (f a) (f b)) := by
  change f ((node077 a b)*(node001 a b))=(node077 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node077,map_node001]

def node079 {G : Type*} [Monoid G] (a b : G) : G := (node078 a b)*(node000 a b)

theorem map_node079 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node079 a b)=(node079 (f a) (f b)) := by
  change f ((node078 a b)*(node000 a b))=(node078 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node078,map_node000]

def node080 {G : Type*} [Monoid G] (a b : G) : G := (node079 a b)*(node059 a b)

theorem map_node080 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node080 a b)=(node080 (f a) (f b)) := by
  change f ((node079 a b)*(node059 a b))=(node079 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node079,map_node059]

def node081 {G : Type*} [Monoid G] (a b : G) : G := (node080 a b)*(node000 a b)

theorem map_node081 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node081 a b)=(node081 (f a) (f b)) := by
  change f ((node080 a b)*(node000 a b))=(node080 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node080,map_node000]

def node082 {G : Type*} [Monoid G] (a b : G) : G := (node081 a b)*(node059 a b)

theorem map_node082 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node082 a b)=(node082 (f a) (f b)) := by
  change f ((node081 a b)*(node059 a b))=(node081 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node081,map_node059]

def node083 {G : Type*} [Monoid G] (a b : G) : G := (node082 a b)*(node000 a b)

theorem map_node083 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node083 a b)=(node083 (f a) (f b)) := by
  change f ((node082 a b)*(node000 a b))=(node082 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node082,map_node000]

def node084 {G : Type*} [Monoid G] (a b : G) : G := (node083 a b)*(node001 a b)

theorem map_node084 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node084 a b)=(node084 (f a) (f b)) := by
  change f ((node083 a b)*(node001 a b))=(node083 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node083,map_node001]

def node085 {G : Type*} [Monoid G] (a b : G) : G := (node084 a b)*(node000 a b)

theorem map_node085 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node085 a b)=(node085 (f a) (f b)) := by
  change f ((node084 a b)*(node000 a b))=(node084 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node084,map_node000]

def node086 {G : Type*} [Monoid G] (a b : G) : G := (node085 a b)*(node001 a b)

theorem map_node086 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node086 a b)=(node086 (f a) (f b)) := by
  change f ((node085 a b)*(node001 a b))=(node085 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node085,map_node001]

def node087 {G : Type*} [Monoid G] (a b : G) : G := (node086 a b)*(node000 a b)

theorem map_node087 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node087 a b)=(node087 (f a) (f b)) := by
  change f ((node086 a b)*(node000 a b))=(node086 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node086,map_node000]

def node088 {G : Type*} [Monoid G] (a b : G) : G := (node087 a b)*(node059 a b)

theorem map_node088 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node088 a b)=(node088 (f a) (f b)) := by
  change f ((node087 a b)*(node059 a b))=(node087 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node087,map_node059]

def node089 {G : Type*} [Monoid G] (a b : G) : G := (node088 a b)*(node000 a b)

theorem map_node089 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node089 a b)=(node089 (f a) (f b)) := by
  change f ((node088 a b)*(node000 a b))=(node088 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node088,map_node000]

def node090 {G : Type*} [Monoid G] (a b : G) : G := (node089 a b)*(node059 a b)

theorem map_node090 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node090 a b)=(node090 (f a) (f b)) := by
  change f ((node089 a b)*(node059 a b))=(node089 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node089,map_node059]

def node091 {G : Type*} [Monoid G] (a b : G) : G := (node090 a b)*(node000 a b)

theorem map_node091 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node091 a b)=(node091 (f a) (f b)) := by
  change f ((node090 a b)*(node000 a b))=(node090 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node090,map_node000]

def node092 {G : Type*} [Monoid G] (a b : G) : G := (node091 a b)*(node001 a b)

theorem map_node092 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node092 a b)=(node092 (f a) (f b)) := by
  change f ((node091 a b)*(node001 a b))=(node091 (f a) (f b))*(node001 (f a) (f b))
  simp only [map_mul,map_node091,map_node001]

def node093 {G : Type*} [Monoid G] (a b : G) : G := (node092 a b)*(node000 a b)

theorem map_node093 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node093 a b)=(node093 (f a) (f b)) := by
  change f ((node092 a b)*(node000 a b))=(node092 (f a) (f b))*(node000 (f a) (f b))
  simp only [map_mul,map_node092,map_node000]

def node094 {G : Type*} [Monoid G] (a b : G) : G := (node093 a b)*(node059 a b)

theorem map_node094 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node094 a b)=(node094 (f a) (f b)) := by
  change f ((node093 a b)*(node059 a b))=(node093 (f a) (f b))*(node059 (f a) (f b))
  simp only [map_mul,map_node093,map_node059]

def node095 {G : Type*} [Monoid G] (a b : G) : G := (node070 a b)*(node070 a b)

theorem map_node095 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node095 a b)=(node095 (f a) (f b)) := by
  change f ((node070 a b)*(node070 a b))=(node070 (f a) (f b))*(node070 (f a) (f b))
  simp only [map_mul,map_node070]

def node096 {G : Type*} [Monoid G] (a b : G) : G := (node095 a b)*(node095 a b)

theorem map_node096 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node096 a b)=(node096 (f a) (f b)) := by
  change f ((node095 a b)*(node095 a b))=(node095 (f a) (f b))*(node095 (f a) (f b))
  simp only [map_mul,map_node095]

def node097 {G : Type*} [Monoid G] (a b : G) : G := (node002 a b)*(node096 a b)

theorem map_node097 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node097 a b)=(node097 (f a) (f b)) := by
  change f ((node002 a b)*(node096 a b))=(node002 (f a) (f b))*(node096 (f a) (f b))
  simp only [map_mul,map_node002,map_node096]

def node098 {G : Type*} [Monoid G] (a b : G) : G := (node096 a b)*(node096 a b)

theorem map_node098 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node098 a b)=(node098 (f a) (f b)) := by
  change f ((node096 a b)*(node096 a b))=(node096 (f a) (f b))*(node096 (f a) (f b))
  simp only [map_mul,map_node096]

def node099 {G : Type*} [Monoid G] (a b : G) : G := (node097 a b)*(node098 a b)

theorem map_node099 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node099 a b)=(node099 (f a) (f b)) := by
  change f ((node097 a b)*(node098 a b))=(node097 (f a) (f b))*(node098 (f a) (f b))
  simp only [map_mul,map_node097,map_node098]

def node100 {G : Type*} [Monoid G] (a b : G) : G := (node002 a b)*(node094 a b)

theorem map_node100 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node100 a b)=(node100 (f a) (f b)) := by
  change f ((node002 a b)*(node094 a b))=(node002 (f a) (f b))*(node094 (f a) (f b))
  simp only [map_mul,map_node002,map_node094]

def node101 {G : Type*} [Monoid G] (a b : G) : G := (node094 a b)*(node094 a b)

theorem map_node101 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node101 a b)=(node101 (f a) (f b)) := by
  change f ((node094 a b)*(node094 a b))=(node094 (f a) (f b))*(node094 (f a) (f b))
  simp only [map_mul,map_node094]

def node102 {G : Type*} [Monoid G] (a b : G) : G := (node100 a b)*(node101 a b)

theorem map_node102 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node102 a b)=(node102 (f a) (f b)) := by
  change f ((node100 a b)*(node101 a b))=(node100 (f a) (f b))*(node101 (f a) (f b))
  simp only [map_mul,map_node100,map_node101]

theorem power000 {G : Type*} [Monoid G] (a b : G) : (node006 a b)^1=(node006 a b) := by
  exact pow_one _

theorem power001 {G : Type*} [Monoid G] (a b : G) : (node006 a b)^2=(node009 a b) := by
  calc
    (node006 a b)^2=(node006 a b)^1*(node006 a b)^1 := pow_add _ 1 1
    _=(node006 a b)*(node006 a b) := congrArg₂ (fun x y : G => x*y)
      (power000 a b) (power000 a b)
    _=(node009 a b) := rfl

theorem power002 {G : Type*} [Monoid G] (a b : G) : (node009 a b)^1=(node009 a b) := by
  exact pow_one _

theorem power003 {G : Type*} [Monoid G] (a b : G) : (node006 a b)^2=(node009 a b) := by
  calc
    (node006 a b)^2=((node006 a b)^2)^1 := pow_mul _ 2 1
    _=(node009 a b)^1 := congrArg (fun x : G => x^1) (power001 a b)
    _=(node009 a b) := power002 a b

theorem power004 {G : Type*} [Monoid G] (a b : G) : (node006 a b)^3=(node010 a b) := by
  calc
    (node006 a b)^3=(node006 a b)^1*(node006 a b)^2 := pow_add _ 1 2
    _=(node006 a b)*(node009 a b) := congrArg₂ (fun x y : G => x*y)
      (power000 a b) (power003 a b)
    _=(node010 a b) := rfl

theorem power005 {G : Type*} [Monoid G] (a b : G) : (node008 a b)^1=(node008 a b) := by
  exact pow_one _

theorem power006 {G : Type*} [Monoid G] (a b : G) : (node008 a b)^2=(node011 a b) := by
  calc
    (node008 a b)^2=(node008 a b)^1*(node008 a b)^1 := pow_add _ 1 1
    _=(node008 a b)*(node008 a b) := congrArg₂ (fun x y : G => x*y)
      (power005 a b) (power005 a b)
    _=(node011 a b) := rfl

theorem power007 {G : Type*} [Monoid G] (a b : G) : (node011 a b)^1=(node011 a b) := by
  exact pow_one _

theorem power008 {G : Type*} [Monoid G] (a b : G) : (node011 a b)^2=(node012 a b) := by
  calc
    (node011 a b)^2=(node011 a b)^1*(node011 a b)^1 := pow_add _ 1 1
    _=(node011 a b)*(node011 a b) := congrArg₂ (fun x y : G => x*y)
      (power007 a b) (power007 a b)
    _=(node012 a b) := rfl

theorem power009 {G : Type*} [Monoid G] (a b : G) : (node012 a b)^1=(node012 a b) := by
  exact pow_one _

theorem power010 {G : Type*} [Monoid G] (a b : G) : (node011 a b)^2=(node012 a b) := by
  calc
    (node011 a b)^2=((node011 a b)^2)^1 := pow_mul _ 2 1
    _=(node012 a b)^1 := congrArg (fun x : G => x^1) (power008 a b)
    _=(node012 a b) := power009 a b

theorem power011 {G : Type*} [Monoid G] (a b : G) : (node008 a b)^4=(node012 a b) := by
  calc
    (node008 a b)^4=((node008 a b)^2)^2 := pow_mul _ 2 2
    _=(node011 a b)^2 := congrArg (fun x : G => x^2) (power006 a b)
    _=(node012 a b) := power010 a b

theorem power012 {G : Type*} [Monoid G] (a b : G) : (node008 a b)^5=(node013 a b) := by
  calc
    (node008 a b)^5=(node008 a b)^1*(node008 a b)^4 := pow_add _ 1 4
    _=(node008 a b)*(node012 a b) := congrArg₂ (fun x y : G => x*y)
      (power005 a b) (power011 a b)
    _=(node013 a b) := rfl

theorem power013 {G : Type*} [Monoid G] (a b : G) : (node015 a b)^1=(node015 a b) := by
  exact pow_one _

theorem power014 {G : Type*} [Monoid G] (a b : G) : (node015 a b)^2=(node016 a b) := by
  calc
    (node015 a b)^2=(node015 a b)^1*(node015 a b)^1 := pow_add _ 1 1
    _=(node015 a b)*(node015 a b) := congrArg₂ (fun x y : G => x*y)
      (power013 a b) (power013 a b)
    _=(node016 a b) := rfl

theorem power015 {G : Type*} [Monoid G] (a b : G) : (node016 a b)^1=(node016 a b) := by
  exact pow_one _

theorem power016 {G : Type*} [Monoid G] (a b : G) : (node015 a b)^2=(node016 a b) := by
  calc
    (node015 a b)^2=((node015 a b)^2)^1 := pow_mul _ 2 1
    _=(node016 a b)^1 := congrArg (fun x : G => x^1) (power014 a b)
    _=(node016 a b) := power015 a b

theorem power017 {G : Type*} [Monoid G] (a b : G) : (node015 a b)^3=(node017 a b) := by
  calc
    (node015 a b)^3=(node015 a b)^1*(node015 a b)^2 := pow_add _ 1 2
    _=(node015 a b)*(node016 a b) := congrArg₂ (fun x y : G => x*y)
      (power013 a b) (power016 a b)
    _=(node017 a b) := rfl

theorem power018 {G : Type*} [Monoid G] (a b : G) : (node000 a b)^1=(node000 a b) := by
  exact pow_one _

theorem power019 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^1=(node021 a b) := by
  exact pow_one _

theorem power020 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^2=(node030 a b) := by
  calc
    (node021 a b)^2=(node021 a b)^1*(node021 a b)^1 := pow_add _ 1 1
    _=(node021 a b)*(node021 a b) := congrArg₂ (fun x y : G => x*y)
      (power019 a b) (power019 a b)
    _=(node030 a b) := rfl

theorem power021 {G : Type*} [Monoid G] (a b : G) : (node030 a b)^1=(node030 a b) := by
  exact pow_one _

theorem power022 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^2=(node030 a b) := by
  calc
    (node021 a b)^2=((node021 a b)^2)^1 := pow_mul _ 2 1
    _=(node030 a b)^1 := congrArg (fun x : G => x^1) (power020 a b)
    _=(node030 a b) := power021 a b

theorem power023 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^1=(node027 a b) := by
  exact pow_one _

theorem power024 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^2=(node031 a b) := by
  calc
    (node027 a b)^2=(node027 a b)^1*(node027 a b)^1 := pow_add _ 1 1
    _=(node027 a b)*(node027 a b) := congrArg₂ (fun x y : G => x*y)
      (power023 a b) (power023 a b)
    _=(node031 a b) := rfl

theorem power025 {G : Type*} [Monoid G] (a b : G) : (node031 a b)^1=(node031 a b) := by
  exact pow_one _

theorem power026 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^2=(node031 a b) := by
  calc
    (node027 a b)^2=((node027 a b)^2)^1 := pow_mul _ 2 1
    _=(node031 a b)^1 := congrArg (fun x : G => x^1) (power024 a b)
    _=(node031 a b) := power025 a b

theorem power027 {G : Type*} [Monoid G] (a b : G) : (node034 a b)^1=(node034 a b) := by
  exact pow_one _

theorem power028 {G : Type*} [Monoid G] (a b : G) : (node034 a b)^2=(node035 a b) := by
  calc
    (node034 a b)^2=(node034 a b)^1*(node034 a b)^1 := pow_add _ 1 1
    _=(node034 a b)*(node034 a b) := congrArg₂ (fun x y : G => x*y)
      (power027 a b) (power027 a b)
    _=(node035 a b) := rfl

theorem power029 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^1=(node035 a b) := by
  exact pow_one _

theorem power030 {G : Type*} [Monoid G] (a b : G) : (node034 a b)^2=(node035 a b) := by
  calc
    (node034 a b)^2=((node034 a b)^2)^1 := pow_mul _ 2 1
    _=(node035 a b)^1 := congrArg (fun x : G => x^1) (power028 a b)
    _=(node035 a b) := power029 a b

theorem power031 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^1=(node035 a b) := by
  exact pow_one _

theorem power032 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^2=(node036 a b) := by
  calc
    (node035 a b)^2=(node035 a b)^1*(node035 a b)^1 := pow_add _ 1 1
    _=(node035 a b)*(node035 a b) := congrArg₂ (fun x y : G => x*y)
      (power031 a b) (power031 a b)
    _=(node036 a b) := rfl

theorem power033 {G : Type*} [Monoid G] (a b : G) : (node036 a b)^1=(node036 a b) := by
  exact pow_one _

theorem power034 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^2=(node036 a b) := by
  calc
    (node035 a b)^2=((node035 a b)^2)^1 := pow_mul _ 2 1
    _=(node036 a b)^1 := congrArg (fun x : G => x^1) (power032 a b)
    _=(node036 a b) := power033 a b

theorem power035 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^1=(node021 a b) := by
  exact pow_one _

theorem power036 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^2=(node037 a b) := by
  calc
    (node021 a b)^2=(node021 a b)^1*(node021 a b)^1 := pow_add _ 1 1
    _=(node021 a b)*(node021 a b) := congrArg₂ (fun x y : G => x*y)
      (power035 a b) (power035 a b)
    _=(node037 a b) := rfl

theorem power037 {G : Type*} [Monoid G] (a b : G) : (node037 a b)^1=(node037 a b) := by
  exact pow_one _

theorem power038 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^2=(node037 a b) := by
  calc
    (node021 a b)^2=((node021 a b)^2)^1 := pow_mul _ 2 1
    _=(node037 a b)^1 := congrArg (fun x : G => x^1) (power036 a b)
    _=(node037 a b) := power037 a b

theorem power039 {G : Type*} [Monoid G] (a b : G) : (node021 a b)^3=(node038 a b) := by
  calc
    (node021 a b)^3=(node021 a b)^1*(node021 a b)^2 := pow_add _ 1 2
    _=(node021 a b)*(node037 a b) := congrArg₂ (fun x y : G => x*y)
      (power035 a b) (power038 a b)
    _=(node038 a b) := rfl

theorem power040 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^1=(node027 a b) := by
  exact pow_one _

theorem power041 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^2=(node039 a b) := by
  calc
    (node027 a b)^2=(node027 a b)^1*(node027 a b)^1 := pow_add _ 1 1
    _=(node027 a b)*(node027 a b) := congrArg₂ (fun x y : G => x*y)
      (power040 a b) (power040 a b)
    _=(node039 a b) := rfl

theorem power042 {G : Type*} [Monoid G] (a b : G) : (node039 a b)^1=(node039 a b) := by
  exact pow_one _

theorem power043 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^2=(node039 a b) := by
  calc
    (node027 a b)^2=((node027 a b)^2)^1 := pow_mul _ 2 1
    _=(node039 a b)^1 := congrArg (fun x : G => x^1) (power041 a b)
    _=(node039 a b) := power042 a b

theorem power044 {G : Type*} [Monoid G] (a b : G) : (node027 a b)^3=(node040 a b) := by
  calc
    (node027 a b)^3=(node027 a b)^1*(node027 a b)^2 := pow_add _ 1 2
    _=(node027 a b)*(node039 a b) := congrArg₂ (fun x y : G => x*y)
      (power040 a b) (power043 a b)
    _=(node040 a b) := rfl

theorem power045 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^1=(node035 a b) := by
  exact pow_one _

theorem power046 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^2=(node041 a b) := by
  calc
    (node035 a b)^2=(node035 a b)^1*(node035 a b)^1 := pow_add _ 1 1
    _=(node035 a b)*(node035 a b) := congrArg₂ (fun x y : G => x*y)
      (power045 a b) (power045 a b)
    _=(node041 a b) := rfl

theorem power047 {G : Type*} [Monoid G] (a b : G) : (node041 a b)^1=(node041 a b) := by
  exact pow_one _

theorem power048 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^2=(node041 a b) := by
  calc
    (node035 a b)^2=((node035 a b)^2)^1 := pow_mul _ 2 1
    _=(node041 a b)^1 := congrArg (fun x : G => x^1) (power046 a b)
    _=(node041 a b) := power047 a b

theorem power049 {G : Type*} [Monoid G] (a b : G) : (node035 a b)^3=(node042 a b) := by
  calc
    (node035 a b)^3=(node035 a b)^1*(node035 a b)^2 := pow_add _ 1 2
    _=(node035 a b)*(node041 a b) := congrArg₂ (fun x y : G => x*y)
      (power045 a b) (power048 a b)
    _=(node042 a b) := rfl

theorem power050 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^0=(node002 a b) := by
  simp only [pow_zero,node002]

theorem power051 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^1=(node061 a b) := by
  exact pow_one _

theorem power052 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^1=(node062 a b) := by
  calc
    (node061 a b)^1=(node061 a b)^0*(node061 a b)^1 := pow_add _ 0 1
    _=(node002 a b)*(node061 a b) := congrArg₂ (fun x y : G => x*y)
      (power050 a b) (power051 a b)
    _=(node062 a b) := rfl

theorem power053 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^2=(node063 a b) := by
  calc
    (node061 a b)^2=(node061 a b)^1*(node061 a b)^1 := pow_add _ 1 1
    _=(node061 a b)*(node061 a b) := congrArg₂ (fun x y : G => x*y)
      (power051 a b) (power051 a b)
    _=(node063 a b) := rfl

theorem power054 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^3=(node064 a b) := by
  calc
    (node061 a b)^3=(node061 a b)^1*(node061 a b)^2 := pow_add _ 1 2
    _=(node062 a b)*(node063 a b) := congrArg₂ (fun x y : G => x*y)
      (power052 a b) (power053 a b)
    _=(node064 a b) := rfl

theorem power055 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^4=(node065 a b) := by
  calc
    (node061 a b)^4=(node061 a b)^2*(node061 a b)^2 := pow_add _ 2 2
    _=(node063 a b)*(node063 a b) := congrArg₂ (fun x y : G => x*y)
      (power053 a b) (power053 a b)
    _=(node065 a b) := rfl

theorem power056 {G : Type*} [Monoid G] (a b : G) : (node061 a b)^7=(node066 a b) := by
  calc
    (node061 a b)^7=(node061 a b)^3*(node061 a b)^4 := pow_add _ 3 4
    _=(node064 a b)*(node065 a b) := congrArg₂ (fun x y : G => x*y)
      (power054 a b) (power055 a b)
    _=(node066 a b) := rfl

theorem power057 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^0=(node002 a b) := by
  simp only [pow_zero,node002]

theorem power058 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^1=(node070 a b) := by
  exact pow_one _

theorem power059 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^2=(node095 a b) := by
  calc
    (node070 a b)^2=(node070 a b)^1*(node070 a b)^1 := pow_add _ 1 1
    _=(node070 a b)*(node070 a b) := congrArg₂ (fun x y : G => x*y)
      (power058 a b) (power058 a b)
    _=(node095 a b) := rfl

theorem power060 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^4=(node096 a b) := by
  calc
    (node070 a b)^4=(node070 a b)^2*(node070 a b)^2 := pow_add _ 2 2
    _=(node095 a b)*(node095 a b) := congrArg₂ (fun x y : G => x*y)
      (power059 a b) (power059 a b)
    _=(node096 a b) := rfl

theorem power061 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^4=(node097 a b) := by
  calc
    (node070 a b)^4=(node070 a b)^0*(node070 a b)^4 := pow_add _ 0 4
    _=(node002 a b)*(node096 a b) := congrArg₂ (fun x y : G => x*y)
      (power057 a b) (power060 a b)
    _=(node097 a b) := rfl

theorem power062 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^8=(node098 a b) := by
  calc
    (node070 a b)^8=(node070 a b)^4*(node070 a b)^4 := pow_add _ 4 4
    _=(node096 a b)*(node096 a b) := congrArg₂ (fun x y : G => x*y)
      (power060 a b) (power060 a b)
    _=(node098 a b) := rfl

theorem power063 {G : Type*} [Monoid G] (a b : G) : (node070 a b)^12=(node099 a b) := by
  calc
    (node070 a b)^12=(node070 a b)^4*(node070 a b)^8 := pow_add _ 4 8
    _=(node097 a b)*(node098 a b) := congrArg₂ (fun x y : G => x*y)
      (power061 a b) (power062 a b)
    _=(node099 a b) := rfl

theorem power064 {G : Type*} [Monoid G] (a b : G) : (node094 a b)^0=(node002 a b) := by
  simp only [pow_zero,node002]

theorem power065 {G : Type*} [Monoid G] (a b : G) : (node094 a b)^1=(node094 a b) := by
  exact pow_one _

theorem power066 {G : Type*} [Monoid G] (a b : G) : (node094 a b)^1=(node100 a b) := by
  calc
    (node094 a b)^1=(node094 a b)^0*(node094 a b)^1 := pow_add _ 0 1
    _=(node002 a b)*(node094 a b) := congrArg₂ (fun x y : G => x*y)
      (power064 a b) (power065 a b)
    _=(node100 a b) := rfl

theorem power067 {G : Type*} [Monoid G] (a b : G) : (node094 a b)^2=(node101 a b) := by
  calc
    (node094 a b)^2=(node094 a b)^1*(node094 a b)^1 := pow_add _ 1 1
    _=(node094 a b)*(node094 a b) := congrArg₂ (fun x y : G => x*y)
      (power065 a b) (power065 a b)
    _=(node101 a b) := rfl

theorem power068 {G : Type*} [Monoid G] (a b : G) : (node094 a b)^3=(node102 a b) := by
  calc
    (node094 a b)^3=(node094 a b)^1*(node094 a b)^2 := pow_add _ 1 2
    _=(node100 a b)*(node101 a b) := congrArg₂ (fun x y : G => x*y)
      (power066 a b) (power067 a b)
    _=(node102 a b) := rfl

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
