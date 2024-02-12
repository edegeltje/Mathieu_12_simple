import Mathieu12Simple.GMetricSpace.Basic

-- note: ⨅  (\biginf) is different from Π (\Pi), despite looking very similar!
-- here, we're using the first.
open GMetricSpace

variable {α : Type*} (s:Set α) (β :Type*) [CompleteLattice β] [LinearOrderedAddCommMonoid β] [GMetricSpace α β]
-- packing radius of a subset β is the supremum such that balls around β are disjoint.
noncomputable def packing_radius : β :=
  ⨆ (x : s) (y:s) (z:α) (_:x≠y)
    (_: (closedBall (x:α) (GDist.gdist (x:α) z:β)) ∩
    (closedBall (y:α) (GDist.gdist (x:α) z : β)) = ∅),
    GDist.gdist (x:α) z

-- todo: distinguish between wether closed balls of packing radius are disjunct or not
-- they are not disjunct iff there is some combination (a b:s) (c:α) with (a≠b) and gdist a c = gdist b c = packing_radius


-- covering radius of a subset β is the smallest radius such that for every element of the space,
-- there is some element in the subset that is closer than that radius.
noncomputable def covering_radius : β :=
  ⨅ (d:β) (x:α) (_:∃ y∈ s, x∈ (ball y d)), d

-- todo: distinguish between wether open balls of covering radius are covering the whole space or not.
-- this doesn't cover the entire space iff there is some point (x:α) such that for all (y:s), gdist s x ≥ covering_radius

def uniformly_discrete : Prop := 0 < (packing_radius s β)

def relatively_dense : Prop := (covering_radius s β) < ⊤

variable (α)

@[ext]
structure GDeloneSet where
  carrier:Set α
  uniformly_discrete' : uniformly_discrete carrier β
  relatively_dense' : relatively_dense carrier β

instance :SetLike (GDeloneSet α β) α where
  coe := GDeloneSet.carrier
  coe_injective' := by intro s1 s2; aesop
