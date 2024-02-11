import Mathieu12Simple.GMetricSpace.Basic

-- note: ⨅  (\biginf) is different from Π (\Pi), despite looking very similar!
-- here, we're using the first.
universe u v

variable {α : Type u} {β :Type v}[CompleteLattice β] [LinearOrderedAddCommMonoid β] [GMetricSpace α β]
-- packing radius of a subset β is half the smallest distance between distinct elements. balls around β are disjoint.
noncomputable def packing_radius (s : Set α): β :=
  ⨆ (d:β) (x : s) (y:s) (z:α) (_:x∉x.ball d),d


-- covering radius of a subset β is the smallest radius such that for every element of the space,
-- there is some element in the subset that is closer than that radius.
noncomputable def covering_radius (β : Set α): ENNReal :=
  ⨅ (d:ENNReal) (x:α) (_:∃ y∈ β, x∈ (EMetric.ball y d)), d

-- def uniformly_discrete (β : Set α): Prop := 0 < packing_radius β

-- def relatively_dense (β : Set α): Prop := covering_radius β < ∞

structure IsDeloneSet {α:Type*} [EMetricSpace α] (β : Set α) :Prop:=
  (uniformly_discrete : 0 < packing_radius β)
  (relatively_dense : covering_radius β < ∞)
