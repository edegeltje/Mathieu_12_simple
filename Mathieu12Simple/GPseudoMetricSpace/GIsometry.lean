import Mathieu12Simple.GPseudoMetricSpace.Basic


-- the domain is explicit because unification needs help
def GIsometry {α₁:Type*} {α₂:Type*} (β:Type*) [LinearOrderedAddCommMonoid β] [GPseudoMetricSpace α₁ β] [GPseudoMetricSpace α₂ β] (φ:α₁ → α₂): Prop :=
  ∀ (x y: α₁), GDist.gdist x y = (GDist.gdist (φ x) (φ y):β)
