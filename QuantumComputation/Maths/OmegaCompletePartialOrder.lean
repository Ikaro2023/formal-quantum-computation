/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Order.OrderClosed


/-!
# Topological results on `OmegaCompletePartialOrder`s.

We show `OmegaCompletePartialOrder.ofCompactSpace`:
Any compact space with a closed partial order is an `ω`-complete partial order.
-/

@[expose] public section

open scoped Topology

namespace OmegaCompletePartialOrder
variable {α : Type*}

@[simp]
theorem Chain.coe_mk [Preorder α] (f : ℕ →o α) : ⇑(Chain.mk f) = f :=
  rfl

@[simp]
theorem Pi.ωSup_apply {β : α → Type*} [∀ a, OmegaCompletePartialOrder (β a)]
    (c : OmegaCompletePartialOrder.Chain (∀ a, β a)) (a : α) :
    ωSup c a = ωSup (c.map (Pi.evalOrderHom a)) :=
  rfl

lemma chain_isLUB_of_mapClusterPt [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    (c : OmegaCompletePartialOrder.Chain α) {a : α} (ha : MapClusterPt a Filter.atTop c) :
    IsLUB (Set.range c) a := by
  constructor
  · rintro _ ⟨i, rfl⟩
    apply isClosed_Ici.mem_of_mapClusterPt ha
    filter_upwards [Filter.eventually_ge_atTop i] with n hn
    exact c.monotone hn
  · intro x hx
    apply isClosed_Iic.mem_of_mapClusterPt ha
    exact Filter.Eventually.of_forall fun n ↦ hx ⟨n, rfl⟩

/-- In any compact space with a closed partial order, a monotone chain converges to its `ωSup`. -/
lemma tendsto_ωSup
    [OmegaCompletePartialOrder α] [TopologicalSpace α] [CompactSpace α] [OrderClosedTopology α]
    (c : OmegaCompletePartialOrder.Chain α) :
    Filter.Tendsto c Filter.atTop (𝓝 (OmegaCompletePartialOrder.ωSup c)) :=
  isCompact_univ.tendsto_nhds_of_unique_mapClusterPt (.of_forall fun _ => Set.mem_univ _)
    fun _ _ ha ↦ OmegaCompletePartialOrder.ωSup_eq_of_isLUB (chain_isLUB_of_mapClusterPt c ha)

/-- If a monotone chain stabilizes at index `N`, its `ωSup` equals `c N`. -/
lemma ωSup_eq_of_stabilizes [OmegaCompletePartialOrder α]
    (c : OmegaCompletePartialOrder.Chain α) (N : ℕ) (hstab : ∀ k ≥ N, c k = c N) :
    OmegaCompletePartialOrder.ωSup c = c N := by
  apply le_antisymm
  · apply OmegaCompletePartialOrder.ωSup_le c (c N)
    intro k
    by_cases hk : k ≤ N
    · exact c.monotone hk
    · rw [hstab k (by omega)]
  · exact OmegaCompletePartialOrder.le_ωSup c N

section compactChain
variable [TopologicalSpace α] [PartialOrder α]

/-- A chain contained in a compact set in a closed ordered space has a least upper bound in
that set. -/
@[no_expose] noncomputable def compactChainSup
    {K : Set α} (hK : IsCompact K)
    (c : OmegaCompletePartialOrder.Chain α) (hc : ∀ n, c n ∈ K) : α :=
  Classical.choose (hK.exists_mapClusterPt (f := Filter.atTop) (u := c) (by
    rw [Filter.le_principal_iff]
    change ∀ᶠ n in Filter.atTop, c n ∈ K
    exact Filter.Eventually.of_forall hc))

lemma compactChainSup_spec {K : Set α} (hK : IsCompact K)
    (c : OmegaCompletePartialOrder.Chain α) (hc : ∀ n, c n ∈ K) :
    compactChainSup hK c hc ∈ K ∧
      MapClusterPt (compactChainSup hK c hc) Filter.atTop c := by
  exact Classical.choose_spec (hK.exists_mapClusterPt (f := Filter.atTop) (u := c) (by
    rw [Filter.le_principal_iff]
    change ∀ᶠ n in Filter.atTop, c n ∈ K
    exact Filter.Eventually.of_forall hc))

lemma compactChainSup_mem {K : Set α} (hK : IsCompact K)
    (c : OmegaCompletePartialOrder.Chain α) (hc : ∀ n, c n ∈ K) :
    compactChainSup hK c hc ∈ K :=
  (compactChainSup_spec hK c hc).1

lemma compactChainSup_mapClusterPt {K : Set α} (hK : IsCompact K)
    (c : OmegaCompletePartialOrder.Chain α) (hc : ∀ n, c n ∈ K) :
    MapClusterPt (compactChainSup hK c hc) Filter.atTop c :=
  (compactChainSup_spec hK c hc).2

lemma compactChainSup_isLUB [OrderClosedTopology α] {K : Set α} (hK : IsCompact K)
    (c : OmegaCompletePartialOrder.Chain α) (hc : ∀ n, c n ∈ K) :
    IsLUB (Set.range c) (compactChainSup hK c hc) :=
  OmegaCompletePartialOrder.chain_isLUB_of_mapClusterPt c (compactChainSup_mapClusterPt hK c hc)

lemma compactChainSup_tendsto [OrderClosedTopology α] {K : Set α} (hK : IsCompact K)
    (c : OmegaCompletePartialOrder.Chain α) (hc : ∀ n, c n ∈ K) :
    Filter.Tendsto c Filter.atTop (nhds (compactChainSup hK c hc)) := by
  apply hK.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hc)
  intro a _ ha
  exact (OmegaCompletePartialOrder.chain_isLUB_of_mapClusterPt c ha).unique
    (compactChainSup_isLUB hK c hc)

/-- Any compact space with a closed partial order is an `ω`-complete partial order. -/
noncomputable abbrev ofCompactSpace [CompactSpace α] [OrderClosedTopology α] :
    OmegaCompletePartialOrder α where
  ωSup c := compactChainSup isCompact_univ c fun _ ↦ Set.mem_univ _
  le_ωSup c i :=
    (compactChainSup_isLUB isCompact_univ c fun _ ↦ Set.mem_univ _).1 ⟨i, rfl⟩
  ωSup_le c _ hA :=
    (compactChainSup_isLUB isCompact_univ c fun _ ↦ Set.mem_univ _).2 fun _ ⟨i, hi⟩ ↦ hi ▸ hA i

end compactChain

end OmegaCompletePartialOrder
