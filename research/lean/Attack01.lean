/-
Erdős Problem 74 — attack campaign `erdos74-close-2026-09-05`.

Canonical statement (erdosproblems.com/74, $500):
  Let f(n) → ∞ (possibly very slowly).  Is there a graph of infinite chromatic
  number such that every finite subgraph on n vertices can be made bipartite by
  deleting at most f(n) edges?

STATUS OF THIS FILE: the problem is NOT closed here.  What is proved below is the
"rate-free" half: a graph whose bipartite-defect function is *bounded* has finite
chromatic number, with an explicit bound.  Equivalently, the hypothesis
`Tendsto f atTop atTop` in the formalisation of Erdős 74 is NECESSARY and cannot be
weakened to "f bounded": for bounded f the answer is unconditionally NO.

The object definitions are transcribed verbatim from
  google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/74.lean`
  (Apache License 2.0, Copyright 2025 The Formal Conjectures Authors)
so that every theorem below is a theorem about *those* objects.  The two lemmas
marked `[FC]` are also transcribed from that file (they are its `category test`
lemmas); everything after the `NEW` banner is this campaign's own work.
-/

import Mathlib

open Filter SimpleGraph

namespace Erdos74Close

universe u
variable {V : Type u}

/-! ## Object definitions (transcribed, formal-conjectures ErdosProblems/74.lean) -/

/-- For a given subgraph `A`, the set of all `k` such that `A` can be made bipartite
by deleting `k` edges. -/
def edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe) }

/-- The minimum number of edges that must be deleted from `A` to make it bipartite. -/
noncomputable def minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| edgeDistancesToBipartite A

/-- `minEdgeDistToBipartite A` ranged over subgraphs `A` of `G` on `n` vertices. -/
def subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (minEdgeDistToBipartite A) | (A : G.Subgraph) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/-- The smallest `k` such that every subgraph of `G` on `n` vertices can be made
bipartite by deleting at most `k` edges.  This is Definition 3.1 in [EHS82]. -/
noncomputable def maxSubgraphEdgeDistToBipartite (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup <| subgraphEdgeDistsToBipartite G n

/-- [FC] Deleting every edge makes a graph bipartite, so the set is nonempty. -/
theorem edgeDistancesToBipartite_nonempty {G : SimpleGraph V} (A : G.Subgraph) :
    (edgeDistancesToBipartite A).Nonempty := by
  dsimp only [edgeDistancesToBipartite, Set.nonempty_def]
  refine ⟨_, A.edgeSet, fun _ a ↦ a, ?_, rfl⟩
  use fun _ => 0
  simp

/-- [FC] A graph on `n` vertices has at most `n.choose 2` edges, so the set of
distances of `n`-vertex subgraphs is bounded above. -/
theorem subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (subgraphEdgeDistsToBipartite G n) := by
  use n.choose 2
  simp only [upperBounds, Set.mem_setOf_eq, subgraphEdgeDistsToBipartite,
    minEdgeDistToBipartite, edgeDistancesToBipartite]
  intro m h
  replace ⟨A, ⟨hn, h_fin, h⟩⟩ := h
  rw [← h]
  have : A.edgeSet.ncard ≤ n.choose 2 := by
    rw [← hn]
    have := h_fin.fintype
    have := Fintype.ofFinite ↑A.coe.edgeSet
    convert (A.coe).card_edgeFinset_le_card_choose_two
    · rw [← Set.ncard_coe_finset A.coe.edgeFinset, coe_edgeFinset A.coe,
        ← Subgraph.image_coe_edgeSet_coe A]
      exact (Set.ncard_image_iff (Set.toFinite A.coe.edgeSet)).mpr <|
        Function.Injective.injOn <| Sym2.map.injective Subtype.coe_injective
    · rw [Set.ncard_eq_toFinset_card _ h_fin, Set.Finite.card_toFinset]
  refine le_trans ?_ this
  apply Nat.sInf_le
  simp only [Subgraph.deleteEdges_verts, exists_prop, Set.mem_setOf_eq]
  use A.edgeSet
  refine ⟨by rfl, ?_, rfl⟩
  use fun _ => 0
  simp

/-! ## ============================ NEW (this campaign) ============================ -/

/-- A subgraph with finitely many vertices has finitely many edges. -/
theorem edgeSet_finite_of_verts_finite {G : SimpleGraph V} (A : G.Subgraph)
    (hf : A.verts.Finite) : A.edgeSet.Finite := by
  haveI := hf.to_subtype
  rw [← Subgraph.image_coe_edgeSet_coe A]
  exact (Set.toFinite _).image _

/-- Deleting no edges changes nothing, in the direction we need. -/
theorem colorable_of_deleteEdges_empty {G : SimpleGraph V} (A : G.Subgraph) (k : ℕ)
    (h : (A.deleteEdges ∅).coe.Colorable k) : A.coe.Colorable k := by
  obtain ⟨c⟩ := h
  refine ⟨SimpleGraph.Coloring.mk (fun v => c v) ?_⟩
  intro u v huv
  refine c.valid ?_
  simp only [Subgraph.coe_adj, Subgraph.deleteEdges_adj, Set.mem_empty_iff_false,
    not_false_eq_true, and_true]
  exact huv

/-- Putting a single edge back into a subgraph at most doubles the number of colours
needed.  (Colour by the old colour paired with "am I the endpoint `x`?".) -/
theorem colorable_of_deleteEdges_singleton {G : SimpleGraph V} (A : G.Subgraph)
    (e : Sym2 V) (k : ℕ) (h : (A.deleteEdges {e}).coe.Colorable k) :
    A.coe.Colorable (k * 2) := by
  classical
  obtain ⟨c⟩ := h
  induction e using Sym2.ind with
  | _ x y =>
    have col : A.coe.Coloring (Fin k × Bool) := by
      refine SimpleGraph.Coloring.mk (fun v => (c v, decide ((v : V) = x))) ?_
      intro u v huv
      have hA : A.Adj (u : V) (v : V) := huv
      have hne : (u : V) ≠ (v : V) := hA.ne
      by_cases hEq : s((u : V), (v : V)) = s(x, y)
      · -- the reinstated edge: exactly one endpoint is `x`
        have hbool : decide ((u : V) = x) ≠ decide ((v : V) = x) := by
          rcases Sym2.eq_iff.mp hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hyx : y ≠ x := fun hh => hne (h1.trans (h2.trans hh).symm)
            rw [h1, h2]; simp [hyx]
          · have hyx : y ≠ x := fun hh => hne ((h1.trans hh).trans h2.symm)
            rw [h1, h2]; simp [hyx]
        simp only [ne_eq, Prod.mk.injEq, not_and]
        exact fun _ => hbool
      · -- an untouched edge: the old colouring already separates
        have hadj : (A.deleteEdges {s(x, y)}).coe.Adj u v := by
          simp only [Subgraph.coe_adj, Subgraph.deleteEdges_adj, Set.mem_singleton_iff]
          exact ⟨hA, hEq⟩
        have hcv := c.valid hadj
        simp only [ne_eq, Prod.mk.injEq, not_and]
        exact fun hc => absurd hc hcv
    simpa using col.colorable

/-- **Defect bound ⇒ uniform colouring bound.**  If `A` becomes bipartite after
deleting a set of at most `n` edges, then `A` is `2 ^ (n + 1)`-colourable. -/
theorem colorable_of_defect {G : SimpleGraph V} :
    ∀ (n : ℕ) (A : G.Subgraph) (E : Set (Sym2 V)), E.Finite → E.ncard ≤ n →
      IsBipartite (A.deleteEdges E).coe → A.coe.Colorable (2 ^ (n + 1)) := by
  intro n
  induction n with
  | zero =>
      intro A E hEfin hcard hbip
      have hE : E = ∅ := by
        rw [← Set.ncard_eq_zero hEfin]
        omega
      subst hE
      simpa using colorable_of_deleteEdges_empty A 2 hbip
  | succ n ih =>
      intro A E hEfin hcard hbip
      rcases Set.eq_empty_or_nonempty E with rfl | ⟨e, he⟩
      · have h2 : A.coe.Colorable 2 := colorable_of_deleteEdges_empty A 2 hbip
        refine h2.mono ?_
        have hp : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
        have h1 : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      · have hE'fin : (E \ {e}).Finite := hEfin.diff
        have hE'card : (E \ {e}).ncard ≤ n := by
          have := Set.ncard_diff_singleton_add_one he hEfin
          omega
        have hunion : {e} ∪ (E \ {e}) = E := by
          ext z
          simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_diff]
          constructor
          · rintro (rfl | ⟨hz, -⟩)
            · exact he
            · exact hz
          · intro hz
            by_cases hze : z = e
            · exact Or.inl hze
            · exact Or.inr ⟨hz, hze⟩
        have hbip' : IsBipartite ((A.deleteEdges {e}).deleteEdges (E \ {e})).coe := by
          rw [Subgraph.deleteEdges_deleteEdges, hunion]
          exact hbip
        have hstep := ih (A.deleteEdges {e}) (E \ {e}) hE'fin hE'card hbip'
        have := colorable_of_deleteEdges_singleton A e _ hstep
        have harith : 2 ^ (n + 1) * 2 = 2 ^ (n + 1 + 1) := by ring
        rwa [harith] at this

/-- The infimum defining `minEdgeDistToBipartite` is attained. -/
theorem exists_witness {G : SimpleGraph V} (A : G.Subgraph) :
    ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧ IsBipartite (A.deleteEdges E).coe ∧
      E.ncard = minEdgeDistToBipartite A := by
  have hmem := Nat.sInf_mem (edgeDistancesToBipartite_nonempty A)
  obtain ⟨E, hEsub, hEbip, hEcard⟩ := hmem
  exact ⟨E, hEsub, hEbip, hEcard⟩

/-- Every finite subgraph of a graph with bounded bipartite defect is uniformly
colourable, with a bound depending only on the defect bound. -/
theorem colorable_finite_subgraph_of_bounded {G : SimpleGraph V} (B : ℕ)
    (hB : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ B)
    (A : G.Subgraph) (hfin : A.verts.Finite) :
    A.coe.Colorable (2 ^ (B + 1)) := by
  obtain ⟨E, hEsub, hEbip, hEcard⟩ := exists_witness A
  have hEfin : E.Finite := (edgeSet_finite_of_verts_finite A hfin).subset hEsub
  have hmem : minEdgeDistToBipartite A ∈ subgraphEdgeDistsToBipartite G A.verts.ncard :=
    ⟨A, rfl, hfin, rfl⟩
  have hle : minEdgeDistToBipartite A ≤ maxSubgraphEdgeDistToBipartite G A.verts.ncard :=
    le_csSup (subgraphEdgeDistsToBipartite_bddAbove G _) hmem
  have hcard : E.ncard ≤ B := by
    rw [hEcard]
    exact hle.trans (hB _)
  exact colorable_of_defect B A E hEfin hcard hEbip

/-! ### Main theorem -/

/-- **MAIN.**  If the bipartite-defect function of `G` is bounded by `B`, then `G`
has chromatic number at most `2 ^ (B + 1)`; in particular it is finite.

Proof: every finite subgraph is `2 ^ (B + 1)`-colourable, then de Bruijn–Erdős
compactness (`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`). -/
theorem colorable_of_bounded_defect {G : SimpleGraph V} (B : ℕ)
    (hB : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ B) :
    G.Colorable (2 ^ (B + 1)) := by
  have h : ∀ A : G.Subgraph, A.verts.Finite →
      A.coe →g (completeGraph (Fin (2 ^ (B + 1)))) := by
    intro A hfin
    exact (colorable_finite_subgraph_of_bounded B hB A hfin).some
  exact SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom h

/-- **MAIN (chromatic number form).** -/
theorem chromaticNumber_le_of_bounded_defect {G : SimpleGraph V} (B : ℕ)
    (hB : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ B) :
    G.chromaticNumber ≤ (2 ^ (B + 1) : ℕ) :=
  (colorable_of_bounded_defect B hB).chromaticNumber_le

/-- **MAIN (contrapositive).**  A graph of infinite chromatic number has unbounded
bipartite-defect function.  This is the rate-free half of Erdős 74: it says the
defect function must go to infinity, but says nothing about *how fast*, which is
exactly what the open problem asks. -/
theorem exists_defect_gt_of_chromaticNumber_top {G : SimpleGraph V}
    (h : G.chromaticNumber = ⊤) (B : ℕ) :
    ∃ n, B < maxSubgraphEdgeDistToBipartite G n := by
  by_contra hcon
  push_neg at hcon
  have hle := chromaticNumber_le_of_bounded_defect B hcon
  rw [h] at hle
  exact absurd (top_le_iff.mp hle) (by simp)

/-- **COROLLARY: the hypothesis `f → ∞` in Erdős 74 is necessary.**  For a bounded
`f` there is unconditionally *no* graph of infinite chromatic number all of whose
`n`-vertex subgraphs are within `f n` edges of bipartite.  So the answer to the
Erdős 74 question is NO for every bounded `f`, and the interest of the problem lies
entirely in how slowly an unbounded `f` may grow. -/
theorem no_graph_for_bounded_f (f : ℕ → ℕ) (B : ℕ) (hf : ∀ n, f n ≤ B) :
    ¬ ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n := by
  rintro ⟨V, G, hchi, hbd⟩
  obtain ⟨n, hn⟩ := exists_defect_gt_of_chromaticNumber_top hchi B
  exact absurd ((hbd n).trans (hf n)) (by omega)

/-- Restated against the shape of `Erdos74.erdos_74`: a witness family for a bounded
`f` cannot exist, so `Tendsto f atTop atTop` cannot be dropped from that statement. -/
theorem erdos74_hypothesis_sharp (f : ℕ → ℕ) (hf : ¬ Tendsto f atTop atTop)
    (hmono : ∀ m n, m ≤ n → f m ≤ f n) :
    ∃ B, (∀ n, f n ≤ B) ∧
      ¬ ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n := by
  -- a monotone `ℕ → ℕ` that does not tend to infinity is bounded
  have hbdd : ∃ B, ∀ n, f n ≤ B := by
    by_contra hcon
    push_neg at hcon
    exact hf (tendsto_atTop_atTop.mpr (by
      intro b
      obtain ⟨n, hn⟩ := hcon b
      exact ⟨n, fun m hm => le_trans hn.le (hmono n m hm)⟩))
  obtain ⟨B, hB⟩ := hbdd
  exact ⟨B, hB, no_graph_for_bounded_f f B hB⟩

/-! ## Calibration and formalisation audit

A theorem about a defect function that is secretly identically zero would be
worthless.  This section proves the machinery is calibrated, and isolates a real
definitional hazard in the transcribed definitions. -/

/-- Deleting edges cannot increase the number of colours needed. -/
theorem colorable_deleteEdges_of_colorable {G : SimpleGraph V} (A : G.Subgraph)
    (E : Set (Sym2 V)) (k : ℕ) (h : A.coe.Colorable k) :
    (A.deleteEdges E).coe.Colorable k := by
  obtain ⟨c⟩ := h
  refine ⟨SimpleGraph.Coloring.mk (fun v => c v) ?_⟩
  intro u v huv
  refine c.valid ?_
  simp only [Subgraph.coe_adj, Subgraph.deleteEdges_adj] at huv
  exact huv.1

/-- **CALIBRATION.**  On the domain the problem actually uses (subgraphs with
finitely many vertices) the defect is zero exactly for the bipartite subgraphs.
So `maxSubgraphEdgeDistToBipartite` really does measure distance to bipartite,
and the hypothesis of the main theorem is a genuine constraint. -/
theorem minEdgeDistToBipartite_eq_zero_iff {G : SimpleGraph V} (A : G.Subgraph)
    (hfin : A.verts.Finite) :
    minEdgeDistToBipartite A = 0 ↔ IsBipartite A.coe := by
  constructor
  · intro h
    obtain ⟨E, hEsub, hEbip, hEcard⟩ := exists_witness A
    have hEfin : E.Finite := (edgeSet_finite_of_verts_finite A hfin).subset hEsub
    have hE : E = ∅ := by
      rw [← Set.ncard_eq_zero hEfin, hEcard, h]
    subst hE
    exact colorable_of_deleteEdges_empty A 2 hEbip
  · intro h
    have hmem : (0 : ℕ) ∈ edgeDistancesToBipartite A := by
      refine ⟨∅, by simp, ?_, by simp⟩
      exact colorable_deleteEdges_of_colorable A ∅ 2 h
    exact Nat.le_zero.mp (Nat.sInf_le hmem)

/-- **AUDIT FINDING (the `Set.ncard` hazard).**  `Set.ncard` of an infinite set is
`0`.  So on a subgraph with infinitely many edges, `minEdgeDistToBipartite` collapses
to `0` even when the subgraph is very far from bipartite: witness the complete graph
on `ℕ`, which is not bipartite yet has defect `0`.

Consequence: the `A.verts.Finite` guard inside `subgraphEdgeDistsToBipartite` is
LOAD-BEARING, not cosmetic.  Without it, `maxSubgraphEdgeDistToBipartite` would be
identically `0` for every graph with an infinite edge set and the whole statement of
Erdős 74 would trivialise.  The formal-conjectures file does carry that guard, so its
statement is sound; this lemma records *why* the guard cannot be removed. -/
theorem ncard_hazard_infinite_edgeSet :
    ¬ IsBipartite (⊤ : (⊤ : SimpleGraph ℕ).Subgraph).coe ∧
      minEdgeDistToBipartite (⊤ : (⊤ : SimpleGraph ℕ).Subgraph) = 0 := by
  constructor
  · rintro ⟨c⟩
    have hadj : ∀ a b : ℕ, a ≠ b →
        (⊤ : (⊤ : SimpleGraph ℕ).Subgraph).coe.Adj ⟨a, trivial⟩ ⟨b, trivial⟩ := by
      intro a b hab
      simp [Subgraph.coe_adj, hab]
    have h01 := c.valid (hadj 0 1 (by norm_num))
    have h02 := c.valid (hadj 0 2 (by norm_num))
    have h12 := c.valid (hadj 1 2 (by norm_num))
    have v0 := (c ⟨0, trivial⟩).isLt
    have v1 := (c ⟨1, trivial⟩).isLt
    have v2 := (c ⟨2, trivial⟩).isLt
    have n01 : (c ⟨0, trivial⟩).val ≠ (c ⟨1, trivial⟩).val := fun h => h01 (Fin.ext h)
    have n02 : (c ⟨0, trivial⟩).val ≠ (c ⟨2, trivial⟩).val := fun h => h02 (Fin.ext h)
    have n12 : (c ⟨1, trivial⟩).val ≠ (c ⟨2, trivial⟩).val := fun h => h12 (Fin.ext h)
    omega
  · -- delete the whole (infinite) edge set: `ncard` reports `0`
    refine Nat.le_zero.mp (Nat.sInf_le ?_)
    refine ⟨(⊤ : (⊤ : SimpleGraph ℕ).Subgraph).edgeSet, subset_rfl, ?_, ?_⟩
    · use fun _ => 0
      simp
    · rw [Set.Infinite.ncard]
      apply Set.Infinite.mono (s := (fun n => s(0, n + 1)) '' Set.univ)
      · rintro _ ⟨n, -, rfl⟩
        simp [Subgraph.mem_edgeSet]
      · apply Set.Infinite.image
        · intro a _ b _ hab
          simpa [Sym2.eq_iff] using hab
        · exact Set.infinite_univ

end Erdos74Close
