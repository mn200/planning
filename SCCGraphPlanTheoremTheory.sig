signature SCCGraphPlanTheoremTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ancestors_def : thm
    val childless_problem_scc_set_def : thm
    val childless_svs_def : thm
    val childless_vs_def : thm
    val dep_tc_def : thm
    val member_leaves_def : thm
    val problem_scc_set_def : thm
    val problem_wo_vs_ancestors_def : thm
    val scc_set_def : thm
    val scc_vs_def : thm
    val single_child_ancestors_primitive_def : thm
    val single_child_parents_def : thm
    val sum_scc_parents_def : thm

  (*  Theorems  *)
    val scc_lemma_1_1 : thm
    val scc_lemma_1_2 : thm
    val scc_lemma_1_3 : thm
    val scc_lemma_1_4 : thm
    val scc_lemma_1_4_1 : thm
    val scc_lemma_1_4_1_1 : thm
    val scc_lemma_1_4_2 : thm
    val scc_lemma_1_4_3 : thm
    val scc_lemma_1_4_4 : thm
    val scc_lemma_1_4_5 : thm
    val scc_lemma_1_5 : thm
    val scc_main_lemma : thm
    val scc_main_lemma_1 : thm
    val scc_main_lemma_1_1 : thm
    val scc_main_lemma_1_1_1 : thm
    val scc_main_lemma_1_1_1_1 : thm
    val scc_main_lemma_1_1_1_1_1 : thm
    val scc_main_lemma_1_1_1_1_1_1 : thm
    val scc_main_lemma_1_1_1_2 : thm
    val scc_main_lemma_1_2 : thm
    val scc_main_lemma_1_2_1 : thm
    val scc_main_lemma_1_2_2 : thm
    val scc_main_lemma_1_2_2_1 : thm
    val scc_main_lemma_1_2_2_2 : thm
    val scc_main_lemma_1_2_2_3 : thm
    val scc_main_lemma_1_2_2_4 : thm
    val scc_main_lemma_1_3 : thm
    val scc_main_lemma_1_4 : thm
    val scc_main_lemma_1_5 : thm
    val scc_main_lemma_1_6 : thm
    val scc_main_lemma_1_7 : thm
    val scc_main_lemma_1_xx : thm
    val scc_main_lemma_x : thm
    val single_child_ancestors_def : thm
    val single_child_ancestors_def_1 : thm
    val single_child_ancestors_def_2 : thm
    val single_child_ancestors_def_2_1 : thm
    val single_child_ancestors_ind : thm

  val SCCGraphPlanTheorem_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [GraphPlanTheorem] Parent theory of "SCCGraphPlanTheorem"

   [SCC] Parent theory of "SCCGraphPlanTheorem"

   [ancestors_def]  Definition

      |- ∀PROB vs.
           ancestors (PROB,vs) =
           {v |
            (∃v'. v' ∈ vs ∧ dep_tc PROB v v') ∧
            ∀v'. v' ∈ vs ⇒ ¬dep_tc PROB v' v}

   [childless_problem_scc_set_def]  Definition

      |- ∀PROB.
           childless_problem_scc_set PROB =
           {vs | scc_vs (PROB,vs) ∧ childless_vs (PROB,vs)}

   [childless_svs_def]  Definition

      |- ∀PROB S.
           childless_svs (PROB,S) ⇔ ∀vs. vs ∈ S ⇒ childless_vs (PROB,vs)

   [childless_vs_def]  Definition

      |- ∀PROB vs.
           childless_vs (PROB,vs) ⇔ ∀vs'. ¬dep_var_set (PROB,vs,vs')

   [dep_tc_def]  Definition

      |- ∀PROB. dep_tc PROB = (λv1' v2'. dep (PROB,v1',v2'))⁺

   [member_leaves_def]  Definition

      |- ∀PROB S.
           member_leaves (PROB,S) =
           (λvs. scc_vs (PROB,vs) ∧ childless_vs (PROB,vs)) ∩ S

   [problem_scc_set_def]  Definition

      |- ∀PROB. problem_scc_set PROB = {vs | scc_vs (PROB,vs)}

   [problem_wo_vs_ancestors_def]  Definition

      |- ∀PROB vs.
           problem_wo_vs_ancestors (PROB,vs) =
           prob_proj
             (PROB,
              FDOM PROB.I DIFF
              (vs ∪ BIGUNION (single_child_ancestors (PROB,vs))))

   [scc_set_def]  Definition

      |- ∀PROB S.
           scc_set (PROB,S) ⇔
           ∀vs. vs ∈ S ∧ ¬DISJOINT vs (FDOM PROB.I) ⇒ scc_vs (PROB,vs)

   [scc_vs_def]  Definition

      |- ∀PROB vs. scc_vs (PROB,vs) ⇔ SCC (λv1' v2'. dep (PROB,v1',v2')) vs

   [single_child_ancestors_primitive_def]  Definition

      |- single_child_ancestors =
         WFREC
           (@R.
              WF R ∧
              ∀PROB vs vs'.
                (vs ⊆ FDOM PROB.I ∧ vs ≠ ∅) ∧
                vs' ∈ single_child_parents (PROB,vs) ⇒
                R (prob_proj (PROB,FDOM PROB.I DIFF vs),vs') (PROB,vs))
           (λsingle_child_ancestors a.
              case a of
                (PROB,vs) =>
                  I
                    (if vs ⊆ FDOM PROB.I ∧ vs ≠ ∅ then
                       single_child_parents (PROB,vs) ∪
                       BIGUNION
                         (IMAGE
                            (λvs'.
                               single_child_ancestors
                                 (prob_proj (PROB,FDOM PROB.I DIFF vs),
                                  vs')) (single_child_parents (PROB,vs)))
                     else ∅))

   [single_child_parents_def]  Definition

      |- ∀PROB vs.
           single_child_parents (PROB,vs) =
           {vs' |
            vs' ⊆ ancestors (PROB,vs) ∧
            childless_vs (prob_proj (PROB,FDOM PROB.I DIFF vs),vs') ∧
            scc_vs (PROB,vs')}

   [sum_scc_parents_def]  Definition

      |- ∀PROB S.
           sum_scc_parents (PROB,S) =
           ∑
             (λvs.
                problem_plan_bound
                  (prob_proj (PROB,vs ∪ ancestors (PROB,vs)))) S + 1

   [scc_lemma_1_1]  Theorem

      |- ∀PROB S. FINITE S ⇒ FINITE (member_leaves (PROB,S))

   [scc_lemma_1_2]  Theorem

      |- ∀PROB vs S. vs ∈ member_leaves (PROB,S) ⇒ scc_vs (PROB,vs)

   [scc_lemma_1_3]  Theorem

      |- ∀PROB vs S. vs ∈ member_leaves (PROB,S) ⇒ vs ∈ S

   [scc_lemma_1_4]  Theorem

      [oracles: tactic_failed] [axioms: ] []
      |- ∀S.
           FINITE S ⇒
           ∀PROB vs S'.
             (member_leaves (PROB,S) = vs INSERT S') ⇒
             (member_leaves (problem_wo_vs_ancestors (PROB,vs),S) = S')

   [scc_lemma_1_4_1]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀PROB vs vs'.
           childless_vs (PROB,vs') ∧ DISJOINT vs vs' ⇒
           DISJOINT vs' (BIGUNION (single_child_ancestors (PROB,vs)))

   [scc_lemma_1_4_1_1]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs vs'.
           childless_vs (PROB,vs') ∧ DISJOINT vs vs' ⇒
           ∀vs''.
             vs'' ∈ single_child_ancestors (PROB,vs) ⇒ DISJOINT vs' vs''

   [scc_lemma_1_4_2]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs S vs'.
           DISJOINT vs vs' ∧ vs' ∈ member_leaves (PROB,S) ⇒
           vs' ∈ member_leaves (prob_proj (PROB,FDOM PROB.I DIFF vs),S)

   [scc_lemma_1_4_3]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs vs' S.
           vs ⊆ vs' ⇒ vs ∉ childless_problem_scc_set (prob_proj (PROB,vs))

   [scc_lemma_1_4_4]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB S.
           vs ⊆ vs' ⇒ vs ∉ childless_problem_scc_set (prob_proj (PROB,vs))

   [scc_lemma_1_4_5]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs vs'.
           scc_vs (PROB,vs) ∧ scc_vs (PROB,vs') ∧ vs ≠ vs' ⇒
           DISJOINT vs vs'

   [scc_lemma_1_5]  Theorem

      |- ∀PROB vs S. vs ∈ member_leaves (PROB,S) ⇒ childless_vs (PROB,vs)

   [scc_main_lemma]  Theorem

      [oracles: DISK_THM, cheat, tactic_failed] [axioms: ] []
      |- ∀S PROB.
           planning_problem PROB ∧ scc_set (PROB,S) ∧
           FDOM PROB.I ⊆ BIGUNION S ∧ BIGUNION S ≠ ∅ ∧ FINITE S ⇒
           problem_plan_bound PROB ≤
           sum_scc_parents (PROB,member_leaves (PROB,S))

   [scc_main_lemma_1]  Theorem

      [oracles: DISK_THM, cheat, tactic_failed] [axioms: ] []
      |- ∀s.
           FINITE s ⇒
           ∀S PROB.
             planning_problem PROB ∧ scc_set (PROB,S) ∧
             FDOM PROB.I ⊆ BIGUNION S ∧ (S ≠ ∅ ∧ S ≠ {∅}) ∧ FINITE S ∧
             (s = member_leaves (PROB,S)) ⇒
             problem_plan_bound PROB ≤
             sum_scc_parents (PROB,member_leaves (PROB,S))

   [scc_main_lemma_1_1]  Theorem

      |- ∀PROB S.
           planning_problem PROB ∧ FDOM PROB.I ⊆ BIGUNION S ∧
           scc_set (PROB,S) ⇒
           (childless_problem_scc_set PROB = member_leaves (PROB,S))

   [scc_main_lemma_1_1_1]  Theorem

      |- ∀PROB S vs.
           planning_problem PROB ∧ FDOM PROB.I ⊆ BIGUNION S ∧
           scc_set (PROB,S) ∧ scc_vs (PROB,vs) ⇒
           vs ∈ S

   [scc_main_lemma_1_1_1_1]  Theorem

      |- ∀PROB vs.
           planning_problem PROB ∧ scc_vs (PROB,vs) ⇒ vs ⊆ FDOM PROB.I

   [scc_main_lemma_1_1_1_1_1]  Theorem

      |- ∀PROB v1 v2.
           planning_problem PROB ∧ dep_tc PROB v1 v2 ⇒ v1 ∈ FDOM PROB.I

   [scc_main_lemma_1_1_1_1_1_1]  Theorem

      |- ∀PROB v1 v2.
           planning_problem PROB ∧ dep (PROB,v1,v2) ⇒
           v1 ∈ FDOM PROB.I ∧ v2 ∈ FDOM PROB.I

   [scc_main_lemma_1_1_1_2]  Theorem

      |- ∀PROB vs vs'.
           ¬DISJOINT vs vs' ∧ scc_vs (PROB,vs) ∧ scc_vs (PROB,vs') ⇒
           (vs = vs')

   [scc_main_lemma_1_2]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀PROB.
           planning_problem PROB ⇒
           ((FDOM PROB.I = ∅) ⇔ (childless_problem_scc_set PROB = ∅))

   [scc_main_lemma_1_2_1]  Theorem

      |- ∀PROB.
           planning_problem PROB ⇒
           (FDOM PROB.I = ∅) ⇒
           ∀vs. ¬scc_vs (PROB,vs)

   [scc_main_lemma_1_2_2]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB.
           planning_problem PROB ∧ FDOM PROB.I ≠ ∅ ⇒
           ∃vs. scc_vs (PROB,vs) ∧ childless_vs (PROB,vs)

   [scc_main_lemma_1_2_2_1]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB.
           StrongOrder
             (REL_RESTRICT (λvs1 vs2. dep_var_set (PROB,vs2,vs1))⁺
                (problem_scc_set PROB))

   [scc_main_lemma_1_2_2_2]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB. FINITE (problem_scc_set PROB)

   [scc_main_lemma_1_2_2_3]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB.
           FDOM PROB.I ≠ ∅ ∧ planning_problem PROB ⇒ ∃vs. scc_vs (PROB,vs)

   [scc_main_lemma_1_2_2_4]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀R s min.
           (∀x. REL_RESTRICT R⁺ s x min ⇒ x ∉ s) ⇒ ∀x'. x' ∈ s ⇒ ¬R x' min

   [scc_main_lemma_1_3]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB S S'.
           scc_set (PROB,S) ∧ S' ⊆ S ⇒
           scc_set (prob_proj (PROB,FDOM PROB.I DIFF BIGUNION S'),S)

   [scc_main_lemma_1_4]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs S.
           scc_set (PROB,S) ∧ scc_vs (PROB,vs) ∧ FDOM PROB.I ⊆ BIGUNION S ⇒
           single_child_ancestors (PROB,vs) ⊆ S

   [scc_main_lemma_1_5]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs vs'.
           FDOM PROB.I ⊆ vs ⇒ FDOM (prob_proj (PROB,vs')).I ⊆ vs

   [scc_main_lemma_1_6]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs S S'.
           (member_leaves (PROB,S) = vs INSERT S') ∧ vs ∉ S' ⇒
           (sum_scc_parents
              (problem_wo_vs_ancestors (PROB,vs),
               member_leaves (problem_wo_vs_ancestors (PROB,vs),S)) =
            sum_scc_parents (PROB,S'))

   [scc_main_lemma_1_7]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀PROB vs.
           childless_vs (PROB,vs) ∧ scc_vs (PROB,vs) ⇒
           problem_plan_bound PROB ≤
           problem_plan_bound (problem_wo_vs_ancestors (PROB,vs)) +
           problem_plan_bound (prob_proj (PROB,vs ∪ ancestors (PROB,vs)))

   [scc_main_lemma_1_xx]  Theorem

      |- ∀PROB vs vs'.
           scc_vs (PROB,vs) ∧ scc_vs (PROB,vs') ∧ vs ≠ vs' ⇒
           DISJOINT vs vs'

   [scc_main_lemma_x]  Theorem

      |- ∀s t x. x ∈ s ∧ x ∉ t ⇒ s ≠ t

   [single_child_ancestors_def]  Theorem

      |- ∀vs PROB.
           single_child_ancestors (PROB,vs) =
           if vs ⊆ FDOM PROB.I ∧ vs ≠ ∅ then
             single_child_parents (PROB,vs) ∪
             BIGUNION
               (IMAGE
                  (λvs'.
                     single_child_ancestors
                       (prob_proj (PROB,FDOM PROB.I DIFF vs),vs'))
                  (single_child_parents (PROB,vs)))
           else ∅

   [single_child_ancestors_def_1]  Theorem

      [oracles: cheat] [axioms: ] []
      |- WF (λx y. CARD (FDOM (FST x).I) < CARD (FDOM (FST y).I))

   [single_child_ancestors_def_2]  Theorem

      |- ∀PROB vs vs'.
           vs ⊆ FDOM PROB.I ∧ vs ≠ ∅ ⇒
           CARD (FDOM (prob_proj (PROB,FDOM PROB.I DIFF vs)).I) <
           CARD (FDOM PROB.I)

   [single_child_ancestors_def_2_1]  Theorem

      |- ∀s t. FINITE s ∧ FINITE t ∧ s ⊆ t ⇒ (t ∩ (t DIFF s) = t DIFF s)

   [single_child_ancestors_ind]  Theorem

      |- ∀P.
           (∀PROB vs.
              (∀vs'.
                 (vs ⊆ FDOM PROB.I ∧ vs ≠ ∅) ∧
                 vs' ∈ single_child_parents (PROB,vs) ⇒
                 P (prob_proj (PROB,FDOM PROB.I DIFF vs),vs')) ⇒
              P (PROB,vs)) ⇒
           ∀v v1. P (v,v1)


*)
end
