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
    val scc_def : thm
    val scc_set_def : thm
    val single_child_ancestors_primitive_def : thm
    val single_child_parents_def : thm
    val sum_scc_parents_def : thm

  (*  Theorems  *)
    val single_child_ancestors_def : thm
    val single_child_ancestors_def_1 : thm
    val single_child_ancestors_def_2 : thm
    val single_child_ancestors_def_2_1 : thm
    val single_child_ancestors_ind : thm

  val SCCGraphPlanTheorem_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [GraphPlanTheorem] Parent theory of "SCCGraphPlanTheorem"

   [ancestors_def]  Definition

      |- ∀PROB vs.
           ancestors (PROB,vs) =
           {v |
            (∃v'. v' ∈ vs ∧ dep_tc PROB v v') ∧
            ∀v'. v' ∈ vs ⇒ ¬dep_tc PROB v' v}

   [childless_problem_scc_set_def]  Definition

      |- ∀PROB.
           childless_problem_scc_set PROB =
           {vs | scc (PROB,vs) ∧ childless_vs (PROB,vs)}

   [childless_svs_def]  Definition

      |- ∀PROB S.
           childless_svs (PROB,S) ⇔ ∀vs. vs ∈ S ⇒ childless_vs (PROB,vs)

   [childless_vs_def]  Definition

      |- ∀PROB vs.
           childless_vs (PROB,vs) ⇔
           ∀vs'. DISJOINT vs vs' ⇒ ¬dep_var_set (PROB,vs,vs')

   [dep_tc_def]  Definition

      |- ∀PROB. dep_tc PROB = (λv1' v2'. dep (PROB,v1',v2'))⁺

   [member_leaves_def]  Definition

      |- ∀PROB S.
           member_leaves (PROB,S) =
           FILTER (λvs. scc (PROB,vs) ∧ childless_vs (PROB,vs))
             (SET_TO_LIST S)

   [scc_def]  Definition

      |- ∀PROB vs.
           scc (PROB,vs) ⇔
           (∀v1 v2.
              v1 ∈ vs ∧ v2 ∈ vs ⇒ dep_tc PROB v1 v2 ∧ dep_tc PROB v2 v1) ∧
           ∀vs'.
             DISJOINT vs' vs ⇒
             ¬dep_var_set (PROB,vs,vs') ∨ ¬dep_var_set (PROB,vs',vs)

   [scc_set_def]  Definition

      |- ∀PROB S.
           scc_set (PROB,S) ⇔
           ∀vs. vs ∈ S ∧ vs ⊆ FDOM PROB.I ⇒ scc (PROB,vs)

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
            scc (PROB,vs')}

   [sum_scc_parents_def]  Definition

      |- ∀PROB S.
           sum_scc_parents (PROB,S) =
           ∑
             (λvs.
                problem_plan_bound
                  (prob_proj (PROB,vs ∪ ancestors (PROB,vs)))) S

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
