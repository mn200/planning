signature GraphPlanTheoremTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val MPLS_def : thm
    val PLS_def : thm
    val action_proj_def : thm
    val as_proj_child_def : thm
    val as_proj_parent_def : thm
    val as_proj_primitive_def : thm
    val child_parent_rel_def : thm
    val dep_def : thm
    val dep_var_set_def : thm
    val list_frag_def : thm
    val list_frag_rec_primitive_def : thm
    val no_effectless_act_def : thm
    val prob_proj_def : thm
    val problem_plan_bound_def : thm
    val rem_condless_act_primitive_def : thm
    val rem_effectless_act_def : thm
    val replace_projected_primitive_def : thm
    val sat_precond_as_primitive_def : thm
    val varset_action_def : thm

  (*  Theorems  *)
    val as_proj_def : thm
    val as_proj_ind : thm
    val bound_child_parent_lemma : thm
    val bound_child_parent_lemma_1 : thm
    val bound_child_parent_lemma_1_1 : thm
    val bound_child_parent_lemma_1_1_1 : thm
    val bound_child_parent_lemma_1_1_1_1 : thm
    val bound_child_parent_lemma_1_1_1_1_1 : thm
    val bound_child_parent_lemma_1_1_1_1_1_1 : thm
    val bound_child_parent_lemma_1_1_1_1_1_1_1 : thm
    val bound_child_parent_lemma_1_1_1_1_1_2 : thm
    val bound_child_parent_lemma_1_1_1_1_1_2_1 : thm
    val bound_child_parent_lemma_1_1_1_1_1_3 : thm
    val bound_child_parent_lemma_1_1_1_1_2 : thm
    val bound_child_parent_lemma_1_1_1_1_3 : thm
    val bound_child_parent_lemma_1_1_1_2 : thm
    val bound_child_parent_lemma_1_1_1_2_1 : thm
    val bound_child_parent_lemma_1_1_1_2_1_1 : thm
    val bound_child_parent_lemma_1_1_1_3 : thm
    val bound_child_parent_lemma_1_1_1_3_1 : thm
    val bound_child_parent_lemma_1_1_1_3_1_1 : thm
    val bound_child_parent_lemma_1_1_1_3_1_1_1 : thm
    val bound_child_parent_lemma_1_1_1_3_1_2 : thm
    val bound_child_parent_lemma_1_1_1_3_1_3 : thm
    val bound_child_parent_lemma_1_1_1_3_1_4 : thm
    val bound_child_parent_lemma_1_1_1_3_1_4_1 : thm
    val bound_child_parent_lemma_1_1_1_4 : thm
    val bound_child_parent_lemma_1_1_1_4_1 : thm
    val bound_child_parent_lemma_1_1_1_4_1_1 : thm
    val bound_child_parent_lemma_1_1_1_4_1_2 : thm
    val bound_child_parent_lemma_1_1_1_4_2 : thm
    val bound_child_parent_lemma_1_1_1_4_2_1 : thm
    val bound_child_parent_lemma_1_1_1_4_3 : thm
    val bound_child_parent_lemma_1_1_2 : thm
    val bound_child_parent_lemma_1_1_2_4 : thm
    val bound_child_parent_lemma_1_1_2_4_1 : thm
    val bound_child_parent_lemma_1_1_2_4_1_1 : thm
    val bound_child_parent_lemma_1_1_2_5 : thm
    val bound_child_parent_lemma_1_1_3 : thm
    val bound_child_parent_lemma_1_1_3_1 : thm
    val bound_child_parent_lemma_2 : thm
    val bound_child_parent_lemma_2_1 : thm
    val bound_child_parent_lemma_2_1_1 : thm
    val bound_child_parent_lemma_2_1_2 : thm
    val bound_child_parent_lemma_2_2 : thm
    val bound_child_parent_lemma_2_2_1 : thm
    val bound_child_parent_lemma_3 : thm
    val bound_child_parent_lemma_4 : thm
    val bound_main_lemma : thm
    val bound_main_lemma_1 : thm
    val bound_main_lemma_1_1 : thm
    val bound_main_lemma_1_2 : thm
    val bound_main_lemma_2 : thm
    val bound_main_lemma_2_1 : thm
    val bound_main_lemma_3 : thm
    val child_parent_lemma_1 : thm
    val child_parent_lemma_1_1 : thm
    val child_parent_lemma_1_1_1 : thm
    val child_parent_lemma_1_1_2 : thm
    val child_parent_lemma_1_2 : thm
    val child_parent_lemma_1_2_1 : thm
    val child_parent_lemma_1_2_1_1 : thm
    val child_parent_lemma_1_3_1 : thm
    val child_parent_lemma_1_4_1 : thm
    val child_parent_lemma_1_5_1 : thm
    val child_parent_lemma_2_1 : thm
    val child_parent_lemma_2_1_1 : thm
    val child_parent_lemma_2_1_1_1 : thm
    val child_parent_lemma_2_1_1_1_1 : thm
    val child_parent_lemma_2_1_1_1_1_1 : thm
    val child_parent_lemma_2_1_1_1_2 : thm
    val child_parent_lemma_2_1_1_1_3 : thm
    val child_parent_lemma_2_1_1_1_3_1 : thm
    val child_parent_lemma_2_1_1_1_3_1_1 : thm
    val child_parent_lemma_2_1_1_2 : thm
    val child_parent_lemma_2_1_2 : thm
    val child_parent_lemma_2_1_2_1 : thm
    val child_parent_lemma_2_1_2_2 : thm
    val child_parent_lemma_2_1_2_2_2 : thm
    val child_parent_lemma_2_1_2_3 : thm
    val child_parent_lemma_2_1_2_4 : thm
    val child_parent_lemma_2_1_3 : thm
    val child_parent_lemma_2_1_3_1 : thm
    val child_parent_lemma_2_1_3_1_1 : thm
    val child_parent_lemma_2_1_3_1_1_1 : thm
    val child_parent_lemma_2_1_3_1_1_1_1 : thm
    val child_parent_lemma_2_1_3_1_1_2 : thm
    val child_parent_lemma_xx : thm
    val child_parent_lemma_xxx : thm
    val child_parent_lemma_xxxx : thm
    val child_parent_lemma_xxxxx : thm
    val child_parent_lemma_xxxxxx : thm
    val graph_plan_lemma_1 : thm
    val graph_plan_lemma_10 : thm
    val graph_plan_lemma_10_1 : thm
    val graph_plan_lemma_11 : thm
    val graph_plan_lemma_12 : thm
    val graph_plan_lemma_12_1 : thm
    val graph_plan_lemma_12_2 : thm
    val graph_plan_lemma_12_3 : thm
    val graph_plan_lemma_12_4 : thm
    val graph_plan_lemma_13 : thm
    val graph_plan_lemma_14 : thm
    val graph_plan_lemma_14_1 : thm
    val graph_plan_lemma_14_2 : thm
    val graph_plan_lemma_15 : thm
    val graph_plan_lemma_15_1 : thm
    val graph_plan_lemma_15_2 : thm
    val graph_plan_lemma_16 : thm
    val graph_plan_lemma_16_1 : thm
    val graph_plan_lemma_16_10 : thm
    val graph_plan_lemma_16_11 : thm
    val graph_plan_lemma_16_12 : thm
    val graph_plan_lemma_16_1_1 : thm
    val graph_plan_lemma_16_2 : thm
    val graph_plan_lemma_16_3 : thm
    val graph_plan_lemma_16_4 : thm
    val graph_plan_lemma_16_5 : thm
    val graph_plan_lemma_16_6 : thm
    val graph_plan_lemma_16_7 : thm
    val graph_plan_lemma_16_8 : thm
    val graph_plan_lemma_16_9 : thm
    val graph_plan_lemma_17 : thm
    val graph_plan_lemma_18 : thm
    val graph_plan_lemma_18_1 : thm
    val graph_plan_lemma_19 : thm
    val graph_plan_lemma_1_1 : thm
    val graph_plan_lemma_1_1_1 : thm
    val graph_plan_lemma_1_2 : thm
    val graph_plan_lemma_1_2_1 : thm
    val graph_plan_lemma_1_2_2 : thm
    val graph_plan_lemma_1_3 : thm
    val graph_plan_lemma_2 : thm
    val graph_plan_lemma_20 : thm
    val graph_plan_lemma_21 : thm
    val graph_plan_lemma_22_1 : thm
    val graph_plan_lemma_22_2 : thm
    val graph_plan_lemma_22_2_1 : thm
    val graph_plan_lemma_22_3 : thm
    val graph_plan_lemma_22_3_1 : thm
    val graph_plan_lemma_22_4 : thm
    val graph_plan_lemma_23 : thm
    val graph_plan_lemma_23_1 : thm
    val graph_plan_lemma_23_2 : thm
    val graph_plan_lemma_23_3 : thm
    val graph_plan_lemma_2_1 : thm
    val graph_plan_lemma_2_2 : thm
    val graph_plan_lemma_2_3 : thm
    val graph_plan_lemma_2_3_1 : thm
    val graph_plan_lemma_2_3_10 : thm
    val graph_plan_lemma_2_3_11 : thm
    val graph_plan_lemma_2_3_11_1 : thm
    val graph_plan_lemma_2_3_7 : thm
    val graph_plan_lemma_2_3_7_1 : thm
    val graph_plan_lemma_2_3_7_2 : thm
    val graph_plan_lemma_2_3_7_2_1 : thm
    val graph_plan_lemma_2_3_8 : thm
    val graph_plan_lemma_2_3_8_1 : thm
    val graph_plan_lemma_2_3_8_2 : thm
    val graph_plan_lemma_2_3_8_3 : thm
    val graph_plan_lemma_2_3_8_4 : thm
    val graph_plan_lemma_2_3_8_5 : thm
    val graph_plan_lemma_2_3_8_6 : thm
    val graph_plan_lemma_2_3_9 : thm
    val graph_plan_lemma_3 : thm
    val graph_plan_lemma_4 : thm
    val graph_plan_lemma_4_1 : thm
    val graph_plan_lemma_5 : thm
    val graph_plan_lemma_6 : thm
    val graph_plan_lemma_6_1 : thm
    val graph_plan_lemma_6_2 : thm
    val graph_plan_lemma_7 : thm
    val graph_plan_lemma_7_1 : thm
    val graph_plan_lemma_7_1_1 : thm
    val graph_plan_lemma_7_2 : thm
    val graph_plan_lemma_7_2_1 : thm
    val graph_plan_lemma_7_2_1_1 : thm
    val graph_plan_lemma_7_3 : thm
    val graph_plan_lemma_7_4 : thm
    val graph_plan_lemma_7_6 : thm
    val graph_plan_lemma_7_7 : thm
    val graph_plan_lemma_7_8 : thm
    val graph_plan_lemma_7_8_1 : thm
    val graph_plan_lemma_8 : thm
    val graph_plan_lemma_8_1 : thm
    val graph_plan_lemma_8_1_1 : thm
    val graph_plan_lemma_8_2 : thm
    val graph_plan_lemma_9 : thm
    val graph_plan_lemma_9_1 : thm
    val graph_plan_lemma_9_1_1 : thm
    val graph_plan_lemma_9_1_1_1 : thm
    val graph_plan_lemma_9_2 : thm
    val list_frag_rec_def : thm
    val list_frag_rec_ind : thm
    val rem_condless_act_def : thm
    val rem_condless_act_ind : thm
    val replace_projected_def : thm
    val replace_projected_ind : thm
    val sat_precond_as_def : thm
    val sat_precond_as_ind : thm

  val GraphPlanTheorem_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [FM_plan] Parent theory of "GraphPlanTheorem"

   [utils] Parent theory of "GraphPlanTheorem"

   [MPLS_def]  Definition

      |- ∀PROB.
           MPLS PROB =
           IMAGE (λ(s,as). MIN_SET (PLS (s,as)))
             {(s,as) | (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A}

   [PLS_def]  Definition

      |- ∀s as.
           PLS (s,as) =
           IMAGE LENGTH
             {as' |
              (exec_plan (s,as') = exec_plan (s,as)) ∧ sublist as' as}

   [action_proj_def]  Definition

      |- ∀a vs.
           action_proj (a,vs) = (DRESTRICT (FST a) vs,DRESTRICT (SND a) vs)

   [as_proj_child_def]  Definition

      |- ∀as vs.
           as_proj_child (as,vs) =
           FILTER (λa. varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅)
             (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)

   [as_proj_parent_def]  Definition

      |- ∀as vs.
           as_proj_parent (as,vs) =
           FILTER (λa. ¬varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅) as

   [as_proj_primitive_def]  Definition

      |- as_proj =
         WFREC
           (@R.
              WF R ∧
              (∀as vs a.
                 ¬(FDOM (DRESTRICT (SND a) vs) ≠ ∅) ⇒
                 R (as,vs) (a::as,vs)) ∧
              ∀as vs a.
                FDOM (DRESTRICT (SND a) vs) ≠ ∅ ⇒ R (as,vs) (a::as,vs))
           (λas_proj a'.
              case a' of
                ([],vs) => I []
              | (a::as,vs) =>
                  I
                    (if FDOM (DRESTRICT (SND a) vs) ≠ ∅ then
                       action_proj (a,vs)::as_proj (as,vs)
                     else as_proj (as,vs)))

   [child_parent_rel_def]  Definition

      |- ∀PROB vs.
           child_parent_rel (PROB,vs) ⇔
           dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
           ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)

   [dep_def]  Definition

      |- ∀PROB v1 v2.
           dep (PROB,v1,v2) ⇔
           (∃a.
              a ∈ PROB.A ∧
              (v1 ∈ FDOM (FST a) ∧ v2 ∈ FDOM (SND a) ∨
               v1 ∈ FDOM (SND a) ∧ v2 ∈ FDOM (SND a))) ∨ (v1 = v2)

   [dep_var_set_def]  Definition

      |- ∀PROB vs1 vs2.
           dep_var_set (PROB,vs1,vs2) ⇔
           ∃v1 v2.
             v1 ∈ vs1 ∧ v2 ∈ vs2 ∧ DISJOINT vs1 vs2 ∧ dep (PROB,v1,v2)

   [list_frag_def]  Definition

      |- ∀l frag. list_frag (l,frag) ⇔ ∃pfx sfx. pfx ++ frag ++ sfx = l

   [list_frag_rec_primitive_def]  Definition

      |- list_frag_rec =
         WFREC
           (@R.
              WF R ∧
              (∀l' l_original l h_orig h' h.
                 h ≠ h' ∧ h ≠ h_orig ⇒
                 R (l,h_orig::l_original,h_orig::l_original)
                   (h::l,h'::l',h_orig::l_original)) ∧
              (∀l' l_original l h_orig h' h.
                 h ≠ h' ∧ (h = h_orig) ⇒
                 R (l,l_original,h_orig::l_original)
                   (h::l,h'::l',h_orig::l_original)) ∧
              ∀l_original h_orig l' l h' h.
                (h = h') ⇒
                R (l,l',h_orig::l_original)
                  (h::l,h'::l',h_orig::l_original))
           (λlist_frag_rec a.
              case a of
                (l'',[],l''') => I T
              | ([],h'::l',l''') => I F
              | (h::l,h'::l',[]) => I T
              | (h::l,h'::l',h_orig::l_original) =>
                  I
                    (if h = h' then list_frag_rec (l,l',h_orig::l_original)
                     else if h = h_orig then
                       list_frag_rec (l,l_original,h_orig::l_original)
                     else
                       list_frag_rec
                         (l,h_orig::l_original,h_orig::l_original)))

   [no_effectless_act_def]  Definition

      |- (∀a as.
            no_effectless_act (a::as) ⇔
            FDOM (SND a) ≠ ∅ ∧ no_effectless_act as) ∧
         (no_effectless_act [] ⇔ T)

   [prob_proj_def]  Definition

      |- ∀PROB vs.
           prob_proj (PROB,vs) =
           PROB with
           <|A :=
               IMAGE (λa. (DRESTRICT (FST a) vs,DRESTRICT (SND a) vs))
                 PROB.A; G := DRESTRICT PROB.G vs;
             I := DRESTRICT PROB.I vs|>

   [problem_plan_bound_def]  Definition

      |- ∀PROB. problem_plan_bound PROB = MAX_SET (MPLS PROB)

   [rem_condless_act_primitive_def]  Definition

      |- rem_condless_act =
         WFREC
           (@R.
              WF R ∧
              (∀as pfx_a s a.
                 ¬(FST a ⊑ exec_plan (s,pfx_a)) ⇒
                 R (s,pfx_a,as) (s,pfx_a,a::as)) ∧
              ∀as pfx_a s a.
                FST a ⊑ exec_plan (s,pfx_a) ⇒
                R (s,pfx_a ++ [a],as) (s,pfx_a,a::as))
           (λrem_condless_act a'.
              case a' of
                (s,pfx_a,[]) => I pfx_a
              | (s,pfx_a,a::as) =>
                  I
                    (if FST a ⊑ exec_plan (s,pfx_a) then
                       rem_condless_act (s,pfx_a ++ [a],as)
                     else rem_condless_act (s,pfx_a,as)))

   [rem_effectless_act_def]  Definition

      |- (∀a as.
            rem_effectless_act (a::as) =
            if FDOM (SND a) ≠ ∅ then a::rem_effectless_act as
            else rem_effectless_act as) ∧ (rem_effectless_act [] = [])

   [replace_projected_primitive_def]  Definition

      |- replace_projected =
         WFREC
           (@R.
              WF R ∧
              (∀as as' a' as'' vs a.
                 ¬varset_action (a,vs) ⇒
                 R (as'' ++ [a],a'::as',as,vs) (as'',a'::as',a::as,vs)) ∧
              (∀as as' as'' a' vs a.
                 varset_action (a,vs) ∧ a' ≠ action_proj (a,vs) ⇒
                 R (as'',a'::as',as,vs) (as'',a'::as',a::as,vs)) ∧
              ∀as as' as'' a' vs a.
                varset_action (a,vs) ∧ (a' = action_proj (a,vs)) ⇒
                R (as'' ++ [a],as',as,vs) (as'',a'::as',a::as,vs))
           (λreplace_projected a''.
              case a'' of
                (as'',[],as''',vs) =>
                  I (as'' ++ FILTER (λa. ¬varset_action (a,vs)) as''')
              | (as'',a'::as',[],vs) => I as''
              | (as'',a'::as',a::as,vs) =>
                  I
                    (if varset_action (a,vs) then
                       if a' = action_proj (a,vs) then
                         replace_projected (as'' ++ [a],as',as,vs)
                       else replace_projected (as'',a'::as',as,vs)
                     else replace_projected (as'' ++ [a],a'::as',as,vs)))

   [sat_precond_as_primitive_def]  Definition

      |- sat_precond_as =
         WFREC (@R. WF R ∧ ∀as a s. R (state_succ s a,as) (s,a::as))
           (λsat_precond_as a'.
              case a' of
                (s,[]) => I T
              | (s,a::as) =>
                  I (FST a ⊑ s ∧ sat_precond_as (state_succ s a,as)))

   [varset_action_def]  Definition

      |- ∀a varset. varset_action (a,varset) ⇔ FDOM (SND a) ⊆ varset

   [as_proj_def]  Theorem

      |- (∀vs as a.
            as_proj (a::as,vs) =
            if FDOM (DRESTRICT (SND a) vs) ≠ ∅ then
              action_proj (a,vs)::as_proj (as,vs)
            else as_proj (as,vs)) ∧ ∀vs. as_proj ([],vs) = []

   [as_proj_ind]  Theorem

      |- ∀P.
           (∀a as vs.
              (¬(FDOM (DRESTRICT (SND a) vs) ≠ ∅) ⇒ P (as,vs)) ∧
              (FDOM (DRESTRICT (SND a) vs) ≠ ∅ ⇒ P (as,vs)) ⇒
              P (a::as,vs)) ∧ (∀vs. P ([],vs)) ⇒
           ∀v v1. P (v,v1)

   [bound_child_parent_lemma]  Theorem

      |- ∀PROB vs.
           child_parent_rel (PROB,vs) ∧ PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧
           FINITE vs ∧ planning_problem PROB ⇒
           problem_plan_bound PROB <
           (problem_plan_bound (prob_proj (PROB,vs)) + 1) *
           (problem_plan_bound (prob_proj (PROB,FDOM PROB.I DIFF vs)) + 1)

   [bound_child_parent_lemma_1]  Theorem

      |- ∀PROB as vs.
           child_parent_rel (PROB,vs) ∧ plan (PROB,as) ∧
           PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧ FINITE vs ⇒
           ∃as'.
             plan (PROB,as') ∧ sublist as' as ∧
             LENGTH as' <
             (problem_plan_bound (prob_proj (PROB,vs)) + 1) *
             (problem_plan_bound (prob_proj (PROB,FDOM PROB.I DIFF vs)) +
              1)

   [bound_child_parent_lemma_1_1]  Theorem

      |- ∀as PROB vs s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧ set as ⊆ PROB.A ∧ FINITE vs ∧
           child_parent_rel (PROB,vs) ⇒
           ∃as'.
             (exec_plan (s,as') = exec_plan (s,as)) ∧
             LENGTH (FILTER (λa. varset_action (a,vs)) as') ≤
             problem_plan_bound (prob_proj (PROB,vs)) ∧
             (∀as''.
                list_frag (as',as'') ∧
                (∀a''.
                   MEM a'' as'' ⇒
                   varset_action (a'',FDOM PROB.I DIFF vs)) ⇒
                LENGTH as'' ≤
                problem_plan_bound
                  (prob_proj (PROB,FDOM PROB.I DIFF vs))) ∧ sublist as' as

   [bound_child_parent_lemma_1_1_1]  Theorem

      |- ∀PROB as vs s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ∧ child_parent_rel (PROB,vs) ∧ FINITE vs ⇒
           ∃as'.
             (exec_plan (s,as') = exec_plan (s,as)) ∧
             LENGTH (FILTER (λa. varset_action (a,vs)) as') ≤
             problem_plan_bound (prob_proj (PROB,vs)) ∧ sublist as' as

   [bound_child_parent_lemma_1_1_1_1]  Theorem

      |- ∀PROB s as vs.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ∧ sat_precond_as (s,as) ⇒
           ∃as'.
             (exec_plan (DRESTRICT s vs,as') =
              exec_plan (DRESTRICT s vs,as_proj (as,vs))) ∧
             LENGTH as' ≤ problem_plan_bound (prob_proj (PROB,vs)) ∧
             sublist as' (as_proj (as,vs)) ∧ sat_precond_as (s,as') ∧
             no_effectless_act as'

   [bound_child_parent_lemma_1_1_1_1_1]  Theorem

      |- ∀PROB as.
           plan (PROB,as) ⇒
           ∃as'.
             plan (PROB,as') ∧ sublist as' as ∧
             LENGTH as' ≤ problem_plan_bound PROB

   [bound_child_parent_lemma_1_1_1_1_1_1]  Theorem

      |- ∀PROB s as k.
           (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A ∧
           problem_plan_bound PROB ≤ k ∧ planning_problem PROB ⇒
           MIN_SET (PLS (s,as)) ≤ problem_plan_bound PROB

   [bound_child_parent_lemma_1_1_1_1_1_1_1]  Theorem

      |- ∀PROB s as.
           (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A ⇒
           MIN_SET (PLS (s,as)) ∈ MPLS PROB

   [bound_child_parent_lemma_1_1_1_1_1_2]  Theorem

      |- ∀s as. ∃x. x ∈ PLS (s,as) ∧ (x = MIN_SET (PLS (s,as)))

   [bound_child_parent_lemma_1_1_1_1_1_2_1]  Theorem

      |- ∀s as. PLS (s,as) ≠ ∅

   [bound_child_parent_lemma_1_1_1_1_1_3]  Theorem

      |- ∀x s as.
           x ∈ PLS (s,as) ⇒
           ∃as'.
             (exec_plan (s,as) = exec_plan (s,as')) ∧ (LENGTH as' = x) ∧
             sublist as' as

   [bound_child_parent_lemma_1_1_1_1_2]  Theorem

      |- ∀PROB s as.
           (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A ⇒
           (problem_plan_bound PROB =
            problem_plan_bound
              (PROB with <|I := s; G := exec_plan (s,as)|>))

   [bound_child_parent_lemma_1_1_1_1_3]  Theorem

      |- ∀x y z.
           (FDOM x = FDOM y) ⇒
           (FDOM (DRESTRICT x z) = FDOM (DRESTRICT y z))

   [bound_child_parent_lemma_1_1_1_2]  Theorem

      |- ∀PROB s as vs as'.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A ∧
           sublist as' (as_proj (as,vs)) ∧ no_effectless_act as ⇒
           (LENGTH as' =
            LENGTH
              (FILTER (λa. varset_action (a,vs))
                 (replace_projected ([],as',as,vs))))

   [bound_child_parent_lemma_1_1_1_2_1]  Theorem

      |- ∀PROB as as' vs.
           planning_problem PROB ∧ no_effectless_act as ∧
           child_parent_rel (PROB,vs) ∧ set as ⊆ PROB.A ∧
           sublist as' (as_proj (as,vs)) ⇒
           (as' = as_proj (replace_projected ([],as',as,vs),vs))

   [bound_child_parent_lemma_1_1_1_2_1_1]  Theorem

      |- ∀PROB as vs.
           planning_problem PROB ∧ no_effectless_act as ∧
           child_parent_rel (PROB,vs) ∧ set as ⊆ PROB.A ⇒
           (as_proj (FILTER (λa. ¬varset_action (a,vs)) as,vs) = [])

   [bound_child_parent_lemma_1_1_1_3]  Theorem

      |- ∀PROB s as vs as'.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A ∧
           sat_precond_as (s,as) ∧ sublist as' (as_proj (as,vs)) ∧
           no_effectless_act as ∧ sat_precond_as (s,as') ⇒
           (DRESTRICT (exec_plan (s,replace_projected ([],as',as,vs))) vs =
            exec_plan (DRESTRICT s vs,as'))

   [bound_child_parent_lemma_1_1_1_3_1]  Theorem

      |- ∀PROB vs sa sc as as_c.
           sublist as_c (as_proj (as,vs)) ∧ planning_problem PROB ∧
           (FDOM sa = FDOM PROB.I) ∧ (FDOM sc = FDOM PROB.I) ∧
           child_parent_rel (PROB,vs) ∧ set as ⊆ PROB.A ∧
           no_effectless_act as ∧
           (DRESTRICT sa (FDOM PROB.I DIFF vs) =
            DRESTRICT sc (FDOM PROB.I DIFF vs)) ∧ sat_precond_as (sa,as) ∧
           sat_precond_as (sc,as_c) ⇒
           sat_precond_as (sc,replace_projected ([],as_c,as,vs))

   [bound_child_parent_lemma_1_1_1_3_1_1]  Theorem

      |- ∀PROB vs a s s'.
           planning_problem PROB ∧ child_parent_rel (PROB,vs) ∧
           a ∈ PROB.A ∧ FDOM (SND a) ≠ ∅ ∧ (FDOM s = FDOM PROB.I) ∧
           (FDOM s' = FDOM PROB.I) ∧
           (DRESTRICT s (FDOM PROB.I DIFF vs) =
            DRESTRICT s' (FDOM PROB.I DIFF vs)) ∧ ¬varset_action (a,vs) ∧
           FST a ⊑ s ⇒
           FST a ⊑ s'

   [bound_child_parent_lemma_1_1_1_3_1_1_1]  Theorem

      |- ∀vs a s s'.
           (DRESTRICT s vs = DRESTRICT s' vs) ∧ a ⊑ s ⇒ DRESTRICT a vs ⊑ s'

   [bound_child_parent_lemma_1_1_1_3_1_2]  Theorem

      |- ∀vs a s.
           FDOM a ⊆ FDOM s ∧ DRESTRICT a vs ⊑ s ∧
           DRESTRICT a (FDOM s DIFF vs) ⊑ s ⇒
           a ⊑ s

   [bound_child_parent_lemma_1_1_1_3_1_3]  Theorem

      |- ∀a b. a ⊆ b ⇒ (a ∩ b = a)

   [bound_child_parent_lemma_1_1_1_3_1_4]  Theorem

      |- ∀a s vs.
           varset_action (a,vs) ∧ FST a ⊑ s ∧ FDOM (SND a) ⊆ FDOM s ⇒
           (state_succ s (action_proj (a,vs)) = state_succ s a)

   [bound_child_parent_lemma_1_1_1_3_1_4_1]  Theorem

      |- ∀a s vs.
           DISJOINT (FDOM (SND a)) s ⇒
           DISJOINT (FDOM (SND (action_proj (a,vs)))) s

   [bound_child_parent_lemma_1_1_1_4]  Theorem

      |- ∀PROB vs s as_c as.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           (FDOM s = FDOM PROB.I) ∧ set as ⊆ PROB.A ∧
           sublist as_c (as_proj (as,vs)) ∧ sat_precond_as (s,as) ∧
           sat_precond_as (s,as_c) ∧ no_effectless_act as ⇒
           (DRESTRICT (exec_plan (s,as)) (FDOM PROB.I DIFF vs) =
            DRESTRICT (exec_plan (s,replace_projected ([],as_c,as,vs)))
              (FDOM PROB.I DIFF vs))

   [bound_child_parent_lemma_1_1_1_4_1]  Theorem

      |- ∀PROB vs as_c as.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           no_effectless_act as ∧ set as ⊆ PROB.A ⇒
           (FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs)) as =
            FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs))
              (replace_projected ([],as_c,as,vs)))

   [bound_child_parent_lemma_1_1_1_4_1_1]  Theorem

      |- ∀PROB vs as_c as.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           set as ⊆ PROB.A ⇒
           (FILTER (λa. ¬varset_action (a,vs)) as =
            FILTER (λa. ¬varset_action (a,vs))
              (replace_projected ([],as_c,as,vs)))

   [bound_child_parent_lemma_1_1_1_4_1_2]  Theorem

      |- ∀PROB vs as.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           no_effectless_act as ∧ set as ⊆ PROB.A ⇒
           (FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs)) as =
            FILTER (λa. ¬varset_action (a,vs)) as)

   [bound_child_parent_lemma_1_1_1_4_2]  Theorem

      |- ∀PROB vs as.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           set as ⊆ PROB.A ∧ no_effectless_act as ⇒
           (as_proj (as,FDOM PROB.I DIFF vs) =
            FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs)) as)

   [bound_child_parent_lemma_1_1_1_4_2_1]  Theorem

      |- ∀as.
           no_effectless_act as ⇒ (FILTER (λa. FDOM (SND a) ≠ ∅) as = as)

   [bound_child_parent_lemma_1_1_1_4_3]  Theorem

      |- ∀PROB vs s as.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           set as ⊆ PROB.A ∧ (FDOM PROB.I = FDOM s) ∧
           sat_precond_as (s,as) ∧ no_effectless_act as ⇒
           sat_precond_as
             (s,FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs)) as)

   [bound_child_parent_lemma_1_1_2]  Theorem

      |- ∀PROB as vs s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ∧
           EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as ∧
           child_parent_rel (PROB,vs) ⇒
           ∃as'.
             (exec_plan (s,as') = exec_plan (s,as)) ∧
             LENGTH as' ≤
             problem_plan_bound (prob_proj (PROB,FDOM PROB.I DIFF vs)) ∧
             EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as' ∧
             sublist as' as

   [bound_child_parent_lemma_1_1_2_4]  Theorem

      |- ∀PROB vs as.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ∧
           EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as ∧
           no_effectless_act as ⇒
           (as_proj (as,FDOM PROB.I DIFF vs) = as)

   [bound_child_parent_lemma_1_1_2_4_1]  Theorem

      |- ∀PROB vs a.
           planning_problem PROB ∧ child_parent_rel (PROB,vs) ∧
           a ∈ PROB.A ∧ varset_action (a,FDOM PROB.I DIFF vs) ∧
           FDOM (SND a) ≠ ∅ ⇒
           (action_proj (a,FDOM PROB.I DIFF vs) = a)

   [bound_child_parent_lemma_1_1_2_4_1_1]  Theorem

      |- ∀PROB vs a.
           planning_problem PROB ∧ child_parent_rel (PROB,vs) ∧
           a ∈ PROB.A ∧ varset_action (a,FDOM PROB.I DIFF vs) ∧
           FDOM (SND a) ≠ ∅ ⇒
           FDOM (FST a) ⊆ FDOM PROB.I DIFF vs

   [bound_child_parent_lemma_1_1_2_5]  Theorem

      |- ∀as' as s. set as ⊆ s ∧ sublist as' as ⇒ set as' ⊆ s

   [bound_child_parent_lemma_1_1_3]  Theorem

      |- ∀k1 k2 s Par Ch f l PProbs PProbl.
           PProbs s ∧ PProbl l ∧
           (∀l s.
              PProbs s ∧ PProbl l ∧ EVERY Par l ⇒
              ∃l'.
                (f (s,l') = f (s,l)) ∧ LENGTH l' ≤ k1 ∧ EVERY Par l' ∧
                sublist l' l) ∧
           (∀l s.
              PProbs s ∧ PProbl l ⇒
              ∃l'.
                (f (s,l') = f (s,l)) ∧ LENGTH (FILTER Ch l') ≤ k2 ∧
                sublist l' l) ∧
           (∀a l. PProbl l ∧ MEM a l ⇒ (Ch a ⇔ ¬Par a)) ∧
           (∀s l1 l2. f (f (s,l1),l2) = f (s,l1 ++ l2)) ∧
           (∀s l. PProbs s ∧ PProbl l ⇒ PProbs (f (s,l))) ∧
           (∀l1 l2. sublist l1 l2 ∧ PProbl l2 ⇒ PProbl l1) ∧
           (∀l1 l2. PProbl (l1 ++ l2) ⇔ PProbl l1 ∧ PProbl l2) ⇒
           ∃l'.
             (f (s,l') = f (s,l)) ∧ LENGTH (FILTER Ch l') ≤ k2 ∧
             (∀l''. list_frag (l',l'') ∧ EVERY Par l'' ⇒ LENGTH l'' ≤ k1) ∧
             sublist l' l

   [bound_child_parent_lemma_1_1_3_1]  Theorem

      |- ∀Ch k1 Par f s l PProbs PProbl.
           PProbs s ∧ PProbl l ∧
           (∀l s.
              PProbs s ∧ PProbl l ∧ EVERY Par l ⇒
              ∃l'.
                (f (s,l') = f (s,l)) ∧ LENGTH l' ≤ k1 ∧ EVERY Par l' ∧
                sublist l' l) ∧
           (∀a l. PProbl l ∧ MEM a l ⇒ (Ch a ⇔ ¬Par a)) ∧
           (∀s l1 l2. f (f (s,l1),l2) = f (s,l1 ++ l2)) ∧
           (∀s l. PProbs s ∧ PProbl l ⇒ PProbs (f (s,l))) ∧
           (∀l1 l2. sublist l1 l2 ∧ PProbl l2 ⇒ PProbl l1) ∧
           (∀l1 l2. PProbl (l1 ++ l2) ⇔ PProbl l1 ∧ PProbl l2) ⇒
           ∃l'.
             (f (s,l') = f (s,l)) ∧
             (LENGTH (FILTER Ch l') = LENGTH (FILTER Ch l)) ∧
             (∀l''. list_frag (l',l'') ∧ EVERY Par l'' ⇒ LENGTH l'' ≤ k1) ∧
             sublist l' l

   [bound_child_parent_lemma_2]  Theorem

      |- ∀P f.
           (∀PROB s s'.
              P PROB ∧ (FDOM s = FDOM PROB.I) ∧ (FDOM s' = FDOM PROB.I) ⇒
              P (PROB with <|I := s; G := s'|>) ∧
              (f PROB = f (PROB with <|I := s; G := s'|>))) ∧
           (∀PROB as.
              P PROB ∧ plan (PROB,as) ⇒
              ∃as'.
                plan (PROB,as') ∧ sublist as' as ∧ LENGTH as' < f PROB) ⇒
           ∀PROB.
             planning_problem PROB ∧ P PROB ⇒
             problem_plan_bound PROB < f PROB

   [bound_child_parent_lemma_2_1]  Theorem

      |- ∀P f.
           (∀PROB s s'.
              P PROB ∧ (FDOM s = FDOM PROB.I) ∧ (FDOM s' = FDOM PROB.I) ⇒
              P (PROB with <|I := s; G := s'|>) ∧
              (f PROB = f (PROB with <|I := s; G := s'|>))) ∧
           (∀PROB as.
              P PROB ∧ plan (PROB,as) ⇒
              ∃as'.
                plan (PROB,as') ∧ sublist as' as ∧ LENGTH as' < f PROB) ⇒
           ∀PROB x.
             P PROB ∧ planning_problem PROB ⇒ x ∈ MPLS PROB ⇒ x < f PROB

   [bound_child_parent_lemma_2_1_1]  Theorem

      |- ∀P f.
           (∀PROB s s'.
              P PROB ∧ (FDOM s = FDOM PROB.I) ∧ (FDOM s' = FDOM PROB.I) ⇒
              P (PROB with <|I := s; G := s'|>) ∧
              (f PROB = f (PROB with <|I := s; G := s'|>))) ∧
           (∀PROB as.
              P PROB ∧ plan (PROB,as) ⇒
              ∃as'.
                plan (PROB,as') ∧ sublist as' as ∧ LENGTH as' < f PROB) ⇒
           ∀PROB s as.
             P PROB ∧ planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
             set as ⊆ PROB.A ⇒
             ∃x. x ∈ PLS (s,as) ∧ x < f PROB

   [bound_child_parent_lemma_2_1_2]  Theorem

      |- ∀s k. (∃x. x ∈ s ∧ x < k) ⇒ MIN_SET s < k

   [bound_child_parent_lemma_2_2]  Theorem

      |- ∀s k. s ≠ ∅ ∧ (∀x. x ∈ s ⇒ x < k) ⇒ MAX_SET s < k

   [bound_child_parent_lemma_2_2_1]  Theorem

      |- ∀s k. (∀x. x ∈ s ⇒ x < k) ⇒ FINITE s

   [bound_child_parent_lemma_3]  Theorem

      |- ∀PROB vs s s'.
           (λPROB.
              child_parent_rel (PROB,vs) ∧
              PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧ FINITE vs) PROB ∧
           (FDOM s = FDOM PROB.I) ∧ (FDOM s' = FDOM PROB.I) ⇒
           (λPROB.
              child_parent_rel (PROB,vs) ∧
              PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧ FINITE vs)
             (PROB with <|I := s; G := s'|>)

   [bound_child_parent_lemma_4]  Theorem

      |- ∀PROB vs s s'.
           (FDOM s = FDOM PROB.I) ∧ (FDOM s' = FDOM PROB.I) ⇒
           ((λPROB.
               (problem_plan_bound (prob_proj (PROB,vs)) + 1) *
               (problem_plan_bound (prob_proj (PROB,FDOM PROB.I DIFF vs)) +
                1)) PROB =
            (λPROB.
               (problem_plan_bound (prob_proj (PROB,vs)) + 1) *
               (problem_plan_bound (prob_proj (PROB,FDOM PROB.I DIFF vs)) +
                1)) (PROB with <|I := s; G := s'|>))

   [bound_main_lemma]  Theorem

      |- ∀PROB.
           planning_problem PROB ⇒
           problem_plan_bound PROB ≤ 2 ** CARD (FDOM PROB.I)

   [bound_main_lemma_1]  Theorem

      |- ∀PROB x.
           planning_problem PROB ⇒
           x ∈ MPLS PROB ⇒
           x ≤ 2 ** CARD (FDOM PROB.I)

   [bound_main_lemma_1_1]  Theorem

      |- ∀PROB s as.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ⇒
           ∃x. x ∈ PLS (s,as) ∧ x ≤ 2 ** CARD (FDOM PROB.I)

   [bound_main_lemma_1_2]  Theorem

      |- ∀s k. (∃x. x ∈ s ∧ x ≤ k) ⇒ MIN_SET s ≤ k

   [bound_main_lemma_2]  Theorem

      |- ∀s k. s ≠ ∅ ∧ (∀x. x ∈ s ⇒ x ≤ k) ⇒ MAX_SET s ≤ k

   [bound_main_lemma_2_1]  Theorem

      |- ∀s k. (∀x. x ∈ s ⇒ x ≤ k) ⇒ FINITE s

   [bound_main_lemma_3]  Theorem

      |- ∀PROB. MPLS PROB ≠ ∅

   [child_parent_lemma_1]  Theorem

      |- ∀PROB as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ⇒
           (as_proj_child (as,vs) = as_proj (as,vs)) ∧
           (as_proj_parent (as,vs) = as_proj (as,FDOM PROB.I DIFF vs))

   [child_parent_lemma_1_1]  Theorem

      |- ∀PROB as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ⇒
           (as_proj_child (as,vs) = as_proj (as,vs))

   [child_parent_lemma_1_1_1]  Theorem

      |- ∀a vs. varset_action (a,vs) ⇒ (DRESTRICT (SND a) vs = SND a)

   [child_parent_lemma_1_1_2]  Theorem

      |- ∀PROB a vs.
           planning_problem PROB ∧ a ∈ PROB.A ∧
           child_parent_rel (PROB,vs) ∧ FDOM (SND a) ≠ ∅ ⇒
           (varset_action (a,vs) ⇔ ¬varset_action (a,FDOM PROB.I DIFF vs))

   [child_parent_lemma_1_2]  Theorem

      |- ∀PROB as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ⇒
           (as_proj_parent (as,vs) = as_proj (as,FDOM PROB.I DIFF vs))

   [child_parent_lemma_1_2_1]  Theorem

      |- ∀PROB vs a.
           child_parent_rel (PROB,vs) ∧ planning_problem PROB ∧
           a ∈ PROB.A ∧ varset_action (a,FDOM PROB.I DIFF vs) ∧
           FDOM (SND a) ≠ ∅ ⇒
           FDOM (FST a) ⊆ FDOM PROB.I DIFF vs

   [child_parent_lemma_1_2_1_1]  Theorem

      |- ∀PROB vs a.
           child_parent_rel (PROB,vs) ∧ a ∈ PROB.A ∧
           ¬DISJOINT (FDOM (SND a)) (FDOM PROB.I DIFF vs) ⇒
           DISJOINT (FDOM (FST a)) vs

   [child_parent_lemma_1_3_1]  Theorem

      |- ∀x vs. FDOM (DRESTRICT x vs) ≠ ∅ ⇒ FDOM x ≠ ∅

   [child_parent_lemma_1_4_1]  Theorem

      |- ∀PROB a vs.
           child_parent_rel (PROB,vs) ∧ a ∈ PROB.A ∧
           ¬DISJOINT (FDOM (SND a)) (FDOM PROB.I DIFF vs) ⇒
           DISJOINT (FDOM (SND a)) vs

   [child_parent_lemma_1_5_1]  Theorem

      |- ∀PROB a vs.
           planning_problem PROB ∧ a ∈ PROB.A ∧ ¬varset_action (a,vs) ⇒
           ¬DISJOINT (FDOM (SND a)) (FDOM PROB.I DIFF vs)

   [child_parent_lemma_2_1]  Theorem

      |- ∀PROB as vs.
           plan (PROB,as) ∧ PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧
           child_parent_rel (PROB,vs) ∧ FINITE vs ⇒
           ∃as'.
             plan (PROB,as') ∧
             LENGTH as' <
             (2 ** CARD vs + 1) * (2 ** CARD (FDOM PROB.I DIFF vs) + 1)

   [child_parent_lemma_2_1_1]  Theorem

      |- ∀PROB vs as s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ∧ FINITE vs ∧ child_parent_rel (PROB,vs) ⇒
           ∃as'.
             (exec_plan (s,as') = exec_plan (s,as)) ∧
             LENGTH (FILTER (λa. varset_action (a,vs)) as') ≤
             2 ** CARD vs ∧ set as' ⊆ PROB.A

   [child_parent_lemma_2_1_1_1]  Theorem

      |- ∀PROB s as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ∧
           (DRESTRICT s vs = DRESTRICT (exec_plan (s,as)) vs) ∧
           (∃a. MEM a as ∧ (λa. varset_action (a,vs)) a) ⇒
           (DRESTRICT (exec_plan (s,as)) vs =
            DRESTRICT (exec_plan (s,as_proj_parent (as,vs))) vs) ∧
           LENGTH
             (FILTER (λa. varset_action (a,vs)) (as_proj_parent (as,vs))) <
           LENGTH (FILTER (λa. varset_action (a,vs)) as)

   [child_parent_lemma_2_1_1_1_1]  Theorem

      |- ∀PROB s s' as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ∧
           (DRESTRICT s vs = DRESTRICT (exec_plan (s,as)) vs) ⇒
           (DRESTRICT s vs =
            DRESTRICT (exec_plan (s,as_proj_parent (as,vs))) vs)

   [child_parent_lemma_2_1_1_1_1_1]  Theorem

      |- ∀PROB s as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ⇒
           (DRESTRICT s vs =
            DRESTRICT (exec_plan (s,as_proj_parent (as,vs))) vs)

   [child_parent_lemma_2_1_1_1_2]  Theorem

      |- ∀P l.
           (∃x. MEM x l ∧ P x) ⇒ LENGTH (FILTER (λx. ¬P x) l) < LENGTH l

   [child_parent_lemma_2_1_1_1_3]  Theorem

      |- ∀as vs.
           (∃a. MEM a as ∧ (λa. varset_action (a,vs)) a) ⇒
           LENGTH
             (FILTER (λa. varset_action (a,vs)) (as_proj_parent (as,vs))) <
           LENGTH (FILTER (λa. varset_action (a,vs)) as)

   [child_parent_lemma_2_1_1_1_3_1]  Theorem

      |- ∀P P2 l.
           (∃a. MEM a l ∧ P a) ⇒
           LENGTH (FILTER (λa. P a) (FILTER (λa. ¬P a ∧ P2 a) l)) <
           LENGTH (FILTER (λa. P a) l)

   [child_parent_lemma_2_1_1_1_3_1_1]  Theorem

      |- ∀P l. LENGTH (FILTER (λa. P a) (FILTER (λa. ¬P a) l)) = 0

   [child_parent_lemma_2_1_1_2]  Theorem

      |- ∀PROB s as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ∧ sat_precond_as (s,as) ⇒
           sat_precond_as (s,as_proj_parent (as,vs))

   [child_parent_lemma_2_1_2]  Theorem

      |- ∀PROB vs as s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ∧ FINITE vs ∧ child_parent_rel (PROB,vs) ∧
           EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as ⇒
           ∃as'.
             (exec_plan (s,as') = exec_plan (s,as)) ∧
             LENGTH as' ≤ 2 ** CARD (FDOM PROB.I DIFF vs) ∧
             EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as' ∧
             set as' ⊆ PROB.A

   [child_parent_lemma_2_1_2_1]  Theorem

      |- ∀PROB vs as.
           child_parent_rel (PROB,vs) ∧ set as ⊆ PROB.A ∧
           planning_problem PROB ⇒
           (as_proj_parent (as,vs) =
            FILTER
              (λa.
                 varset_action (a,FDOM PROB.I DIFF vs) ∧ FDOM (SND a) ≠ ∅)
              as)

   [child_parent_lemma_2_1_2_2]  Theorem

      |- ∀PROB vs as s.
           child_parent_rel (PROB,vs) ∧ set as ⊆ PROB.A ∧
           planning_problem PROB ∧
           EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as ⇒
           (DRESTRICT s vs = DRESTRICT (exec_plan (s,as)) vs)

   [child_parent_lemma_2_1_2_2_2]  Theorem

      |- ∀P l. (FILTER (λx. P x) l = []) ⇔ EVERY (λx. ¬P x) l

   [child_parent_lemma_2_1_2_3]  Theorem

      |- ∀P1 P2 a. (λa. P1 a) a ∧ (λa. P2 a) a ⇔ (λa. P1 a ∧ P2 a) a

   [child_parent_lemma_2_1_2_4]  Theorem

      |- ∀PROB as vs.
           planning_problem PROB ∧ set as ⊆ PROB.A ∧
           child_parent_rel (PROB,vs) ⇒
           (FILTER
              (λa.
                 varset_action (a,FDOM PROB.I DIFF vs) ∧ FDOM (SND a) ≠ ∅)
              as =
            FILTER (λa. ¬varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅) as)

   [child_parent_lemma_2_1_3]  Theorem

      |- ∀as PROB vs s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) ∧ set as ⊆ PROB.A ∧ FINITE vs ∧
           child_parent_rel (PROB,vs) ⇒
           ∃as'.
             (exec_plan (s,as') = exec_plan (s,as)) ∧
             LENGTH (FILTER (λa. varset_action (a,vs)) as') ≤
             2 ** CARD vs ∧
             (∀as''.
                list_frag (as',as'') ∧
                (∀a''.
                   MEM a'' as'' ⇒
                   varset_action (a'',FDOM PROB.I DIFF vs)) ⇒
                LENGTH as'' ≤ 2 ** CARD (FDOM PROB.I DIFF vs)) ∧
             set as' ⊆ PROB.A

   [child_parent_lemma_2_1_3_1]  Theorem

      |- ∀k1 k2 s Par Ch f l PProbs PProbl.
           PProbs s ∧ PProbl l ∧
           (∀l s.
              PProbs s ∧ PProbl l ∧ EVERY Par l ⇒
              ∃l'.
                (f (s,l') = f (s,l)) ∧ LENGTH l' ≤ k1 ∧ EVERY Par l' ∧
                PProbl l') ∧
           (∀l s.
              PProbs s ∧ PProbl l ⇒
              ∃l'.
                (f (s,l') = f (s,l)) ∧ LENGTH (FILTER Ch l') ≤ k2 ∧
                PProbl l') ∧ (∀a l. PProbl l ∧ MEM a l ⇒ (Ch a ⇔ ¬Par a)) ∧
           (∀s l1 l2. f (f (s,l1),l2) = f (s,l1 ++ l2)) ∧
           (∀l1 l2. PProbl (l1 ++ l2) ⇔ PProbl l1 ∧ PProbl l2) ∧
           (∀s l. PProbs s ∧ PProbl l ⇒ PProbs (f (s,l))) ⇒
           ∃l'.
             (f (s,l') = f (s,l)) ∧ LENGTH (FILTER Ch l') ≤ k2 ∧
             (∀l''. list_frag (l',l'') ∧ EVERY Par l'' ⇒ LENGTH l'' ≤ k1) ∧
             PProbl l'

   [child_parent_lemma_2_1_3_1_1]  Theorem

      |- ∀Ch k1 Par f s l PProbs PProbl.
           PProbs s ∧ PProbl l ∧
           (∀l s.
              PProbs s ∧ PProbl l ∧ EVERY Par l ⇒
              ∃l'.
                (f (s,l') = f (s,l)) ∧ LENGTH l' ≤ k1 ∧ EVERY Par l' ∧
                PProbl l') ∧ (∀a l. PProbl l ∧ MEM a l ⇒ (Ch a ⇔ ¬Par a)) ∧
           (∀s l1 l2. f (f (s,l1),l2) = f (s,l1 ++ l2)) ∧
           (∀l1 l2. PProbl (l1 ++ l2) ⇔ PProbl l1 ∧ PProbl l2) ∧
           (∀s l. PProbs s ∧ PProbl l ⇒ PProbs (f (s,l))) ⇒
           ∃l'.
             (f (s,l') = f (s,l)) ∧
             (LENGTH (FILTER Ch l') = LENGTH (FILTER Ch l)) ∧
             (∀l''. list_frag (l',l'') ∧ EVERY Par l'' ⇒ LENGTH l'' ≤ k1) ∧
             PProbl l'

   [child_parent_lemma_2_1_3_1_1_1]  Theorem

      |- ∀l la x lb P.
           list_frag (la ++ [x] ++ lb,l) ∧ ¬P x ∧ EVERY P l ⇒
           list_frag (la,l) ∨ list_frag (lb,l)

   [child_parent_lemma_2_1_3_1_1_1_1]  Theorem

      |- ∀l la x lb P.
           list_frag (la ++ [x] ++ lb,l) ∧ x ∉ set l ⇒
           list_frag (la,l) ∨ list_frag (lb,l)

   [child_parent_lemma_2_1_3_1_1_2]  Theorem

      |- ∀l' l. list_frag (l,l') ⇒ LENGTH l' ≤ LENGTH l

   [child_parent_lemma_xx]  Theorem

      |- ∀PROB a vs.
           planning_problem PROB ∧ child_parent_rel (PROB,vs) ∧
           a ∈ PROB.A ∧ ¬varset_action (a,vs) ⇒
           DISJOINT (FDOM (SND a)) vs

   [child_parent_lemma_xxx]  Theorem

      |- ∀PROB a vs.
           varset_action (a,vs) ⇒
           DISJOINT (FDOM (SND a)) (FDOM PROB.I DIFF vs)

   [child_parent_lemma_xxxx]  Theorem

      |- ∀PROB a vs.
           varset_action (a,FDOM PROB.I DIFF vs) ⇒
           DISJOINT (FDOM (SND a)) vs

   [child_parent_lemma_xxxxx]  Theorem

      |- ∀PROB a vs.
           varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅ ⇒
           ¬DISJOINT (FDOM (SND a)) vs

   [child_parent_lemma_xxxxxx]  Theorem

      |- ∀s a vs.
           varset_action (a,vs) ⇒ DISJOINT (FDOM (SND a)) (s DIFF vs)

   [graph_plan_lemma_1]  Theorem

      |- ∀s vs as.
           sat_precond_as (s,as) ⇒
           (exec_plan (DRESTRICT s vs,as_proj (as,vs)) =
            DRESTRICT (exec_plan (s,as)) vs)

   [graph_plan_lemma_10]  Theorem

      |- ∀as s PROB vs.
           set as ⊆ PROB.A ∧ planning_problem PROB ∧
           (FDOM s = FDOM PROB.I) ⇒
           (FDOM (exec_plan (s,as_proj (as,vs))) = FDOM PROB.I)

   [graph_plan_lemma_10_1]  Theorem

      |- ∀a vs. FDOM (SND (action_proj (a,vs))) ⊆ FDOM (SND a)

   [graph_plan_lemma_11]  Theorem

      |- ∀s as vs.
           sat_precond_as (s,as) ⇒
           (DRESTRICT (exec_plan (s,as_proj (as,vs))) vs =
            DRESTRICT (exec_plan (s,as)) vs)

   [graph_plan_lemma_12]  Theorem

      |- ∀as s s' vs.
           sat_precond_as (s,as) ∧ (DRESTRICT s vs = DRESTRICT s' vs) ⇒
           sat_precond_as (s',as_proj (as,vs))

   [graph_plan_lemma_12_1]  Theorem

      |- ∀s s' vs x.
           (DRESTRICT s vs = DRESTRICT s' vs) ⇒
           (DRESTRICT x vs ⊑ s ⇔ DRESTRICT x vs ⊑ s')

   [graph_plan_lemma_12_2]  Theorem

      |- ∀a vs. action_proj (action_proj (a,vs),vs) = action_proj (a,vs)

   [graph_plan_lemma_12_3]  Theorem

      |- ∀s a vs.
           (FDOM (DRESTRICT (SND a) vs) = ∅) ⇒
           (DRESTRICT (state_succ s a) vs = DRESTRICT s vs)

   [graph_plan_lemma_12_4]  Theorem

      |- ∀fm1 fm2 vs. fm2 ⊑ fm1 ⇒ DRESTRICT fm2 vs ⊑ fm1

   [graph_plan_lemma_13]  Theorem

      |- ∀as s s' vs.
           sat_precond_as (s,as) ∧ (DRESTRICT s vs = DRESTRICT s' vs) ⇒
           sat_precond_as (DRESTRICT s' vs,as_proj (as,vs))

   [graph_plan_lemma_14]  Theorem

      |- ∀l f1 f2 x.
           MEM x (MAP f1 l) ∧ f2 x ∧ (∀g. SND (f1 g) = SND g) ∧
           (∀g h. (SND g = SND h) ⇒ (f2 g ⇔ f2 h)) ⇒
           ∃y. MEM y l ∧ f2 y

   [graph_plan_lemma_14_1]  Theorem

      |- ∀x. SND ((λa. (DRESTRICT (FST a) vs,SND a)) x) = SND x

   [graph_plan_lemma_14_2]  Theorem

      |- ∀x y.
           (SND x = SND y) ⇒
           ((λa. varset_action (a,vs)) x ⇔ (λa. varset_action (a,vs)) y)

   [graph_plan_lemma_15]  Theorem

      |- ∀l1 l2 l3 l4 P.
           LENGTH (FILTER P l2) < LENGTH (FILTER P l3) ⇒
           LENGTH (FILTER P (l1 ++ l2 ++ l4)) <
           LENGTH (FILTER P (l1 ++ l3 ++ l4))

   [graph_plan_lemma_15_1]  Theorem

      |- ∀l1 l2 l3 P.
           LENGTH (FILTER P l3) < LENGTH (FILTER P l2) ⇒
           LENGTH (FILTER P (l1 ++ l3)) < LENGTH (FILTER P (l1 ++ l2))

   [graph_plan_lemma_15_2]  Theorem

      |- ∀l1 l2 l3 P.
           LENGTH (FILTER P l3) < LENGTH (FILTER P l2) ⇒
           LENGTH (FILTER P (l3 ++ l1)) < LENGTH (FILTER P (l2 ++ l1))

   [graph_plan_lemma_16]  Theorem

      |- ∀s A as.
           (exec_plan (s,as) = exec_plan (s,rem_effectless_act as)) ∧
           (sat_precond_as (s,as) ⇒
            sat_precond_as (s,rem_effectless_act as)) ∧
           LENGTH (rem_effectless_act as) ≤ LENGTH as ∧
           (set as ⊆ A ⇒ set (rem_effectless_act as) ⊆ A) ∧
           no_effectless_act (rem_effectless_act as) ∧
           ∀P.
             LENGTH (FILTER P (rem_effectless_act as)) ≤
             LENGTH (FILTER P as)

   [graph_plan_lemma_16_1]  Theorem

      |- ∀s as. exec_plan (s,as) = exec_plan (s,rem_effectless_act as)

   [graph_plan_lemma_16_10]  Theorem

      |- ∀as P. no_effectless_act as ⇒ no_effectless_act (FILTER P as)

   [graph_plan_lemma_16_11]  Theorem

      |- ∀as1 as2. sublist as1 (rem_effectless_act as2) ⇒ sublist as1 as2

   [graph_plan_lemma_16_12]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀as1 as2.
           no_effectless_act (as1 ++ as2) ⇔
           no_effectless_act as1 ∧ no_effectless_act as2

   [graph_plan_lemma_16_1_1]  Theorem

      |- ∀s a. (FDOM (SND a) = ∅) ⇒ (state_succ s a = s)

   [graph_plan_lemma_16_2]  Theorem

      |- ∀as s.
           sat_precond_as (s,as) ⇒ sat_precond_as (s,rem_effectless_act as)

   [graph_plan_lemma_16_3]  Theorem

      |- ∀as. LENGTH (rem_effectless_act as) ≤ LENGTH as

   [graph_plan_lemma_16_4]  Theorem

      |- ∀A as. set as ⊆ A ⇒ set (rem_effectless_act as) ⊆ A

   [graph_plan_lemma_16_5]  Theorem

      |- ∀P as.
           LENGTH (FILTER P (rem_effectless_act as)) ≤ LENGTH (FILTER P as)

   [graph_plan_lemma_16_6]  Theorem

      |- ∀as. no_effectless_act (rem_effectless_act as)

   [graph_plan_lemma_16_7]  Theorem

      |- ∀as. no_effectless_act as ⇔ EVERY (λa. FDOM (SND a) ≠ ∅) as

   [graph_plan_lemma_16_8]  Theorem

      |- ∀P as. EVERY P as ⇒ EVERY P (rem_effectless_act as)

   [graph_plan_lemma_16_9]  Theorem

      |- ∀as. sublist (rem_effectless_act as) as

   [graph_plan_lemma_17]  Theorem

      |- ∀as_1 as_2 as s.
           (as_1 ++ as_2 = as) ∧ sat_precond_as (s,as) ⇒
           sat_precond_as (s,as_1) ∧
           sat_precond_as (exec_plan (s,as_1),as_2)

   [graph_plan_lemma_18]  Theorem

      |- ∀as vs.
           as_proj_child (rem_effectless_act as,vs) =
           FILTER (λa. varset_action (a,vs))
             (MAP (λa. (DRESTRICT (FST a) vs,SND a))
                (rem_effectless_act as))

   [graph_plan_lemma_18_1]  Theorem

      |- ∀as vs.
           as_proj_child (as,vs) =
           FILTER (λa. varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅)
             (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)

   [graph_plan_lemma_19]  Theorem

      |- ∀as s. set as ⊆ s ⇒ ∀a. MEM a as ⇒ a ∈ s

   [graph_plan_lemma_1_1]  Theorem

      |- ∀s a vs.
           FST a ⊑ s ⇒
           (state_succ (DRESTRICT s vs) (action_proj (a,vs)) =
            DRESTRICT (state_succ s a) vs)

   [graph_plan_lemma_1_1_1]  Theorem

      |- ∀fm1 fm2 vs. fm2 ⊑ fm1 ⇒ DRESTRICT fm2 vs ⊑ DRESTRICT fm1 vs

   [graph_plan_lemma_1_2]  Theorem

      |- ∀a vs s.
           DISJOINT (FDOM (SND a)) vs ⇒
           (DRESTRICT s vs = DRESTRICT (state_succ s a) vs)

   [graph_plan_lemma_1_2_1]  Theorem

      |- ∀fm1 fm2 vs.
           vs ⊆ FDOM fm1 ∧ (fm2 = fm1) ⇒
           (DRESTRICT fm2 vs = DRESTRICT fm1 vs)

   [graph_plan_lemma_1_2_2]  Theorem

      |- ∀x vs s.
           DISJOINT (FDOM x) vs ⇒ (DRESTRICT s vs = DRESTRICT (x ⊌ s) vs)

   [graph_plan_lemma_1_3]  Theorem

      |- ∀x vs. (FDOM (DRESTRICT x vs) = ∅) ⇔ DISJOINT (FDOM x) vs

   [graph_plan_lemma_2]  Theorem

      |- ∀PROB vs as.
           plan (PROB,as) ∧ FINITE vs ∧
           LENGTH (as_proj (as,vs)) > 2 ** CARD vs ∧
           sat_precond_as (PROB.I,as) ⇒
           ∃as1 as2 as3.
             (as1 ++ as2 ++ as3 = as_proj (as,vs)) ∧
             (exec_plan ((prob_proj (PROB,vs)).I,as1 ++ as2) =
              exec_plan ((prob_proj (PROB,vs)).I,as1)) ∧ as2 ≠ []

   [graph_plan_lemma_20]  Theorem

      |- ∀l P. EVERY P l ⇒ (LENGTH (FILTER P l) = LENGTH l)

   [graph_plan_lemma_21]  Theorem

      |- ∀P1 P2 l. EVERY P1 l ∧ EVERY P2 l ⇔ EVERY (λa. P1 a ∧ P2 a) l

   [graph_plan_lemma_22_1]  Theorem

      |- ∀as as' as'' vs s.
           set as ⊆ s ∧ set as'' ⊆ s ⇒
           set (replace_projected (as'',as',as,vs)) ⊆ s

   [graph_plan_lemma_22_2]  Theorem

      |- ∀as as' vs s. sublist (replace_projected ([],as',as,vs)) as

   [graph_plan_lemma_22_2_1]  Theorem

      |- ∀as as' as'' as''' as'''' vs.
           sublist (replace_projected (as'',as',as,vs)) as''' ⇒
           sublist (replace_projected (as'''' ++ as'',as',as,vs))
             (as'''' ++ as''')

   [graph_plan_lemma_22_3]  Theorem

      |- ∀PROB vs as' as.
           no_effectless_act as ∧ planning_problem PROB ∧
           child_parent_rel (PROB,vs) ∧ set as ⊆ PROB.A ⇒
           no_effectless_act (replace_projected ([],as',as,vs))

   [graph_plan_lemma_22_3_1]  Theorem

      |- ∀as''' as'' as' as vs.
           replace_projected (as''' ++ as'',as',as,vs) =
           as''' ++ replace_projected (as'',as',as,vs)

   [graph_plan_lemma_22_4]  Theorem

      |- ∀PROB vs as as'.
           set as ⊆ PROB.A ∧ planning_problem PROB ∧
           child_parent_rel (PROB,vs) ∧ no_effectless_act as ⇒
           set (replace_projected ([],as',as,vs)) ⊆ PROB.A

   [graph_plan_lemma_23]  Theorem

      |- ∀as' as vs.
           sublist as' (as_proj (as,vs)) ⇒ (as_proj (as',vs) = as')

   [graph_plan_lemma_23_1]  Theorem

      |- ∀x s vs. x ⊑ DRESTRICT s vs ⇒ x ⊑ s

   [graph_plan_lemma_23_2]  Theorem

      |- ∀as vs. EVERY (λa. action_proj (a,vs) = a) (as_proj (as,vs))

   [graph_plan_lemma_23_3]  Theorem

      |- ∀a as vs.
           (FDOM (SND (action_proj (a,vs))) = ∅) ⇒
           (as_proj (as,vs) = as_proj (a::as,vs))

   [graph_plan_lemma_2_1]  Theorem

      |- ∀PROB vs.
           FINITE vs ⇒ CARD (FDOM (prob_proj (PROB,vs)).I) ≤ CARD vs

   [graph_plan_lemma_2_2]  Theorem

      |- ∀PROB vs.
           planning_problem PROB ⇒ planning_problem (prob_proj (PROB,vs))

   [graph_plan_lemma_2_3]  Theorem

      |- ∀PROB as vs.
           plan (PROB,as) ∧ sat_precond_as (PROB.I,as) ⇒
           plan (prob_proj (PROB,vs),as_proj (as,vs))

   [graph_plan_lemma_2_3_1]  Theorem

      |- ∀PROB vs. plan (PROB,[]) ⇒ plan (prob_proj (PROB,vs),[])

   [graph_plan_lemma_2_3_10]  Theorem

      |- ∀as a vs.
           (FDOM (DRESTRICT (SND a) vs) = ∅) ⇒
           (as_proj (a::as,vs) = as_proj (as,vs))

   [graph_plan_lemma_2_3_11]  Theorem

      |- ∀PROB a vs.
           (FDOM (DRESTRICT (SND a) vs) = ∅) ⇒
           (prob_proj
              (PROB with I := state_succ PROB.I (action_proj (a,vs)),vs) =
            prob_proj (PROB,vs))

   [graph_plan_lemma_2_3_11_1]  Theorem

      |- ∀s a vs.
           (FDOM (DRESTRICT (SND a) vs) = ∅) ⇒
           (DRESTRICT (state_succ s (action_proj (a,vs))) vs =
            DRESTRICT s vs)

   [graph_plan_lemma_2_3_7]  Theorem

      |- ∀PROB vs h as.
           h ∈ PROB.A ∧ planning_problem PROB ∧ FST h ⊑ PROB.I ∧
           plan (prob_proj (PROB with I := state_succ PROB.I h,vs),as) ⇒
           plan
             (prob_proj
                (PROB with I := state_succ PROB.I (action_proj (h,vs)),vs),
              as)

   [graph_plan_lemma_2_3_7_1]  Theorem

      |- ∀h s vs.
           FDOM (SND h) ⊆ FDOM s ⇒
           (FDOM (state_succ s (action_proj (h,vs))) =
            FDOM (state_succ s h))

   [graph_plan_lemma_2_3_7_2]  Theorem

      |- ∀h s vs.
           FST h ⊑ s ∧ FDOM (SND h) ⊆ FDOM s ⇒
           (DRESTRICT (state_succ s (action_proj (h,vs))) vs =
            DRESTRICT (state_succ s h) vs)

   [graph_plan_lemma_2_3_7_2_1]  Theorem

      |- ∀x vs y. x ∈ vs ⇒ (x ∈ FDOM (DRESTRICT y vs) ⇔ x ∈ FDOM y)

   [graph_plan_lemma_2_3_8]  Theorem

      |- ∀PROB as a vs.
           FST a ⊑ PROB.I ∧ planning_problem PROB ∧ a ∈ PROB.A ∧
           plan (prob_proj (PROB with I := state_succ PROB.I a,vs),as) ⇒
           plan (prob_proj (PROB,vs),action_proj (a,vs)::as)

   [graph_plan_lemma_2_3_8_1]  Theorem

      |- ∀s vs a.
           FST a ⊑ s ⇒
           (state_succ (DRESTRICT s vs) (action_proj (a,vs)) =
            DRESTRICT (state_succ s a) vs)

   [graph_plan_lemma_2_3_8_2]  Theorem

      |- ∀as PROB vs a.
           FST a ⊑ PROB.I ⇒
           (exec_plan ((prob_proj (PROB,vs)).I,action_proj (a,vs)::as) =
            exec_plan
              ((prob_proj (PROB with I := state_succ PROB.I a,vs)).I,as))

   [graph_plan_lemma_2_3_8_3]  Theorem

      |- ∀x y vs.
           FDOM x ⊆ FDOM y ⇒ FDOM (DRESTRICT x vs) ⊆ FDOM (DRESTRICT y vs)

   [graph_plan_lemma_2_3_8_4]  Theorem

      |- ∀PROB vs.
           (FDOM PROB.I = FDOM PROB.G) ⇒
           (FDOM (prob_proj (PROB,vs)).G = FDOM (prob_proj (PROB,vs)).I)

   [graph_plan_lemma_2_3_8_5]  Theorem

      |- ∀x vs. FDOM x ⊆ vs ⇒ (DRESTRICT x vs = x)

   [graph_plan_lemma_2_3_8_6]  Theorem

      |- ∀PROB h as vs.
           (prob_proj (PROB,vs)).G =
           (prob_proj (PROB with I := state_succ PROB.I h,vs)).G

   [graph_plan_lemma_2_3_9]  Theorem

      |- ∀as a vs.
           FDOM (DRESTRICT (SND a) vs) ≠ ∅ ⇒
           (as_proj (a::as,vs) = action_proj (a,vs)::as_proj (as,vs))

   [graph_plan_lemma_3]  Theorem

      |- ∀vs as.
           no_effectless_act as ⇒
           (LENGTH (FILTER (λa. varset_action (a,vs)) as) =
            LENGTH (as_proj_child (as,vs)))

   [graph_plan_lemma_4]  Theorem

      |- ∀s s' as vs P.
           (∀a. MEM a as ∧ P a ⇒ DISJOINT (FDOM (SND a)) vs) ∧
           sat_precond_as (s,as) ∧
           sat_precond_as (s',FILTER (λa. ¬P a) as) ∧
           (DRESTRICT s vs = DRESTRICT s' vs) ⇒
           (DRESTRICT (exec_plan (s,as)) vs =
            DRESTRICT (exec_plan (s',FILTER (λa. ¬P a) as)) vs)

   [graph_plan_lemma_4_1]  Theorem

      |- ∀s s' vs a a'.
           (DRESTRICT s vs = DRESTRICT s' vs) ∧ (FST a ⊑ s ⇔ FST a' ⊑ s') ∧
           (DRESTRICT (SND a) vs = DRESTRICT (SND a') vs) ⇒
           (DRESTRICT (state_succ s a) vs =
            DRESTRICT (state_succ s' a') vs)

   [graph_plan_lemma_5]  Theorem

      |- ∀s s' vs.
           (DRESTRICT s (FDOM s DIFF vs) =
            DRESTRICT s' (FDOM s' DIFF vs)) ∧
           (DRESTRICT s vs = DRESTRICT s' vs) ⇒
           (s = s')

   [graph_plan_lemma_6]  Theorem

      |- ∀as PROB s.
           planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧
           set as ⊆ PROB.A ⇒
           plan (PROB with <|G := exec_plan (s,as); I := s|>,as)

   [graph_plan_lemma_6_1]  Theorem

      |- ∀as s PROB.
           set as ⊆ PROB.A ∧ planning_problem PROB ∧
           (FDOM s = FDOM PROB.I) ⇒
           (FDOM (exec_plan (s,as)) = FDOM PROB.I)

   [graph_plan_lemma_6_2]  Theorem

      |- ∀P l s. set l ⊆ s ⇒ set (FILTER P l) ⊆ s

   [graph_plan_lemma_7]  Theorem

      |- ∀as A s.
           (exec_plan (s,as) = exec_plan (s,rem_condless_act (s,[],as))) ∧
           sat_precond_as (s,rem_condless_act (s,[],as)) ∧
           LENGTH (rem_condless_act (s,[],as)) ≤ LENGTH as ∧
           (set as ⊆ A ⇒ set (rem_condless_act (s,[],as)) ⊆ A) ∧
           ∀P.
             LENGTH (FILTER P (rem_condless_act (s,[],as))) ≤
             LENGTH (FILTER P as)

   [graph_plan_lemma_7_1]  Theorem

      |- ∀as s. exec_plan (s,as) = exec_plan (s,rem_condless_act (s,[],as))

   [graph_plan_lemma_7_1_1]  Theorem

      |- ∀s h as pfx.
           exec_plan (s,rem_condless_act (s,h::pfx,as)) =
           exec_plan
             (state_succ s h,rem_condless_act (state_succ s h,pfx,as))

   [graph_plan_lemma_7_2]  Theorem

      |- ∀as s. sat_precond_as (s,rem_condless_act (s,[],as))

   [graph_plan_lemma_7_2_1]  Theorem

      |- ∀h h' as as' s.
           h'::as' ≼ rem_condless_act (s,[h],as) ⇒
           as' ≼ rem_condless_act (state_succ s h,[],as) ∧ (h' = h)

   [graph_plan_lemma_7_2_1_1]  Theorem

      |- ∀h' pfx as s.
           rem_condless_act (s,h'::pfx,as) =
           h'::rem_condless_act (state_succ s h',pfx,as)

   [graph_plan_lemma_7_3]  Theorem

      |- ∀as s. LENGTH (rem_condless_act (s,[],as)) ≤ LENGTH as

   [graph_plan_lemma_7_4]  Theorem

      |- ∀as A s. set as ⊆ A ⇒ set (rem_condless_act (s,[],as)) ⊆ A

   [graph_plan_lemma_7_6]  Theorem

      |- ∀as s P.
           LENGTH (FILTER P (rem_condless_act (s,[],as))) ≤
           LENGTH (FILTER P as)

   [graph_plan_lemma_7_7]  Theorem

      |- ∀s P as as2.
           EVERY P as ∧ EVERY P as2 ⇒ EVERY P (rem_condless_act (s,as2,as))

   [graph_plan_lemma_7_8]  Theorem

      |- ∀s as. sublist (rem_condless_act (s,[],as)) as

   [graph_plan_lemma_7_8_1]  Theorem

      |- ∀l h l'. sublist l l' ⇒ sublist l (h::l')

   [graph_plan_lemma_8]  Theorem

      |- ∀as1 as2 as3 p vs.
           (as1 ++ as2 ++ as3 = as_proj (p,vs)) ⇒
           ∃p_1 p_2 p_3.
             (p_1 ++ p_2 ++ p_3 = p) ∧ (as2 = as_proj (p_2,vs)) ∧
             (as1 = as_proj (p_1,vs))

   [graph_plan_lemma_8_1]  Theorem

      |- ∀f1 f2 as1 as2 as3 p.
           (as1 ++ as2 ++ as3 = FILTER f1 (MAP f2 p)) ⇒
           ∃p_1 p_2 p_3.
             (p_1 ++ p_2 ++ p_3 = p) ∧ (as1 = FILTER f1 (MAP f2 p_1)) ∧
             (as2 = FILTER f1 (MAP f2 p_2)) ∧
             (as3 = FILTER f1 (MAP f2 p_3))

   [graph_plan_lemma_8_1_1]  Theorem

      |- ∀f1 f2 as1 as2 p.
           (as1 ++ as2 = FILTER f1 (MAP f2 p)) ⇒
           ∃p_1 p_2.
             (p_1 ++ p_2 = p) ∧ (as1 = FILTER f1 (MAP f2 p_1)) ∧
             (as2 = FILTER f1 (MAP f2 p_2))

   [graph_plan_lemma_8_2]  Theorem

      |- ∀as vs.
           as_proj (as,vs) =
           FILTER (λa. FDOM (SND a) ≠ ∅) (MAP (λa. action_proj (a,vs)) as)

   [graph_plan_lemma_9]  Theorem

      |- ∀s as vs.
           DRESTRICT (exec_plan (s,as_proj (as,vs))) vs =
           exec_plan (DRESTRICT s vs,as_proj (as,vs))

   [graph_plan_lemma_9_1]  Theorem

      |- ∀s as vs.
           DRESTRICT (exec_plan (DRESTRICT s vs,as_proj (as,vs))) vs =
           exec_plan (DRESTRICT s vs,as_proj (as,vs))

   [graph_plan_lemma_9_1_1]  Theorem

      |- ∀a s vs.
           state_succ (DRESTRICT s vs) (action_proj (a,vs)) =
           DRESTRICT (state_succ s (action_proj (a,vs))) vs

   [graph_plan_lemma_9_1_1_1]  Theorem

      |- ∀x s vs. DRESTRICT x vs ⊑ s ⇔ DRESTRICT x vs ⊑ DRESTRICT s vs

   [graph_plan_lemma_9_2]  Theorem

      |- ∀s as vs.
           DRESTRICT (exec_plan (DRESTRICT s vs,as_proj (as,vs))) vs =
           DRESTRICT (exec_plan (s,as_proj (as,vs))) vs

   [list_frag_rec_def]  Theorem

      |- (∀l_original l' l h_orig h' h.
            list_frag_rec (h::l,h'::l',h_orig::l_original) ⇔
            if h = h' then list_frag_rec (l,l',h_orig::l_original)
            else if h = h_orig then
              list_frag_rec (l,l_original,h_orig::l_original)
            else list_frag_rec (l,h_orig::l_original,h_orig::l_original)) ∧
         (∀l' l. list_frag_rec (l,[],l') ⇔ T) ∧
         (∀l' l h. list_frag_rec ([],h::l,l') ⇔ F) ∧
         ∀v9 v8 v5 v4. list_frag_rec (v8::v9,v4::v5,[]) ⇔ T

   [list_frag_rec_ind]  Theorem

      |- ∀P.
           (∀h l h' l' h_orig l_original.
              (h ≠ h' ∧ h ≠ h_orig ⇒
               P (l,h_orig::l_original,h_orig::l_original)) ∧
              (h ≠ h' ∧ (h = h_orig) ⇒
               P (l,l_original,h_orig::l_original)) ∧
              ((h = h') ⇒ P (l,l',h_orig::l_original)) ⇒
              P (h::l,h'::l',h_orig::l_original)) ∧ (∀l l'. P (l,[],l')) ∧
           (∀h l l'. P ([],h::l,l')) ∧
           (∀v8 v9 v4 v5. P (v8::v9,v4::v5,[])) ⇒
           ∀v v1 v2. P (v,v1,v2)

   [rem_condless_act_def]  Theorem

      |- (∀s pfx_a as a.
            rem_condless_act (s,pfx_a,a::as) =
            if FST a ⊑ exec_plan (s,pfx_a) then
              rem_condless_act (s,pfx_a ++ [a],as)
            else rem_condless_act (s,pfx_a,as)) ∧
         ∀s pfx_a. rem_condless_act (s,pfx_a,[]) = pfx_a

   [rem_condless_act_ind]  Theorem

      |- ∀P.
           (∀s pfx_a a as.
              (¬(FST a ⊑ exec_plan (s,pfx_a)) ⇒ P (s,pfx_a,as)) ∧
              (FST a ⊑ exec_plan (s,pfx_a) ⇒ P (s,pfx_a ++ [a],as)) ⇒
              P (s,pfx_a,a::as)) ∧ (∀s pfx_a. P (s,pfx_a,[])) ⇒
           ∀v v1 v2. P (v,v1,v2)

   [replace_projected_def]  Theorem

      |- (∀vs as'' as' as a' a.
            replace_projected (as'',a'::as',a::as,vs) =
            if varset_action (a,vs) then
              if a' = action_proj (a,vs) then
                replace_projected (as'' ++ [a],as',as,vs)
              else replace_projected (as'',a'::as',as,vs)
            else replace_projected (as'' ++ [a],a'::as',as,vs)) ∧
         (∀vs as'' as.
            replace_projected (as'',[],as,vs) =
            as'' ++ FILTER (λa. ¬varset_action (a,vs)) as) ∧
         ∀vs v7 v6 as''. replace_projected (as'',v6::v7,[],vs) = as''

   [replace_projected_ind]  Theorem

      |- ∀P.
           (∀as'' a' as' a as vs.
              (¬varset_action (a,vs) ⇒ P (as'' ++ [a],a'::as',as,vs)) ∧
              (varset_action (a,vs) ∧ a' ≠ action_proj (a,vs) ⇒
               P (as'',a'::as',as,vs)) ∧
              (varset_action (a,vs) ∧ (a' = action_proj (a,vs)) ⇒
               P (as'' ++ [a],as',as,vs)) ⇒
              P (as'',a'::as',a::as,vs)) ∧
           (∀as'' as vs. P (as'',[],as,vs)) ∧
           (∀as'' v6 v7 vs. P (as'',v6::v7,[],vs)) ⇒
           ∀v v1 v2 v3. P (v,v1,v2,v3)

   [sat_precond_as_def]  Theorem

      |- (∀s as a.
            sat_precond_as (s,a::as) ⇔
            FST a ⊑ s ∧ sat_precond_as (state_succ s a,as)) ∧
         ∀s. sat_precond_as (s,[]) ⇔ T

   [sat_precond_as_ind]  Theorem

      |- ∀P.
           (∀s a as. P (state_succ s a,as) ⇒ P (s,a::as)) ∧
           (∀s. P (s,[])) ⇒
           ∀v v1. P (v,v1)


*)
end
