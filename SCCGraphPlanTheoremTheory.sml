structure SCCGraphPlanTheoremTheory :> SCCGraphPlanTheoremTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading SCCGraphPlanTheoremTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open GraphPlanTheoremTheory SCCTheory
  in end;
  val _ = Theory.link_parents
          ("SCCGraphPlanTheorem",
          Arbnum.fromString "1387528669",
          Arbnum.fromString "921144")
          [("SCC",
           Arbnum.fromString "1387528667",
           Arbnum.fromString "351515"),
           ("GraphPlanTheorem",
           Arbnum.fromString "1387528654",
           Arbnum.fromString "934021")];
  val _ = Theory.incorporate_types "SCCGraphPlanTheorem" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("num", "num"), ID("pair", "prod"),
   ID("min", "bool"), ID("FM_plan", "problem"), ID("bool", "!"),
   ID("arithmetic", "+"), ID("pair", ","), ID("bool", "/\\"),
   ID("prim_rec", "<"), ID("arithmetic", "<="), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("min", "@"),
   ID("pred_set", "BIGUNION"), ID("arithmetic", "BIT1"),
   ID("pred_set", "CARD"), ID("bool", "COND"), ID("pred_set", "DIFF"),
   ID("pred_set", "DISJOINT"), ID("pred_set", "EMPTY"),
   ID("finite_map", "FDOM"), ID("finite_map", "fmap"),
   ID("pred_set", "FINITE"), ID("pair", "FST"), ID("pred_set", "GSPEC"),
   ID("combin", "I"), ID("pred_set", "IMAGE"), ID("bool", "IN"),
   ID("pred_set", "INSERT"), ID("pred_set", "INTER"),
   ID("arithmetic", "NUMERAL"), ID("pred_set", "REL_RESTRICT"),
   ID("SCC", "SCC"), ID("pred_set", "SUBSET"), ID("pred_set", "SUM_IMAGE"),
   ID("relation", "StrongOrder"), ID("relation", "TC"),
   ID("pred_set", "UNION"), ID("relation", "WF"), ID("relation", "WFREC"),
   ID("arithmetic", "ZERO"), ID("SCCGraphPlanTheorem", "ancestors"),
   ID("SCCGraphPlanTheorem", "childless_problem_scc_set"),
   ID("SCCGraphPlanTheorem", "childless_svs"),
   ID("SCCGraphPlanTheorem", "childless_vs"),
   ID("GraphPlanTheorem", "dep"), ID("SCCGraphPlanTheorem", "dep_tc"),
   ID("GraphPlanTheorem", "dep_var_set"),
   ID("SCCGraphPlanTheorem", "member_leaves"), ID("pair", "pair_CASE"),
   ID("FM_plan", "planning_problem"), ID("GraphPlanTheorem", "prob_proj"),
   ID("FM_plan", "problem_I"),
   ID("GraphPlanTheorem", "problem_plan_bound"),
   ID("SCCGraphPlanTheorem", "problem_scc_set"),
   ID("SCCGraphPlanTheorem", "problem_wo_vs_ancestors"),
   ID("SCCGraphPlanTheorem", "scc_set"),
   ID("SCCGraphPlanTheorem", "scc_vs"),
   ID("SCCGraphPlanTheorem", "single_child_ancestors"),
   ID("SCCGraphPlanTheorem", "single_child_parents"),
   ID("SCCGraphPlanTheorem", "sum_scc_parents"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYOP [3], TYV "'a", TYOP [0, 2, 1], TYOP [0, 3, 1],
   TYOP [4, 2], TYOP [2, 5, 4], TYOP [0, 6, 0], TYOP [2, 5, 3],
   TYOP [0, 8, 4], TYOP [0, 8, 1], TYOP [0, 6, 1], TYOP [0, 8, 5],
   TYOP [0, 5, 4], TYOP [0, 6, 4], TYOP [0, 2, 3], TYOP [0, 5, 15],
   TYOP [0, 8, 3], TYOP [0, 8, 10], TYV "'b", TYOP [2, 5, 19],
   TYOP [0, 19, 1], TYOP [0, 21, 1], TYOP [0, 4, 1], TYOP [0, 15, 1],
   TYOP [0, 24, 1], TYOP [0, 23, 1], TYOP [0, 10, 1], TYOP [0, 27, 1],
   TYOP [0, 5, 1], TYOP [0, 29, 1], TYOP [0, 0, 0], TYOP [0, 0, 31],
   TYOP [2, 2, 2], TYOP [0, 2, 33], TYOP [0, 2, 34], TYOP [2, 2, 1],
   TYOP [0, 1, 36], TYOP [0, 2, 37], TYOP [2, 3, 1], TYOP [0, 1, 39],
   TYOP [0, 3, 40], TYOP [2, 3, 3], TYOP [0, 3, 42], TYOP [0, 3, 43],
   TYOP [0, 3, 8], TYOP [0, 5, 45], TYOP [0, 4, 6], TYOP [0, 5, 47],
   TYOP [2, 5, 33], TYOP [0, 33, 49], TYOP [0, 5, 50], TYOP [2, 5, 42],
   TYOP [0, 42, 52], TYOP [0, 5, 53], TYOP [0, 1, 1], TYOP [0, 1, 55],
   TYOP [0, 0, 1], TYOP [0, 0, 57], TYOP [0, 3, 4], TYOP [0, 15, 24],
   TYOP [0, 4, 23], TYOP [0, 9, 1], TYOP [0, 9, 62], TYOP [0, 5, 29],
   TYOP [0, 18, 1], TYOP [0, 65, 18], TYOP [0, 4, 3], TYOP [0, 23, 4],
   TYOP [0, 3, 0], TYOP [0, 4, 4], TYOP [0, 4, 70], TYOP [0, 1, 71],
   TYOP [0, 3, 3], TYOP [0, 3, 73], TYOP [23, 2, 1], TYOP [0, 75, 3],
   TYOP [0, 20, 5], TYOP [0, 2, 36], TYOP [0, 78, 3], TYOP [0, 3, 39],
   TYOP [0, 80, 4], TYOP [0, 59, 61], TYOP [0, 2, 4], TYOP [0, 3, 23],
   TYOP [0, 3, 70], TYOP [0, 3, 15], TYOP [0, 15, 86], TYOP [0, 4, 59],
   TYOP [0, 59, 88], TYOP [0, 15, 4], TYOP [0, 4, 0], TYOP [0, 69, 91],
   TYOP [0, 59, 1], TYOP [0, 15, 15], TYOP [0, 59, 59], TYOP [0, 20, 1],
   TYOP [0, 20, 96], TYOP [0, 97, 1], TYOP [0, 9, 9], TYOP [0, 99, 9],
   TYOP [0, 18, 100], TYOP [0, 49, 1], TYOP [0, 52, 1], TYOP [0, 5, 59],
   TYOP [0, 104, 4], TYOP [0, 8, 105], TYOP [0, 5, 75], TYOP [0, 5, 0]]
  end
  val _ = Theory.incorporate_consts "SCCGraphPlanTheorem" tyvector
     [("sum_scc_parents", 7), ("single_child_parents", 9),
      ("single_child_ancestors", 9), ("scc_vs", 10), ("scc_set", 11),
      ("problem_wo_vs_ancestors", 12), ("problem_scc_set", 13),
      ("member_leaves", 14), ("dep_tc", 16), ("childless_vs", 10),
      ("childless_svs", 11), ("childless_problem_scc_set", 13),
      ("ancestors", 17)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P", 10), TMV("PROB", 5), TMV("R", 15), TMV("R", 18), TMV("S", 4),
   TMV("S'", 4), TMV("a", 8), TMV("min", 2), TMV("s", 3), TMV("s", 4),
   TMV("single_child_ancestors", 9), TMV("t", 3), TMV("v", 2), TMV("v", 5),
   TMV("v'", 2), TMV("v1", 2), TMV("v1", 3), TMV("v1'", 2), TMV("v2", 2),
   TMV("v2'", 2), TMV("vs", 3), TMV("vs'", 19), TMV("vs'", 3),
   TMV("vs1", 3), TMV("vs2", 3), TMV("x", 2), TMV("x", 20), TMV("x'", 2),
   TMV("y", 20), TMC(5, 4), TMC(5, 22), TMC(5, 23), TMC(5, 25), TMC(5, 26),
   TMC(5, 28), TMC(5, 30), TMC(6, 32), TMC(7, 35), TMC(7, 38), TMC(7, 41),
   TMC(7, 44), TMC(7, 46), TMC(7, 48), TMC(7, 51), TMC(7, 54), TMC(8, 56),
   TMC(9, 58), TMC(10, 58), TMC(11, 56), TMC(11, 59), TMC(11, 60),
   TMC(11, 61), TMC(11, 63), TMC(11, 58), TMC(11, 64), TMC(12, 56),
   TMC(13, 4), TMC(13, 23), TMC(14, 66), TMC(15, 67), TMC(15, 68),
   TMC(16, 31), TMC(17, 69), TMC(18, 72), TMC(19, 74), TMC(20, 59),
   TMC(21, 3), TMC(21, 4), TMC(22, 76), TMC(24, 4), TMC(24, 23),
   TMC(25, 77), TMC(26, 79), TMC(26, 81), TMC(27, 70), TMC(28, 82),
   TMC(29, 83), TMC(29, 84), TMC(30, 85), TMC(31, 74), TMC(31, 71),
   TMC(32, 31), TMC(33, 87), TMC(33, 89), TMC(34, 90), TMC(35, 59),
   TMC(35, 61), TMC(36, 92), TMC(37, 93), TMC(38, 94), TMC(38, 95),
   TMC(39, 74), TMC(39, 71), TMC(40, 98), TMC(40, 65), TMC(41, 101),
   TMC(42, 0), TMC(43, 17), TMC(44, 13), TMC(45, 11), TMC(46, 10),
   TMC(47, 102), TMC(48, 16), TMC(49, 103), TMC(50, 14), TMC(51, 106),
   TMC(52, 29), TMC(53, 12), TMC(54, 107), TMC(55, 108), TMC(56, 13),
   TMC(57, 12), TMC(58, 11), TMC(59, 10), TMC(60, 9), TMC(61, 9),
   TMC(62, 7), TMC(63, 55)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op dep_tc_def =
    DT([],
       [read"(%35 (|%1. ((%50 (%102 $0)) (%89 (|%17. (|%19. (%101 ((%43 $2) ((%37 $1) $0)))))))))"])
  val op ancestors_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. ((%49 (%97 ((%41 $1) $0))) (%72 (|%12. ((%38 $0) ((%45 (%56 (|%14. ((%45 ((%76 $0) $2)) (((%102 $3) $1) $0))))) (%29 (|%14. ((%55 ((%76 $0) $2)) (%117 (((%102 $3) $0) $1))))))))))))))"])
  val op scc_vs_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. ((%48 (%113 ((%41 $1) $0))) ((%84 (|%17. (|%19. (%101 ((%43 $3) ((%37 $1) $0)))))) $0))))))"])
  val op scc_set_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. ((%48 (%112 ((%42 $1) $0))) (%31 (|%20. ((%55 ((%45 ((%77 $0) $1)) (%117 ((%65 $0) (%68 (%108 $2)))))) (%113 ((%41 $2) $0))))))))))"])
  val op sum_scc_parents_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. ((%53 (%116 ((%42 $1) $0))) ((%36 ((%87 (|%20. (%109 (%107 ((%41 $2) ((%91 $0) (%97 ((%41 $2) $0)))))))) $0)) (%81 (%61 %96))))))))"])
  val op childless_vs_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. ((%48 (%100 ((%41 $1) $0))) (%31 (|%22. ((%55 ((%65 $1) $0)) (%117 (%103 ((%44 $2) ((%40 $1) $0))))))))))))"])
  val op childless_svs_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. ((%48 (%99 ((%42 $1) $0))) (%31 (|%20. ((%55 ((%77 $0) $1)) (%100 ((%41 $2) $0))))))))))"])
  val op problem_scc_set_def =
    DT([],
       [read"(%35 (|%1. ((%51 (%110 $0)) (%73 (|%20. ((%39 $0) (%113 ((%41 $1) $0))))))))"])
  val op childless_problem_scc_set_def =
    DT([],
       [read"(%35 (|%1. ((%51 (%98 $0)) (%73 (|%20. ((%39 $0) ((%45 (%113 ((%41 $1) $0))) (%100 ((%41 $1) $0)))))))))"])
  val op single_child_parents_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. ((%51 (%115 ((%41 $1) $0))) (%73 (|%22. ((%39 $0) ((%45 ((%85 $0) (%97 ((%41 $2) $1)))) ((%45 (%100 ((%41 (%107 ((%41 $2) ((%64 (%68 (%108 $2))) $1)))) $0))) (%113 ((%41 $2) $0))))))))))))"])
  val op single_child_ancestors_primitive_def =
    DT([],
       [read"((%52 %114) ((%95 (%58 (|%3. ((%45 (%94 $0)) (%35 (|%1. (%31 (|%20. (%31 (|%22. ((%55 ((%45 ((%45 ((%85 $1) (%68 (%108 $2)))) (%117 ((%49 $1) %66)))) ((%77 $0) (%115 ((%41 $2) $1))))) (($3 ((%41 (%107 ((%41 $2) ((%64 (%68 (%108 $2))) $1)))) $0)) ((%41 $2) $1))))))))))))) (|%10. (|%6. ((%105 $0) (|%1. (|%20. (%74 (((%63 ((%45 ((%85 $0) (%68 (%108 $1)))) (%117 ((%49 $0) %66)))) ((%92 (%115 ((%41 $1) $0))) (%60 ((%75 (|%22. ($4 ((%41 (%107 ((%41 $2) ((%64 (%68 (%108 $2))) $1)))) $0)))) (%115 ((%41 $1) $0)))))) %67)))))))))"])
  val op member_leaves_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. ((%51 (%104 ((%42 $1) $0))) ((%80 (|%20. ((%45 (%113 ((%41 $2) $0))) (%100 ((%41 $2) $0))))) $0))))))"])
  val op problem_wo_vs_ancestors_def =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. ((%54 (%111 ((%41 $1) $0))) (%107 ((%41 $1) ((%64 (%68 (%108 $1))) ((%91 $0) (%59 (%114 ((%41 $1) $0))))))))))))"])
  val op single_child_ancestors_def_1 =
    DT(["cheat"],
       [read"(%93 (|%26. (|%28. ((%46 (%62 (%68 (%108 (%71 $1))))) (%62 (%68 (%108 (%71 $0))))))))"])
  val op single_child_ancestors_def_2_1 =
    DT(["DISK_THM"],
       [read"(%31 (|%8. (%31 (|%11. ((%55 ((%45 (%69 $1)) ((%45 (%69 $0)) ((%85 $1) $0)))) ((%49 ((%79 $0) ((%64 $0) $1))) ((%64 $0) $1)))))))"])
  val op single_child_ancestors_def_2 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. (%30 (|%21. ((%55 ((%45 ((%85 $1) (%68 (%108 $2)))) (%117 ((%49 $1) %66)))) ((%46 (%62 (%68 (%108 (%107 ((%41 $2) ((%64 (%68 (%108 $2))) $1))))))) (%62 (%68 (%108 $2)))))))))))"])
  val op single_child_ancestors_ind =
    DT(["DISK_THM"],
       [read"(%34 (|%0. ((%55 (%35 (|%1. (%31 (|%20. ((%55 (%31 (|%22. ((%55 ((%45 ((%45 ((%85 $1) (%68 (%108 $2)))) (%117 ((%49 $1) %66)))) ((%77 $0) (%115 ((%41 $2) $1))))) ($3 ((%41 (%107 ((%41 $2) ((%64 (%68 (%108 $2))) $1)))) $0)))))) ($2 ((%41 $1) $0)))))))) (%35 (|%13. (%31 (|%16. ($2 ((%41 $1) $0)))))))))"])
  val op single_child_ancestors_def =
    DT(["DISK_THM"],
       [read"(%31 (|%20. (%35 (|%1. ((%51 (%114 ((%41 $0) $1))) (((%63 ((%45 ((%85 $1) (%68 (%108 $0)))) (%117 ((%49 $1) %66)))) ((%92 (%115 ((%41 $0) $1))) (%60 ((%75 (|%22. (%114 ((%41 (%107 ((%41 $1) ((%64 (%68 (%108 $1))) $2)))) $0)))) (%115 ((%41 $0) $1)))))) %67))))))"])
  val op scc_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. ((%55 (%70 $0)) (%70 (%104 ((%42 $1) $0))))))))"])
  val op scc_lemma_1_2 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. (%33 (|%4. ((%55 ((%77 $1) (%104 ((%42 $2) $0)))) (%113 ((%41 $2) $1)))))))))"])
  val op scc_lemma_1_3 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. (%33 (|%4. ((%55 ((%77 $1) (%104 ((%42 $2) $0)))) ((%77 $1) $0))))))))"])
  val op scc_lemma_1_4 =
    DT(["cheat"],
       [read"(%33 (|%4. ((%55 (%70 $0)) (%35 (|%1. (%31 (|%20. (%33 (|%5. ((%55 ((%51 (%104 ((%42 $2) $3))) ((%78 $1) $0))) ((%51 (%104 ((%42 (%111 ((%41 $2) $1))) $3))) $0)))))))))))"])
  val op scc_lemma_1_5 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. (%33 (|%4. ((%55 ((%77 $1) (%104 ((%42 $2) $0)))) (%100 ((%41 $2) $1)))))))))"])
  val op scc_main_lemma_1_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%29 (|%15. (%29 (|%18. ((%55 ((%45 (%106 $2)) (%101 ((%43 $2) ((%37 $1) $0))))) ((%45 ((%76 $1) (%68 (%108 $2)))) ((%76 $0) (%68 (%108 $2)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%29 (|%15. (%29 (|%18. ((%55 ((%45 (%106 $2)) (((%102 $2) $1) $0))) ((%76 $1) (%68 (%108 $2))))))))))"])
  val op scc_main_lemma_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. ((%55 ((%45 (%106 $1)) (%113 ((%41 $1) $0)))) ((%85 $0) (%68 (%108 $1))))))))"])
  val op scc_main_lemma_x =
    DT(["DISK_THM"],
       [read"(%31 (|%8. (%31 (|%11. (%29 (|%25. ((%55 ((%45 ((%76 $0) $2)) (%117 ((%76 $0) $1)))) (%117 ((%49 $2) $1)))))))))"])
  val op scc_main_lemma_1_xx =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. (%31 (|%22. ((%55 ((%45 (%113 ((%41 $2) $1))) ((%45 (%113 ((%41 $2) $0))) (%117 ((%49 $1) $0))))) ((%65 $1) $0))))))))"])
  val op scc_main_lemma_1_1_1_2 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%31 (|%20. (%31 (|%22. ((%55 ((%45 (%117 ((%65 $1) $0))) ((%45 (%113 ((%41 $2) $1))) (%113 ((%41 $2) $0))))) ((%49 $1) $0))))))))"])
  val op scc_main_lemma_1_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. (%31 (|%20. ((%55 ((%45 (%106 $2)) ((%45 ((%85 (%68 (%108 $2))) (%59 $1))) ((%45 (%112 ((%42 $2) $1))) (%113 ((%41 $2) $0)))))) ((%77 $0) $1))))))))"])
  val op scc_main_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. (%33 (|%4. ((%55 ((%45 (%106 $1)) ((%45 ((%85 (%68 (%108 $1))) (%59 $0))) (%112 ((%42 $1) $0))))) ((%51 (%98 $1)) (%104 ((%42 $1) $0))))))))"])
  val op scc_main_lemma_1_2_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%1. ((%55 (%106 $0)) ((%55 ((%49 (%68 (%108 $0))) %66)) (%31 (|%20. (%117 (%113 ((%41 $1) $0)))))))))"])
  val op scc_main_lemma_1_2_2_1 =
    DT(["cheat"],
       [read"(%35 (|%1. (%88 ((%83 (%90 (|%23. (|%24. (%103 ((%44 $2) ((%40 $0) $1))))))) (%110 $0)))))"])
  val op scc_main_lemma_1_2_2_2 =
    DT(["cheat"], [read"(%35 (|%1. (%70 (%110 $0))))"])
  val op scc_main_lemma_1_2_2_3 =
    DT(["cheat"],
       [read"(%35 (|%1. ((%55 ((%45 (%117 ((%49 (%68 (%108 $0))) %66))) (%106 $0))) (%57 (|%20. (%113 ((%41 $1) $0)))))))"])
  val op scc_main_lemma_1_2_2_4 =
    DT(["cheat"],
       [read"(%32 (|%2. (%31 (|%8. (%29 (|%7. ((%55 (%29 (|%25. ((%55 ((((%82 (%89 $3)) $2) $0) $1)) (%117 ((%76 $0) $2)))))) (%29 (|%27. ((%55 ((%76 $0) $2)) (%117 (($3 $0) $1))))))))))))"])
  val op scc_main_lemma_1_2_2 =
    DT(["cheat"],
       [read"(%35 (|%1. ((%55 ((%45 (%106 $0)) (%117 ((%49 (%68 (%108 $0))) %66)))) (%57 (|%20. ((%45 (%113 ((%41 $1) $0))) (%100 ((%41 $1) $0))))))))"])
  val op scc_main_lemma_1_2 =
    DT(["DISK_THM", "cheat"],
       [read"(%35 (|%1. ((%55 (%106 $0)) ((%48 ((%49 (%68 (%108 $0))) %66)) ((%51 (%98 $0)) %67)))))"])
  val op scc_main_lemma_1_3 =
    DT(["cheat"],
       [read"(%35 (|%1. (%33 (|%4. (%33 (|%5. ((%55 ((%45 (%112 ((%42 $2) $1))) ((%86 $0) $1))) (%112 ((%42 (%107 ((%41 $2) ((%64 (%68 (%108 $2))) (%59 $0))))) $1)))))))))"])
  val op scc_main_lemma_1_4 =
    DT(["cheat"],
       [read"(%35 (|%1. (%31 (|%20. (%33 (|%4. ((%55 ((%45 (%112 ((%42 $2) $0))) ((%45 (%113 ((%41 $2) $1))) ((%85 (%68 (%108 $2))) (%59 $0))))) ((%86 (%114 ((%41 $2) $1))) $0))))))))"])
  val op scc_main_lemma_1_5 =
    DT(["cheat"],
       [read"(%35 (|%1. (%31 (|%20. (%31 (|%22. ((%55 ((%85 (%68 (%108 $2))) $1)) ((%85 (%68 (%108 (%107 ((%41 $2) $0))))) $1))))))))"])
  val op scc_main_lemma_1_6 =
    DT(["cheat"],
       [read"(%35 (|%1. (%31 (|%20. (%33 (|%4. (%33 (|%5. ((%55 ((%45 ((%51 (%104 ((%42 $3) $1))) ((%78 $2) $0))) (%117 ((%77 $2) $0)))) ((%53 (%116 ((%42 (%111 ((%41 $3) $2))) (%104 ((%42 (%111 ((%41 $3) $2))) $1))))) (%116 ((%42 $3) $0))))))))))))"])
  val op scc_main_lemma_1_7 =
    DT(["cheat"],
       [read"(%35 (|%1. (%31 (|%20. ((%55 ((%45 (%100 ((%41 $1) $0))) (%113 ((%41 $1) $0)))) ((%47 (%109 $1)) ((%36 (%109 (%111 ((%41 $1) $0)))) (%109 (%107 ((%41 $1) ((%91 $0) (%97 ((%41 $1) $0)))))))))))))"])
  val op scc_main_lemma_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%9. ((%55 (%70 $0)) (%33 (|%4. (%35 (|%1. ((%55 ((%45 (%106 $0)) ((%45 (%112 ((%42 $0) $1))) ((%45 ((%85 (%68 (%108 $0))) (%59 $1))) ((%45 ((%45 (%117 ((%51 $1) %67))) (%117 ((%51 $1) ((%78 %66) %67))))) ((%45 (%70 $1)) ((%51 $2) (%104 ((%42 $0) $1))))))))) ((%47 (%109 $0)) (%116 ((%42 $0) (%104 ((%42 $0) $1)))))))))))))"])
  val op scc_main_lemma =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%4. (%35 (|%1. ((%55 ((%45 (%106 $0)) ((%45 (%112 ((%42 $0) $1))) ((%45 ((%85 (%68 (%108 $0))) (%59 $1))) ((%45 (%117 ((%49 (%59 $1)) %66))) (%70 $1)))))) ((%47 (%109 $0)) (%116 ((%42 $0) (%104 ((%42 $0) $1))))))))))"])
  end
  val _ = DB.bindl "SCCGraphPlanTheorem"
  [("dep_tc_def",dep_tc_def,DB.Def),
   ("ancestors_def",ancestors_def,DB.Def),
   ("scc_vs_def",scc_vs_def,DB.Def), ("scc_set_def",scc_set_def,DB.Def),
   ("sum_scc_parents_def",sum_scc_parents_def,DB.Def),
   ("childless_vs_def",childless_vs_def,DB.Def),
   ("childless_svs_def",childless_svs_def,DB.Def),
   ("problem_scc_set_def",problem_scc_set_def,DB.Def),
   ("childless_problem_scc_set_def",childless_problem_scc_set_def,DB.Def),
   ("single_child_parents_def",single_child_parents_def,DB.Def),
   ("single_child_ancestors_primitive_def",
    single_child_ancestors_primitive_def,
    DB.Def), ("member_leaves_def",member_leaves_def,DB.Def),
   ("problem_wo_vs_ancestors_def",problem_wo_vs_ancestors_def,DB.Def),
   ("single_child_ancestors_def_1",single_child_ancestors_def_1,DB.Thm),
   ("single_child_ancestors_def_2_1",
    single_child_ancestors_def_2_1,
    DB.Thm),
   ("single_child_ancestors_def_2",single_child_ancestors_def_2,DB.Thm),
   ("single_child_ancestors_ind",single_child_ancestors_ind,DB.Thm),
   ("single_child_ancestors_def",single_child_ancestors_def,DB.Thm),
   ("scc_lemma_1_1",scc_lemma_1_1,DB.Thm),
   ("scc_lemma_1_2",scc_lemma_1_2,DB.Thm),
   ("scc_lemma_1_3",scc_lemma_1_3,DB.Thm),
   ("scc_lemma_1_4",scc_lemma_1_4,DB.Thm),
   ("scc_lemma_1_5",scc_lemma_1_5,DB.Thm),
   ("scc_main_lemma_1_1_1_1_1_1",scc_main_lemma_1_1_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_1_1",scc_main_lemma_1_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_1",scc_main_lemma_1_1_1_1,DB.Thm),
   ("scc_main_lemma_x",scc_main_lemma_x,DB.Thm),
   ("scc_main_lemma_1_xx",scc_main_lemma_1_xx,DB.Thm),
   ("scc_main_lemma_1_1_1_2",scc_main_lemma_1_1_1_2,DB.Thm),
   ("scc_main_lemma_1_1_1",scc_main_lemma_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1",scc_main_lemma_1_1,DB.Thm),
   ("scc_main_lemma_1_2_1",scc_main_lemma_1_2_1,DB.Thm),
   ("scc_main_lemma_1_2_2_1",scc_main_lemma_1_2_2_1,DB.Thm),
   ("scc_main_lemma_1_2_2_2",scc_main_lemma_1_2_2_2,DB.Thm),
   ("scc_main_lemma_1_2_2_3",scc_main_lemma_1_2_2_3,DB.Thm),
   ("scc_main_lemma_1_2_2_4",scc_main_lemma_1_2_2_4,DB.Thm),
   ("scc_main_lemma_1_2_2",scc_main_lemma_1_2_2,DB.Thm),
   ("scc_main_lemma_1_2",scc_main_lemma_1_2,DB.Thm),
   ("scc_main_lemma_1_3",scc_main_lemma_1_3,DB.Thm),
   ("scc_main_lemma_1_4",scc_main_lemma_1_4,DB.Thm),
   ("scc_main_lemma_1_5",scc_main_lemma_1_5,DB.Thm),
   ("scc_main_lemma_1_6",scc_main_lemma_1_6,DB.Thm),
   ("scc_main_lemma_1_7",scc_main_lemma_1_7,DB.Thm),
   ("scc_main_lemma_1",scc_main_lemma_1,DB.Thm),
   ("scc_main_lemma",scc_main_lemma,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("SCCTheory.SCC_grammars",SCCTheory.SCC_grammars),
                         ("GraphPlanTheoremTheory.GraphPlanTheorem_grammars",
                          GraphPlanTheoremTheory.GraphPlanTheorem_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dep_tc", (Term.prim_mk_const { Name = "dep_tc", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dep_tc", (Term.prim_mk_const { Name = "dep_tc", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ancestors", (Term.prim_mk_const { Name = "ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ancestors", (Term.prim_mk_const { Name = "ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_vs", (Term.prim_mk_const { Name = "scc_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_vs", (Term.prim_mk_const { Name = "scc_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_set", (Term.prim_mk_const { Name = "scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_set", (Term.prim_mk_const { Name = "scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sum_scc_parents", (Term.prim_mk_const { Name = "sum_scc_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sum_scc_parents", (Term.prim_mk_const { Name = "sum_scc_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_vs", (Term.prim_mk_const { Name = "childless_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_vs", (Term.prim_mk_const { Name = "childless_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_svs", (Term.prim_mk_const { Name = "childless_svs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_svs", (Term.prim_mk_const { Name = "childless_svs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_scc_set", (Term.prim_mk_const { Name = "problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_scc_set", (Term.prim_mk_const { Name = "problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_problem_scc_set", (Term.prim_mk_const { Name = "childless_problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_problem_scc_set", (Term.prim_mk_const { Name = "childless_problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_parents", (Term.prim_mk_const { Name = "single_child_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_parents", (Term.prim_mk_const { Name = "single_child_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_ancestors", (Term.prim_mk_const { Name = "single_child_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_ancestors", (Term.prim_mk_const { Name = "single_child_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("member_leaves", (Term.prim_mk_const { Name = "member_leaves", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("member_leaves", (Term.prim_mk_const { Name = "member_leaves", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_wo_vs_ancestors", (Term.prim_mk_const { Name = "problem_wo_vs_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_wo_vs_ancestors", (Term.prim_mk_const { Name = "problem_wo_vs_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val SCCGraphPlanTheorem_grammars = Parse.current_lgrms()
  end
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "SCCGraphPlanTheorem",
    thydataty = "compute",
    data =
        "SCCGraphPlanTheorem.dep_tc_def SCCGraphPlanTheorem.single_child_ancestors_def SCCGraphPlanTheorem.problem_wo_vs_ancestors_def SCCGraphPlanTheorem.member_leaves_def SCCGraphPlanTheorem.single_child_parents_def SCCGraphPlanTheorem.sum_scc_parents_def SCCGraphPlanTheorem.childless_problem_scc_set_def SCCGraphPlanTheorem.problem_scc_set_def SCCGraphPlanTheorem.childless_svs_def SCCGraphPlanTheorem.childless_vs_def SCCGraphPlanTheorem.scc_set_def SCCGraphPlanTheorem.scc_vs_def SCCGraphPlanTheorem.ancestors_def"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "SCCGraphPlanTheorem"
end
