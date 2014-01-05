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
          Arbnum.fromString "1388744242",
          Arbnum.fromString "587867")
          [("SCC",
           Arbnum.fromString "1388744238",
           Arbnum.fromString "551178"),
           ("GraphPlanTheorem",
           Arbnum.fromString "1388744218",
           Arbnum.fromString "499585")];
  val _ = Theory.incorporate_types "SCCGraphPlanTheorem" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("num", "num"), ID("pair", "prod"),
   ID("min", "bool"), ID("FM_plan", "problem"), ID("finite_map", "fmap"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("arithmetic", "<="), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("pred_set", "BIGUNION"),
   ID("arithmetic", "BIT1"), ID("pred_set", "DELETE"),
   ID("pred_set", "DIFF"), ID("pred_set", "DISJOINT"),
   ID("finite_map", "DRESTRICT"), ID("pred_set", "EMPTY"),
   ID("finite_map", "FDOM"), ID("pred_set", "FINITE"), ID("pair", "FST"),
   ID("pred_set", "GSPEC"), ID("bool", "IN"), ID("pred_set", "INSERT"),
   ID("pred_set", "INTER"), ID("arithmetic", "NUMERAL"),
   ID("pred_set", "REL_RESTRICT"), ID("SCC", "SCC"), ID("pair", "SND"),
   ID("pred_set", "SUBSET"), ID("pred_set", "SUM_IMAGE"),
   ID("relation", "StrongOrder"), ID("relation", "TC"),
   ID("pred_set", "UNION"), ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("GraphPlanTheorem", "action_proj"),
   ID("SCCGraphPlanTheorem", "ancestors"),
   ID("SCCGraphPlanTheorem", "childless_problem_scc_set"),
   ID("SCCGraphPlanTheorem", "childless_svs"),
   ID("SCCGraphPlanTheorem", "childless_vs"),
   ID("GraphPlanTheorem", "dep"), ID("SCCGraphPlanTheorem", "dep_tc"),
   ID("GraphPlanTheorem", "dep_var_set"),
   ID("SCCGraphPlanTheorem", "member_leaves"),
   ID("FM_plan", "planning_problem"), ID("GraphPlanTheorem", "prob_proj"),
   ID("FM_plan", "problem_A"), ID("FM_plan", "problem_I"),
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
   TYOP [0, 8, 4], TYOP [0, 3, 4], TYOP [0, 5, 10], TYOP [0, 8, 1],
   TYOP [0, 6, 1], TYOP [0, 8, 5], TYOP [0, 5, 4], TYOP [0, 6, 4],
   TYOP [0, 2, 3], TYOP [0, 5, 17], TYOP [0, 8, 3], TYV "'c",
   TYOP [5, 2, 20], TYV "'b", TYOP [5, 2, 22], TYOP [2, 23, 21],
   TYOP [5, 2, 1], TYOP [2, 25, 25], TYOP [0, 23, 1], TYOP [0, 27, 1],
   TYOP [0, 4, 1], TYOP [0, 17, 1], TYOP [0, 30, 1], TYOP [0, 29, 1],
   TYOP [0, 5, 1], TYOP [0, 33, 1], TYOP [0, 24, 1], TYOP [0, 35, 1],
   TYOP [0, 26, 1], TYOP [0, 37, 1], TYOP [0, 0, 0], TYOP [0, 0, 39],
   TYOP [2, 2, 2], TYOP [0, 2, 41], TYOP [0, 2, 42], TYOP [2, 2, 1],
   TYOP [0, 1, 44], TYOP [0, 2, 45], TYOP [2, 3, 1], TYOP [0, 1, 47],
   TYOP [0, 3, 48], TYOP [2, 3, 3], TYOP [0, 3, 50], TYOP [0, 3, 51],
   TYOP [0, 3, 8], TYOP [0, 5, 53], TYOP [0, 4, 6], TYOP [0, 5, 55],
   TYOP [2, 5, 41], TYOP [0, 41, 57], TYOP [0, 5, 58], TYOP [2, 5, 50],
   TYOP [0, 50, 60], TYOP [0, 5, 61], TYOP [2, 24, 3], TYOP [0, 3, 63],
   TYOP [0, 24, 64], TYOP [2, 26, 3], TYOP [0, 3, 66], TYOP [0, 26, 67],
   TYOP [0, 1, 1], TYOP [0, 1, 69], TYOP [0, 0, 1], TYOP [0, 0, 71],
   TYOP [0, 17, 30], TYOP [0, 4, 29], TYOP [0, 5, 33], TYOP [0, 4, 3],
   TYOP [0, 4, 10], TYOP [0, 3, 3], TYOP [0, 3, 78], TYOP [0, 3, 23],
   TYOP [0, 23, 80], TYOP [0, 23, 3], TYOP [0, 21, 3], TYOP [0, 25, 3],
   TYOP [0, 24, 23], TYOP [0, 26, 25], TYOP [0, 2, 44], TYOP [0, 87, 3],
   TYOP [0, 3, 47], TYOP [0, 89, 4], TYOP [0, 2, 4], TYOP [0, 3, 29],
   TYOP [0, 26, 38], TYOP [0, 4, 4], TYOP [0, 3, 94], TYOP [0, 4, 94],
   TYOP [0, 3, 17], TYOP [0, 17, 97], TYOP [0, 10, 77], TYOP [0, 17, 4],
   TYOP [0, 24, 21], TYOP [0, 4, 0], TYOP [0, 3, 0], TYOP [0, 103, 102],
   TYOP [0, 10, 1], TYOP [0, 17, 17], TYOP [0, 10, 10], TYOP [0, 63, 24],
   TYOP [0, 66, 26], TYOP [0, 57, 1], TYOP [0, 60, 1], TYOP [0, 5, 37],
   TYOP [0, 5, 25], TYOP [0, 5, 0]]
  end
  val _ = Theory.incorporate_consts "SCCGraphPlanTheorem" tyvector
     [("sum_scc_parents", 7), ("single_child_parents", 9),
      ("single_child_ancestors", 11), ("scc_vs", 12), ("scc_set", 13),
      ("problem_wo_vs_ancestors", 14), ("problem_scc_set", 15),
      ("member_leaves", 16), ("dep_tc", 18), ("childless_vs", 12),
      ("childless_svs", 13), ("childless_problem_scc_set", 15),
      ("ancestors", 19)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P", 3), TMV("PROB", 5), TMV("R", 17), TMV("R'", 17), TMV("S", 4),
   TMV("S'", 4), TMV("a", 24), TMV("a", 26), TMV("f", 23), TMV("fdom", 3),
   TMV("min", 2), TMV("s", 3), TMV("s", 4), TMV("t", 3), TMV("v", 2),
   TMV("v'", 2), TMV("v1", 2), TMV("v1'", 2), TMV("v2", 2), TMV("v2'", 2),
   TMV("vs", 3), TMV("vs'", 3), TMV("vs''", 3), TMV("vs1", 3),
   TMV("vs2", 3), TMV("x", 2), TMV("x'", 2), TMV("y", 2), TMC(6, 4),
   TMC(6, 28), TMC(6, 29), TMC(6, 31), TMC(6, 32), TMC(6, 34), TMC(6, 36),
   TMC(6, 38), TMC(7, 40), TMC(8, 43), TMC(8, 46), TMC(8, 49), TMC(8, 52),
   TMC(8, 54), TMC(8, 56), TMC(8, 59), TMC(8, 62), TMC(8, 65), TMC(8, 68),
   TMC(9, 70), TMC(10, 72), TMC(11, 70), TMC(11, 10), TMC(11, 73),
   TMC(11, 74), TMC(11, 72), TMC(11, 75), TMC(12, 70), TMC(13, 4),
   TMC(13, 29), TMC(14, 76), TMC(15, 39), TMC(16, 77), TMC(17, 79),
   TMC(18, 10), TMC(19, 81), TMC(20, 3), TMC(20, 4), TMC(21, 82),
   TMC(21, 83), TMC(21, 84), TMC(22, 29), TMC(23, 85), TMC(23, 86),
   TMC(24, 88), TMC(24, 90), TMC(25, 91), TMC(25, 92), TMC(25, 93),
   TMC(26, 95), TMC(27, 96), TMC(28, 39), TMC(29, 98), TMC(29, 99),
   TMC(30, 100), TMC(31, 101), TMC(31, 86), TMC(32, 10), TMC(32, 74),
   TMC(33, 104), TMC(34, 105), TMC(35, 106), TMC(35, 107), TMC(36, 79),
   TMC(37, 0), TMC(38, 70), TMC(39, 108), TMC(39, 109), TMC(40, 19),
   TMC(41, 15), TMC(42, 13), TMC(43, 12), TMC(44, 110), TMC(45, 18),
   TMC(46, 111), TMC(47, 16), TMC(48, 33), TMC(49, 14), TMC(50, 112),
   TMC(51, 113), TMC(52, 114), TMC(53, 15), TMC(54, 14), TMC(55, 13),
   TMC(56, 12), TMC(57, 11), TMC(58, 9), TMC(59, 7), TMC(60, 69)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op dep_tc_def =
    DT([],
       [read"(%33 (|%1. ((%51 (%101 $0)) (%89 (|%17. (|%19. (%100 ((%43 $2) ((%37 $1) $0)))))))))"])
  val op ancestors_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. ((%50 (%96 ((%41 $1) $0))) (%72 (|%14. ((%38 $0) ((%47 (%56 (|%15. ((%47 ((%74 $0) $2)) (((%101 $3) $1) $0))))) (%28 (|%15. ((%55 ((%74 $0) $2)) (%116 (((%101 $3) $0) $1))))))))))))))"])
  val op scc_vs_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. ((%49 (%112 ((%41 $1) $0))) ((%82 (|%17. (|%19. (%100 ((%43 $3) ((%37 $1) $0)))))) $0))))))"])
  val op scc_set_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. ((%49 (%111 ((%42 $1) $0))) (%30 (|%20. ((%55 ((%47 ((%75 $0) $1)) (%116 ((%62 $0) (%68 (%107 $2)))))) (%112 ((%41 $2) $0))))))))))"])
  val op sum_scc_parents_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. ((%53 (%115 ((%42 $1) $0))) ((%36 ((%87 (|%20. (%108 (%105 ((%41 $2) ((%91 $0) (%96 ((%41 $2) $0)))))))) $0)) (%79 (%59 %92))))))))"])
  val op childless_vs_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. ((%49 (%99 ((%41 $1) $0))) (%30 (|%21. (%116 (%102 ((%44 $2) ((%40 $1) $0)))))))))))"])
  val op childless_svs_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. ((%49 (%98 ((%42 $1) $0))) (%30 (|%20. ((%55 ((%75 $0) $1)) (%99 ((%41 $2) $0))))))))))"])
  val op problem_scc_set_def =
    DT([],
       [read"(%33 (|%1. ((%52 (%109 $0)) (%73 (|%20. ((%39 $0) (%112 ((%41 $1) $0))))))))"])
  val op childless_problem_scc_set_def =
    DT([],
       [read"(%33 (|%1. ((%52 (%97 $0)) (%73 (|%20. ((%39 $0) ((%47 (%112 ((%41 $1) $0))) (%99 ((%41 $1) $0)))))))))"])
  val op single_child_parents_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. ((%52 (%114 ((%41 $1) $0))) (%73 (|%21. ((%39 $0) ((%47 ((%85 $0) (%96 ((%41 $2) $1)))) ((%47 (%99 ((%41 (%105 ((%41 $2) ((%61 (%68 (%107 $2))) $1)))) $0))) (%112 ((%41 $2) $0))))))))))))"])
  val op single_child_ancestors_def =
    DT([],
       [read"(%33 (|%1. (%30 (|%20. ((%52 ((%113 $1) $0)) (%73 (|%21. ((%39 $0) ((%47 (%112 ((%41 $2) $0))) ((%47 (((%90 (|%20. (|%21. (%102 ((%44 $4) ((%40 $1) $0)))))) $0) $1)) (%30 (|%22. ((%55 ((%47 (((%90 (|%20. (|%21. (%102 ((%44 $5) ((%40 $1) $0)))))) $1) $0)) ((%47 (%99 ((%41 $3) $0))) (%112 ((%41 $3) $0))))) ((%50 $0) $2))))))))))))))"])
  val op member_leaves_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. ((%52 (%103 ((%42 $1) $0))) ((%78 (|%20. ((%47 (%112 ((%41 $2) $0))) (%99 ((%41 $2) $0))))) $0))))))"])
  val op problem_wo_vs_ancestors_def =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. ((%54 (%110 ((%41 $1) $0))) (%105 ((%41 $1) ((%61 (%68 (%107 $1))) ((%91 $0) (%58 ((%113 $1) $0)))))))))))"])
  val op scc_main_lemma_x =
    DT(["DISK_THM"],
       [read"(%30 (|%11. (%30 (|%13. (%28 (|%25. ((%55 ((%47 ((%74 $0) $2)) (%116 ((%74 $0) $1)))) (%116 ((%50 $2) $1)))))))))"])
  val op scc_main_lemma_1_xx =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 ((%47 (%112 ((%41 $2) $1))) ((%47 (%112 ((%41 $2) $0))) (%116 ((%50 $1) $0))))) ((%62 $1) $0))))))))"])
  val op scc_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. ((%55 (%69 $0)) (%69 (%103 ((%42 $1) $0))))))))"])
  val op scc_lemma_1_2 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%32 (|%4. ((%55 ((%75 $1) (%103 ((%42 $2) $0)))) (%112 ((%41 $2) $1)))))))))"])
  val op scc_lemma_1_3 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%32 (|%4. ((%55 ((%75 $1) (%103 ((%42 $2) $0)))) ((%75 $1) $0))))))))"])
  val op scc_lemma_1_5 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%32 (|%4. ((%55 ((%75 $1) (%103 ((%42 $2) $0)))) (%99 ((%41 $2) $1)))))))))"])
  val op scc_lemma_1_4_1_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 ((%47 (%112 ((%41 $2) $0))) (%99 ((%41 $2) $0)))) ((%62 $0) (%58 ((%113 $2) $1))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%30 (|%9. (%30 (|%20. (%28 (|%14. (%29 (|%8. ((%55 ((%47 (%116 ((%74 $1) $2))) ((%47 ((%85 (%66 $0)) $3)) ((%74 $1) (%66 $0))))) ((%74 $1) (%66 ((%63 $0) ((%61 $3) $2)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%28 (|%14. (%35 (|%7. ((%55 ((%47 (%116 ((%74 $1) $2))) ((%47 ((%76 $0) (%106 $3))) (%104 $3)))) ((%47 ((%55 ((%74 $1) (%68 (%71 $0)))) ((%74 $1) (%68 (%71 (%95 ((%46 $0) ((%61 (%68 (%107 $3))) $2)))))))) ((%55 ((%74 $1) (%68 (%84 $0)))) ((%74 $1) (%68 (%84 (%95 ((%46 $0) ((%61 (%68 (%107 $3))) $2)))))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. (%28 (|%14. (%28 (|%15. ((%55 ((%47 (%104 $4)) ((%47 ((%74 $1) $2)) ((%47 ((%74 $0) $2)) ((%62 $3) $2))))) ((%55 (%100 ((%43 $4) ((%37 $1) $0)))) (%100 ((%43 (%105 ((%41 $4) ((%61 (%68 (%107 $4))) $3)))) ((%37 $1) $0)))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_2 =
    DT(["DISK_THM"],
       [read"(%31 (|%2. (%31 (|%3. (%30 (|%0. ((%55 (%28 (|%25. (%28 (|%27. ((%55 ((%47 ($2 $1)) ($2 $0))) ((%47 ((%55 (($4 $1) $0)) (($3 $1) $0))) (((%89 (|%25. (|%27. ((%47 (($6 $1) $0)) ((%47 ($4 $1)) ($4 $0)))))) $1) $0)))))))) (%28 (|%25. (%28 (|%27. ((%55 ((%47 ($2 $1)) ($2 $0))) (((%89 $3) $1) $0)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_4 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%28 (|%14. (%28 (|%15. ((%55 (%100 ((%43 (%105 ((%41 $3) ((%61 (%68 (%107 $3))) $2)))) ((%37 $1) $0)))) (%100 ((%43 $3) ((%37 $1) $0))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 ((%47 (%104 $2)) ((%47 (%112 ((%41 $2) $0))) ((%62 $1) $0)))) (%112 ((%41 (%105 ((%41 $2) ((%61 (%68 (%107 $2))) $1)))) $0)))))))))"])
  val op scc_lemma_1_4_1_1_2_2_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%6. (%30 (|%20. ((%47 ((%85 (%66 (%70 (%94 ((%45 $1) $0))))) (%66 (%70 $1)))) ((%85 (%67 (%83 (%94 ((%45 $1) $0))))) (%67 (%83 $1))))))))"])
  val op scc_lemma_1_4_1_1_2_2_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%6. (%28 (|%14. (%30 (|%20. ((%47 ((%55 (%116 ((%74 $1) (%66 (%70 $2))))) (%116 ((%74 $1) (%66 (%70 (%94 ((%45 $2) $0)))))))) ((%55 (%116 ((%74 $1) (%67 (%83 $2))))) (%116 ((%74 $1) (%67 (%83 (%94 ((%45 $2) $0))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_2_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. (%30 (|%22. ((%55 (%116 (%102 ((%44 $3) ((%40 $2) $1))))) (%116 (%102 ((%44 (%105 ((%41 $3) $0))) ((%40 $2) $1)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_2 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 (%99 ((%41 $2) $0))) (%99 ((%41 (%105 ((%41 $2) ((%61 (%68 (%107 $2))) $1)))) $0)))))))))"])
  val op scc_lemma_1_4_1_1_2 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. (%32 (|%4. ((%55 ((%47 (%104 $3)) ((%47 ((%62 $2) $1)) ((%75 $1) (%103 ((%42 $3) $0)))))) ((%75 $1) (%103 ((%42 (%105 ((%41 $3) ((%61 (%68 (%107 $3))) $2)))) $0))))))))))))"])
  val op scc_lemma_1_4_1_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. (%32 (|%4. ((%55 ((%47 (%104 $3)) ((%47 (%112 ((%41 $3) $2))) ((%47 (%116 ((%50 $2) $1))) ((%75 $1) (%103 ((%42 $3) $0))))))) ((%75 $1) (%103 ((%42 (%110 ((%41 $3) $2))) $0))))))))))))"])
  val op scc_lemma_1_4_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%1. (%32 (|%4. (%30 (|%20. ((%55 ((%47 (%104 $2)) (%112 ((%41 $2) $0)))) ((%86 ((%60 (%103 ((%42 $2) $1))) $0)) (%103 ((%42 (%110 ((%41 $2) $0))) $1))))))))))"])
  val op scc_lemma_1_4_2 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%22. (%32 (|%4. (%30 (|%21. ((%55 ((%47 (%116 ((%75 $0) ((%113 $4) $3)))) ((%47 (%116 ((%75 $0) ((%60 (%103 ((%42 $4) $1))) $2)))) ((%85 $2) $3)))) (%116 ((%75 $0) (%103 ((%42 (%105 ((%41 $4) ((%61 (%68 (%107 $4))) $3)))) $1)))))))))))))))"])
  val op scc_lemma_1_4_3_1 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. (%30 (|%22. ((%55 (((%90 (|%20. (|%21. (%102 ((%44 $5) ((%40 $1) $0)))))) $2) ((%91 $1) $0))) ((%93 (((%90 (|%20. (|%21. (%102 ((%44 $5) ((%40 $1) $0)))))) $2) $1)) (((%90 (|%20. (|%21. (%102 ((%44 $5) ((%40 $1) $0)))))) $2) $0)))))))))))"])
  val op scc_lemma_1_4_3_2 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%32 (|%4. ((%55 (((%90 (|%20. (|%21. (%102 ((%44 $4) ((%40 $1) $0)))))) $1) (%58 $0))) (%57 (|%21. ((%47 ((%75 $0) $1)) (((%90 (|%20. (|%21. (%102 ((%44 $5) ((%40 $1) $0)))))) $2) $0)))))))))))"])
  val op scc_lemma_1_4_3_3 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. ((%55 (%116 (%99 ((%41 $1) $0)))) ((%52 ((%113 $1) $0)) %65))))))"])
  val op scc_lemma_1_4_3_4_1 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 (((%90 (|%20. (|%21. (%102 ((%44 $4) ((%40 $1) $0)))))) $1) $0)) ((%93 ((%62 $1) $0)) ((%47 ((%50 $1) $0)) (%116 (%112 ((%41 $2) $1))))))))))))"])
  val op scc_lemma_1_4_3_4 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 ((%47 (%112 ((%41 $2) $1))) ((%75 $0) ((%113 $2) $1)))) ((%47 ((%62 $1) $0)) (%116 ((%50 $0) %64))))))))))"])
  val op scc_lemma_1_4_3_5 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 (((%90 (|%20. (|%21. (%102 ((%44 $4) ((%40 $1) $0)))))) $1) ((%91 $0) (%58 ((%113 $2) $0))))) (((%90 (|%20. (|%21. (%102 ((%44 $4) ((%40 $1) $0)))))) $1) $0))))))))"])
  val op scc_lemma_1_4_3_6 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. ((%55 (%116 ((%52 ((%113 $1) $0)) %65))) (%116 ((%50 (%58 ((%113 $1) $0))) %64)))))))"])
  val op scc_lemma_1_4_3 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. ((%55 (%112 ((%41 $1) $0))) ((%52 ((%113 $1) ((%91 $0) (%58 ((%113 $1) $0))))) %65))))))"])
  val op scc_lemma_1_4_4 =
    DT(["DISK_THM"],
       [read"(%30 (|%11. (%30 (|%13. ((%55 (%28 (|%25. ((%55 (%116 ((%74 $0) $2))) (%116 ((%74 $0) $1)))))) ((%50 ((%61 $0) $1)) %64))))))"])
  val op scc_lemma_1_4 =
    DT(["DISK_THM", "cheat"],
       [read"(%32 (|%4. ((%55 (%69 $0)) (%33 (|%1. (%30 (|%20. (%32 (|%5. ((%55 ((%47 (%104 $2)) ((%47 (%112 ((%41 $2) $1))) ((%47 (%116 ((%75 $1) $0))) ((%52 (%103 ((%42 $2) $3))) ((%77 $1) $0)))))) ((%52 (%103 ((%42 (%110 ((%41 $2) $1))) $3))) $0)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%28 (|%16. (%28 (|%18. ((%55 ((%47 (%104 $2)) (%100 ((%43 $2) ((%37 $1) $0))))) ((%47 ((%74 $1) (%68 (%107 $2)))) ((%74 $0) (%68 (%107 $2)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%28 (|%16. (%28 (|%18. ((%55 ((%47 (%104 $2)) (((%101 $2) $1) $0))) ((%74 $1) (%68 (%107 $2))))))))))"])
  val op scc_main_lemma_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. ((%55 ((%47 (%104 $1)) (%112 ((%41 $1) $0)))) ((%85 $0) (%68 (%107 $1))))))))"])
  val op scc_main_lemma_1_1_1_2 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 ((%47 (%116 ((%62 $1) $0))) ((%47 (%112 ((%41 $2) $1))) (%112 ((%41 $2) $0))))) ((%50 $1) $0))))))))"])
  val op scc_main_lemma_1_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. (%30 (|%20. ((%55 ((%47 (%104 $2)) ((%47 ((%85 (%68 (%107 $2))) (%58 $1))) ((%47 (%111 ((%42 $2) $1))) (%112 ((%41 $2) $0)))))) ((%75 $0) $1))))))))"])
  val op scc_main_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. (%32 (|%4. ((%55 ((%47 (%104 $1)) ((%47 ((%85 (%68 (%107 $1))) (%58 $0))) (%111 ((%42 $1) $0))))) ((%52 (%97 $1)) (%103 ((%42 $1) $0))))))))"])
  val op scc_main_lemma_1_2_1 =
    DT(["DISK_THM"],
       [read"(%33 (|%1. ((%55 (%104 $0)) ((%55 ((%50 (%68 (%107 $0))) %64)) (%30 (|%20. (%116 (%112 ((%41 $1) $0)))))))))"])
  val op scc_main_lemma_1_2_2_1 =
    DT(["cheat"],
       [read"(%33 (|%1. (%88 ((%81 (%90 (|%23. (|%24. (%102 ((%44 $2) ((%40 $0) $1))))))) (%109 $0)))))"])
  val op scc_main_lemma_1_2_2_2 =
    DT(["cheat"], [read"(%33 (|%1. (%69 (%109 $0))))"])
  val op scc_main_lemma_1_2_2_3 =
    DT(["cheat"],
       [read"(%33 (|%1. ((%55 ((%47 (%116 ((%50 (%68 (%107 $0))) %64))) (%104 $0))) (%57 (|%20. (%112 ((%41 $1) $0)))))))"])
  val op scc_main_lemma_1_2_2_4 =
    DT(["cheat"],
       [read"(%31 (|%2. (%30 (|%11. (%28 (|%10. ((%55 (%28 (|%25. ((%55 ((((%80 (%89 $3)) $2) $0) $1)) (%116 ((%74 $0) $2)))))) (%28 (|%26. ((%55 ((%74 $0) $2)) (%116 (($3 $0) $1))))))))))))"])
  val op scc_main_lemma_1_2_2 =
    DT(["cheat"],
       [read"(%33 (|%1. ((%55 ((%47 (%104 $0)) (%116 ((%50 (%68 (%107 $0))) %64)))) (%57 (|%20. ((%47 (%112 ((%41 $1) $0))) (%99 ((%41 $1) $0))))))))"])
  val op scc_main_lemma_1_2 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%1. ((%55 (%104 $0)) ((%49 ((%50 (%68 (%107 $0))) %64)) ((%52 (%97 $0)) %65)))))"])
  val op scc_main_lemma_1_3 =
    DT(["cheat"],
       [read"(%33 (|%1. (%32 (|%4. (%32 (|%5. ((%55 ((%47 (%111 ((%42 $2) $1))) ((%86 $0) $1))) (%111 ((%42 (%105 ((%41 $2) ((%61 (%68 (%107 $2))) (%58 $0))))) $1)))))))))"])
  val op scc_main_lemma_1_4 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%32 (|%4. ((%55 ((%47 (%111 ((%42 $2) $0))) ((%47 (%112 ((%41 $2) $1))) ((%85 (%68 (%107 $2))) (%58 $0))))) ((%86 ((%113 $2) $1)) $0))))))))"])
  val op scc_main_lemma_1_5 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%30 (|%21. ((%55 ((%85 (%68 (%107 $2))) $1)) ((%85 (%68 (%107 (%105 ((%41 $2) $0))))) $1))))))))"])
  val op scc_main_lemma_1_6 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. (%32 (|%4. (%32 (|%5. ((%55 ((%47 ((%52 (%103 ((%42 $3) $1))) ((%77 $2) $0))) (%116 ((%75 $2) $0)))) ((%53 (%115 ((%42 (%110 ((%41 $3) $2))) (%103 ((%42 (%110 ((%41 $3) $2))) $1))))) (%115 ((%42 $3) $0))))))))))))"])
  val op scc_main_lemma_1_7 =
    DT(["cheat"],
       [read"(%33 (|%1. (%30 (|%20. ((%55 ((%47 (%99 ((%41 $1) $0))) (%112 ((%41 $1) $0)))) ((%48 (%108 $1)) ((%36 (%108 (%110 ((%41 $1) $0)))) (%108 (%105 ((%41 $1) ((%91 $0) (%96 ((%41 $1) $0)))))))))))))"])
  val op scc_main_lemma_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%32 (|%12. ((%55 (%69 $0)) (%32 (|%4. (%33 (|%1. ((%55 ((%47 (%104 $0)) ((%47 (%111 ((%42 $0) $1))) ((%47 ((%85 (%68 (%107 $0))) (%58 $1))) ((%47 ((%47 (%116 ((%52 $1) %65))) (%116 ((%52 $1) ((%77 %64) %65))))) ((%47 (%69 $1)) ((%52 $2) (%103 ((%42 $0) $1))))))))) ((%48 (%108 $0)) (%115 ((%42 $0) (%103 ((%42 $0) $1)))))))))))))"])
  val op scc_main_lemma =
    DT(["DISK_THM", "cheat"],
       [read"(%32 (|%4. (%33 (|%1. ((%55 ((%47 (%104 $0)) ((%47 (%111 ((%42 $0) $1))) ((%47 ((%85 (%68 (%107 $0))) (%58 $1))) ((%47 (%116 ((%50 (%58 $1)) %64))) (%69 $1)))))) ((%48 (%108 $0)) (%115 ((%42 $0) (%103 ((%42 $0) $1))))))))))"])
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
   ("single_child_ancestors_def",single_child_ancestors_def,DB.Def),
   ("member_leaves_def",member_leaves_def,DB.Def),
   ("problem_wo_vs_ancestors_def",problem_wo_vs_ancestors_def,DB.Def),
   ("scc_main_lemma_x",scc_main_lemma_x,DB.Thm),
   ("scc_main_lemma_1_xx",scc_main_lemma_1_xx,DB.Thm),
   ("scc_lemma_1_1",scc_lemma_1_1,DB.Thm),
   ("scc_lemma_1_2",scc_lemma_1_2,DB.Thm),
   ("scc_lemma_1_3",scc_lemma_1_3,DB.Thm),
   ("scc_lemma_1_5",scc_lemma_1_5,DB.Thm),
   ("scc_lemma_1_4_1_1_1",scc_lemma_1_4_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_1_1_1",scc_lemma_1_4_1_1_2_1_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_1_1",scc_lemma_1_4_1_1_2_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_1",scc_lemma_1_4_1_1_2_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_2",scc_lemma_1_4_1_1_2_1_2,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_4",scc_lemma_1_4_1_1_2_1_4,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1",scc_lemma_1_4_1_1_2_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2_1_1_1",scc_lemma_1_4_1_1_2_2_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2_1_1",scc_lemma_1_4_1_1_2_2_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2_1",scc_lemma_1_4_1_1_2_2_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2",scc_lemma_1_4_1_1_2_2,DB.Thm),
   ("scc_lemma_1_4_1_1_2",scc_lemma_1_4_1_1_2,DB.Thm),
   ("scc_lemma_1_4_1_1",scc_lemma_1_4_1_1,DB.Thm),
   ("scc_lemma_1_4_1",scc_lemma_1_4_1,DB.Thm),
   ("scc_lemma_1_4_2",scc_lemma_1_4_2,DB.Thm),
   ("scc_lemma_1_4_3_1",scc_lemma_1_4_3_1,DB.Thm),
   ("scc_lemma_1_4_3_2",scc_lemma_1_4_3_2,DB.Thm),
   ("scc_lemma_1_4_3_3",scc_lemma_1_4_3_3,DB.Thm),
   ("scc_lemma_1_4_3_4_1",scc_lemma_1_4_3_4_1,DB.Thm),
   ("scc_lemma_1_4_3_4",scc_lemma_1_4_3_4,DB.Thm),
   ("scc_lemma_1_4_3_5",scc_lemma_1_4_3_5,DB.Thm),
   ("scc_lemma_1_4_3_6",scc_lemma_1_4_3_6,DB.Thm),
   ("scc_lemma_1_4_3",scc_lemma_1_4_3,DB.Thm),
   ("scc_lemma_1_4_4",scc_lemma_1_4_4,DB.Thm),
   ("scc_lemma_1_4",scc_lemma_1_4,DB.Thm),
   ("scc_main_lemma_1_1_1_1_1_1",scc_main_lemma_1_1_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_1_1",scc_main_lemma_1_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_1",scc_main_lemma_1_1_1_1,DB.Thm),
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
