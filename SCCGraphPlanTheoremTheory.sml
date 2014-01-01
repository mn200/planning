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
          Arbnum.fromString "1388583127",
          Arbnum.fromString "955848")
          [("SCC",
           Arbnum.fromString "1388583124",
           Arbnum.fromString "13352"),
           ("GraphPlanTheorem",
           Arbnum.fromString "1388583103",
           Arbnum.fromString "597030")];
  val _ = Theory.incorporate_types "SCCGraphPlanTheorem" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("num", "num"), ID("pair", "prod"),
   ID("min", "bool"), ID("FM_plan", "problem"), ID("finite_map", "fmap"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("prim_rec", "<"), ID("arithmetic", "<="),
   ID("min", "="), ID("min", "==>"), ID("bool", "?"), ID("min", "@"),
   ID("pred_set", "BIGUNION"), ID("arithmetic", "BIT1"),
   ID("pred_set", "CARD"), ID("bool", "COND"), ID("pred_set", "DELETE"),
   ID("pred_set", "DIFF"), ID("pred_set", "DISJOINT"),
   ID("finite_map", "DRESTRICT"), ID("pred_set", "EMPTY"),
   ID("finite_map", "FDOM"), ID("pred_set", "FINITE"), ID("pair", "FST"),
   ID("pred_set", "GSPEC"), ID("combin", "I"), ID("pred_set", "IMAGE"),
   ID("bool", "IN"), ID("pred_set", "INSERT"), ID("pred_set", "INTER"),
   ID("arithmetic", "NUMERAL"), ID("pred_set", "REL_RESTRICT"),
   ID("SCC", "SCC"), ID("pair", "SND"), ID("pred_set", "SUBSET"),
   ID("pred_set", "SUM_IMAGE"), ID("relation", "StrongOrder"),
   ID("relation", "TC"), ID("pred_set", "UNION"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("arithmetic", "ZERO"),
   ID("GraphPlanTheorem", "action_proj"),
   ID("SCCGraphPlanTheorem", "ancestors"),
   ID("SCCGraphPlanTheorem", "childless_problem_scc_set"),
   ID("SCCGraphPlanTheorem", "childless_svs"),
   ID("SCCGraphPlanTheorem", "childless_vs"),
   ID("GraphPlanTheorem", "dep"), ID("SCCGraphPlanTheorem", "dep_tc"),
   ID("GraphPlanTheorem", "dep_var_set"),
   ID("SCCGraphPlanTheorem", "member_leaves"), ID("pair", "pair_CASE"),
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
   TYOP [0, 8, 4], TYOP [0, 8, 1], TYOP [0, 6, 1], TYOP [0, 8, 5],
   TYOP [0, 5, 4], TYOP [0, 6, 4], TYOP [0, 2, 3], TYOP [0, 5, 15],
   TYOP [0, 8, 3], TYOP [0, 8, 10], TYOP [5, 2, 1], TYOP [2, 19, 19],
   TYV "'b", TYOP [5, 2, 21], TYOP [2, 5, 21], TYOP [0, 21, 1],
   TYOP [0, 24, 1], TYOP [0, 22, 1], TYOP [0, 26, 1], TYOP [0, 4, 1],
   TYOP [0, 15, 1], TYOP [0, 29, 1], TYOP [0, 28, 1], TYOP [0, 10, 1],
   TYOP [0, 32, 1], TYOP [0, 5, 1], TYOP [0, 34, 1], TYOP [0, 20, 1],
   TYOP [0, 36, 1], TYOP [0, 0, 0], TYOP [0, 0, 38], TYOP [2, 2, 2],
   TYOP [0, 2, 40], TYOP [0, 2, 41], TYOP [2, 2, 1], TYOP [0, 1, 43],
   TYOP [0, 2, 44], TYOP [2, 3, 1], TYOP [0, 1, 46], TYOP [0, 3, 47],
   TYOP [2, 3, 3], TYOP [0, 3, 49], TYOP [0, 3, 50], TYOP [0, 3, 8],
   TYOP [0, 5, 52], TYOP [0, 4, 6], TYOP [0, 5, 54], TYOP [2, 5, 40],
   TYOP [0, 40, 56], TYOP [0, 5, 57], TYOP [2, 5, 49], TYOP [0, 49, 59],
   TYOP [0, 5, 60], TYOP [2, 20, 3], TYOP [0, 3, 62], TYOP [0, 20, 63],
   TYOP [0, 1, 1], TYOP [0, 1, 65], TYOP [0, 0, 1], TYOP [0, 0, 67],
   TYOP [0, 3, 4], TYOP [0, 15, 29], TYOP [0, 4, 28], TYOP [0, 9, 1],
   TYOP [0, 9, 72], TYOP [0, 5, 34], TYOP [0, 18, 1], TYOP [0, 75, 18],
   TYOP [0, 4, 3], TYOP [0, 28, 4], TYOP [0, 3, 0], TYOP [0, 4, 4],
   TYOP [0, 4, 80], TYOP [0, 1, 81], TYOP [0, 4, 69], TYOP [0, 3, 3],
   TYOP [0, 3, 84], TYOP [0, 3, 22], TYOP [0, 22, 86], TYOP [0, 22, 3],
   TYOP [0, 19, 3], TYOP [0, 20, 19], TYOP [0, 23, 5], TYOP [0, 2, 43],
   TYOP [0, 92, 3], TYOP [0, 3, 46], TYOP [0, 94, 4], TYOP [0, 69, 71],
   TYOP [0, 2, 4], TYOP [0, 3, 28], TYOP [0, 20, 37], TYOP [0, 3, 80],
   TYOP [0, 3, 15], TYOP [0, 15, 101], TYOP [0, 69, 83], TYOP [0, 15, 4],
   TYOP [0, 4, 0], TYOP [0, 79, 105], TYOP [0, 69, 1], TYOP [0, 15, 15],
   TYOP [0, 69, 69], TYOP [0, 23, 1], TYOP [0, 23, 110], TYOP [0, 111, 1],
   TYOP [0, 9, 9], TYOP [0, 113, 9], TYOP [0, 18, 114], TYOP [0, 62, 20],
   TYOP [0, 56, 1], TYOP [0, 59, 1], TYOP [0, 5, 69], TYOP [0, 119, 4],
   TYOP [0, 8, 120], TYOP [0, 5, 36], TYOP [0, 5, 19], TYOP [0, 5, 0]]
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
  [TMV("P", 3), TMV("P", 10), TMV("PROB", 5), TMV("R", 15), TMV("R", 18),
   TMV("R'", 15), TMV("S", 4), TMV("S'", 4), TMV("a", 20), TMV("a", 8),
   TMV("f", 22), TMV("fdom", 3), TMV("min", 2), TMV("s", 3), TMV("s", 4),
   TMV("single_child_ancestors", 9), TMV("t", 3), TMV("v", 2), TMV("v", 5),
   TMV("v'", 2), TMV("v1", 2), TMV("v1", 3), TMV("v1'", 2), TMV("v2", 2),
   TMV("v2'", 2), TMV("vs", 3), TMV("vs'", 21), TMV("vs'", 3),
   TMV("vs''", 3), TMV("vs1", 3), TMV("vs2", 3), TMV("x", 2), TMV("x", 23),
   TMV("x'", 2), TMV("y", 2), TMV("y", 23), TMC(6, 4), TMC(6, 25),
   TMC(6, 27), TMC(6, 28), TMC(6, 30), TMC(6, 31), TMC(6, 33), TMC(6, 35),
   TMC(6, 37), TMC(7, 39), TMC(8, 42), TMC(8, 45), TMC(8, 48), TMC(8, 51),
   TMC(8, 53), TMC(8, 55), TMC(8, 58), TMC(8, 61), TMC(8, 64), TMC(9, 66),
   TMC(10, 68), TMC(11, 68), TMC(12, 66), TMC(12, 69), TMC(12, 70),
   TMC(12, 71), TMC(12, 73), TMC(12, 68), TMC(12, 74), TMC(13, 66),
   TMC(14, 4), TMC(14, 28), TMC(15, 76), TMC(16, 77), TMC(16, 78),
   TMC(17, 38), TMC(18, 79), TMC(19, 82), TMC(20, 83), TMC(21, 85),
   TMC(22, 69), TMC(23, 87), TMC(24, 3), TMC(24, 4), TMC(25, 88),
   TMC(25, 89), TMC(26, 4), TMC(26, 28), TMC(27, 90), TMC(27, 91),
   TMC(28, 93), TMC(28, 95), TMC(29, 80), TMC(30, 96), TMC(31, 97),
   TMC(31, 98), TMC(31, 99), TMC(32, 100), TMC(33, 85), TMC(33, 81),
   TMC(34, 38), TMC(35, 102), TMC(35, 103), TMC(36, 104), TMC(37, 90),
   TMC(38, 69), TMC(38, 71), TMC(39, 106), TMC(40, 107), TMC(41, 108),
   TMC(41, 109), TMC(42, 85), TMC(42, 81), TMC(43, 112), TMC(43, 75),
   TMC(44, 115), TMC(45, 0), TMC(46, 116), TMC(47, 17), TMC(48, 13),
   TMC(49, 11), TMC(50, 10), TMC(51, 117), TMC(52, 16), TMC(53, 118),
   TMC(54, 14), TMC(55, 121), TMC(56, 34), TMC(57, 12), TMC(58, 122),
   TMC(59, 123), TMC(60, 124), TMC(61, 13), TMC(62, 12), TMC(63, 11),
   TMC(64, 10), TMC(65, 9), TMC(66, 9), TMC(67, 7), TMC(68, 65)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op dep_tc_def =
    DT([],
       [read"(%43 (|%2. ((%60 (%119 $0)) (%105 (|%22. (|%24. (%118 ((%52 $2) ((%46 $1) $0)))))))))"])
  val op ancestors_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. ((%59 (%114 ((%50 $1) $0))) (%86 (|%17. ((%47 $0) ((%55 (%66 (|%19. ((%55 ((%90 $0) $2)) (((%119 $3) $1) $0))))) (%36 (|%19. ((%65 ((%90 $0) $2)) (%135 (((%119 $3) $0) $1))))))))))))))"])
  val op scc_vs_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. ((%58 (%131 ((%50 $1) $0))) ((%99 (|%22. (|%24. (%118 ((%52 $3) ((%46 $1) $0)))))) $0))))))"])
  val op scc_set_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. ((%58 (%130 ((%51 $1) $0))) (%39 (|%25. ((%65 ((%55 ((%91 $0) $1)) (%135 ((%76 $0) (%81 (%126 $2)))))) (%131 ((%50 $2) $0))))))))))"])
  val op sum_scc_parents_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. ((%63 (%134 ((%51 $1) $0))) ((%45 ((%103 (|%25. (%127 (%124 ((%50 $2) ((%107 $0) (%114 ((%50 $2) $0)))))))) $0)) (%96 (%71 %112))))))))"])
  val op childless_vs_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. ((%58 (%117 ((%50 $1) $0))) (%39 (|%27. (%135 (%120 ((%53 $2) ((%49 $1) $0)))))))))))"])
  val op childless_svs_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. ((%58 (%116 ((%51 $1) $0))) (%39 (|%25. ((%65 ((%91 $0) $1)) (%117 ((%50 $2) $0))))))))))"])
  val op problem_scc_set_def =
    DT([],
       [read"(%43 (|%2. ((%61 (%128 $0)) (%87 (|%25. ((%48 $0) (%131 ((%50 $1) $0))))))))"])
  val op childless_problem_scc_set_def =
    DT([],
       [read"(%43 (|%2. ((%61 (%115 $0)) (%87 (|%25. ((%48 $0) ((%55 (%131 ((%50 $1) $0))) (%117 ((%50 $1) $0)))))))))"])
  val op single_child_parents_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. ((%61 (%133 ((%50 $1) $0))) (%87 (|%27. ((%48 $0) ((%55 ((%101 $0) (%114 ((%50 $2) $1)))) ((%55 (%117 ((%50 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1)))) $0))) (%131 ((%50 $2) $0))))))))))))"])
  val op single_child_ancestors_primitive_def =
    DT([],
       [read"((%62 %132) ((%111 (%68 (|%4. ((%55 (%110 $0)) (%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 ((%55 ((%55 ((%101 $1) (%81 (%126 $2)))) (%135 ((%59 $1) %78)))) ((%91 $0) (%133 ((%50 $2) $1))))) (($3 ((%50 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1)))) $0)) ((%50 $2) $1))))))))))))) (|%15. (|%9. ((%122 $0) (|%2. (|%25. (%88 (((%73 ((%55 ((%101 $0) (%81 (%126 $1)))) (%135 ((%59 $0) %78)))) ((%108 (%133 ((%50 $1) $0))) (%70 ((%89 (|%27. ($4 ((%50 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1)))) $0)))) (%133 ((%50 $1) $0)))))) %79)))))))))"])
  val op member_leaves_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. ((%61 (%121 ((%51 $1) $0))) ((%95 (|%25. ((%55 (%131 ((%50 $2) $0))) (%117 ((%50 $2) $0))))) $0))))))"])
  val op problem_wo_vs_ancestors_def =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. ((%64 (%129 ((%50 $1) $0))) (%124 ((%50 $1) ((%75 (%81 (%126 $1))) ((%107 $0) (%69 (%132 ((%50 $1) $0))))))))))))"])
  val op single_child_ancestors_def_1 =
    DT(["cheat"],
       [read"(%109 (|%32. (|%35. ((%56 (%72 (%81 (%126 (%85 $1))))) (%72 (%81 (%126 (%85 $0))))))))"])
  val op single_child_ancestors_def_2_1 =
    DT(["DISK_THM"],
       [read"(%39 (|%13. (%39 (|%16. ((%65 ((%55 (%82 $1)) ((%55 (%82 $0)) ((%101 $1) $0)))) ((%59 ((%94 $0) ((%75 $0) $1))) ((%75 $0) $1)))))))"])
  val op single_child_ancestors_def_2 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%37 (|%26. ((%65 ((%55 ((%101 $1) (%81 (%126 $2)))) (%135 ((%59 $1) %78)))) ((%56 (%72 (%81 (%126 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1))))))) (%72 (%81 (%126 $2)))))))))))"])
  val op single_child_ancestors_ind =
    DT(["DISK_THM"],
       [read"(%42 (|%1. ((%65 (%43 (|%2. (%39 (|%25. ((%65 (%39 (|%27. ((%65 ((%55 ((%55 ((%101 $1) (%81 (%126 $2)))) (%135 ((%59 $1) %78)))) ((%91 $0) (%133 ((%50 $2) $1))))) ($3 ((%50 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1)))) $0)))))) ($2 ((%50 $1) $0)))))))) (%43 (|%18. (%39 (|%21. ($2 ((%50 $1) $0)))))))))"])
  val op single_child_ancestors_def =
    DT(["DISK_THM"],
       [read"(%39 (|%25. (%43 (|%2. ((%61 (%132 ((%50 $0) $1))) (((%73 ((%55 ((%101 $1) (%81 (%126 $0)))) (%135 ((%59 $1) %78)))) ((%108 (%133 ((%50 $0) $1))) (%70 ((%89 (|%27. (%132 ((%50 (%124 ((%50 $1) ((%75 (%81 (%126 $1))) $2)))) $0)))) (%133 ((%50 $0) $1)))))) %79))))))"])
  val op scc_main_lemma_x =
    DT(["DISK_THM"],
       [read"(%39 (|%13. (%39 (|%16. (%36 (|%31. ((%65 ((%55 ((%90 $0) $2)) (%135 ((%90 $0) $1)))) (%135 ((%59 $2) $1)))))))))"])
  val op scc_main_lemma_1_xx =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 ((%55 (%131 ((%50 $2) $1))) ((%55 (%131 ((%50 $2) $0))) (%135 ((%59 $1) $0))))) ((%76 $1) $0))))))))"])
  val op scc_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. ((%65 (%83 $0)) (%83 (%121 ((%51 $1) $0))))))))"])
  val op scc_lemma_1_2 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%41 (|%6. ((%65 ((%91 $1) (%121 ((%51 $2) $0)))) (%131 ((%50 $2) $1)))))))))"])
  val op scc_lemma_1_3 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%41 (|%6. ((%65 ((%91 $1) (%121 ((%51 $2) $0)))) ((%91 $1) $0))))))))"])
  val op scc_lemma_1_5 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%41 (|%6. ((%65 ((%91 $1) (%121 ((%51 $2) $0)))) (%117 ((%50 $2) $1)))))))))"])
  val op scc_lemma_1_4_1_1_1 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 (%117 ((%50 $2) $0))) ((%76 $0) (%69 (%132 ((%50 $2) $1)))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%39 (|%11. (%39 (|%25. (%36 (|%17. (%38 (|%10. ((%65 ((%55 (%135 ((%90 $1) $2))) ((%55 ((%101 (%80 $0)) $3)) ((%90 $1) (%80 $0))))) ((%90 $1) (%80 ((%77 $0) ((%75 $3) $2)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%36 (|%17. (%44 (|%8. ((%65 ((%55 (%135 ((%90 $1) $2))) ((%55 ((%92 $0) (%125 $3))) (%123 $3)))) ((%55 ((%65 ((%90 $1) (%81 (%84 $0)))) ((%90 $1) (%81 (%84 (%113 ((%54 $0) ((%75 (%81 (%126 $3))) $2)))))))) ((%65 ((%90 $1) (%81 (%100 $0)))) ((%90 $1) (%81 (%100 (%113 ((%54 $0) ((%75 (%81 (%126 $3))) $2)))))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. (%36 (|%17. (%36 (|%19. ((%65 ((%55 (%123 $4)) ((%55 ((%90 $1) $2)) ((%55 ((%90 $0) $2)) ((%76 $3) $2))))) ((%65 (%118 ((%52 $4) ((%46 $1) $0)))) (%118 ((%52 (%124 ((%50 $4) ((%75 (%81 (%126 $4))) $3)))) ((%46 $1) $0)))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_2 =
    DT(["DISK_THM"],
       [read"(%40 (|%3. (%40 (|%5. (%39 (|%0. ((%65 (%36 (|%31. (%36 (|%34. ((%65 ((%55 ($2 $1)) ($2 $0))) ((%55 ((%65 (($4 $1) $0)) (($3 $1) $0))) (((%105 (|%31. (|%34. ((%55 (($6 $1) $0)) ((%55 ($4 $1)) ($4 $0)))))) $1) $0)))))))) (%36 (|%31. (%36 (|%34. ((%65 ((%55 ($2 $1)) ($2 $0))) (((%105 $3) $1) $0)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_4 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%36 (|%17. (%36 (|%19. ((%65 (%118 ((%52 (%124 ((%50 $3) ((%75 (%81 (%126 $3))) $2)))) ((%46 $1) $0)))) (%118 ((%52 $3) ((%46 $1) $0))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 ((%55 (%123 $2)) ((%55 (%131 ((%50 $2) $0))) ((%76 $1) $0)))) (%131 ((%50 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1)))) $0)))))))))"])
  val op scc_lemma_1_4_1_1_2_2 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 ((%55 (%117 ((%50 $2) $0))) ((%76 $1) $0))) (%117 ((%50 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) $1)))) $0)))))))))"])
  val op scc_lemma_1_4_1_1_2 =
    DT(["tactic_failed"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. (%41 (|%6. ((%65 ((%55 ((%76 $2) $1)) ((%91 $1) (%121 ((%51 $3) $0))))) ((%91 $1) (%121 ((%51 (%124 ((%50 $3) ((%75 (%81 (%126 $3))) $2)))) $0))))))))))))"])
  val op scc_lemma_1_4_1_1 =
    DT(["DISK_THM", "cheat", "tactic_failed"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. (%41 (|%6. ((%65 ((%55 (%131 ((%50 $3) $2))) ((%55 (%135 ((%59 $2) $1))) ((%91 $1) (%121 ((%51 $3) $0)))))) ((%91 $1) (%121 ((%51 (%129 ((%50 $3) $2))) $0))))))))))))"])
  val op scc_lemma_1_4_1 =
    DT(["DISK_THM", "cheat", "tactic_failed"],
       [read"(%43 (|%2. (%41 (|%6. (%39 (|%25. ((%65 (%131 ((%50 $2) $0))) ((%102 ((%74 (%121 ((%51 $2) $1))) $0)) (%121 ((%51 (%129 ((%50 $2) $0))) $1))))))))))"])
  val op scc_lemma_1_4_2 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%28. (%41 (|%6. (%39 (|%27. ((%65 ((%55 (%135 ((%91 $0) (%132 ((%50 $4) $3))))) ((%55 (%135 ((%91 $0) ((%74 (%121 ((%51 $4) $1))) $2)))) ((%101 $2) $3)))) (%135 ((%91 $0) (%121 ((%51 (%124 ((%50 $4) ((%75 (%81 (%126 $4))) $3)))) $1)))))))))))))))"])
  val op scc_lemma_1_4_3 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. ((%61 (%132 ((%50 $1) ((%107 $0) (%69 (%132 ((%50 $1) $0))))))) %79)))))"])
  val op scc_lemma_1_4_4 =
    DT(["DISK_THM"],
       [read"(%39 (|%13. (%39 (|%16. ((%65 (%36 (|%31. ((%65 (%135 ((%90 $0) $2))) (%135 ((%90 $0) $1)))))) ((%59 ((%75 $0) $1)) %78))))))"])
  val op scc_lemma_1_4 =
    DT(["DISK_THM", "cheat", "tactic_failed"],
       [read"(%41 (|%6. ((%65 (%83 $0)) (%43 (|%2. (%39 (|%25. (%41 (|%7. ((%65 ((%55 (%131 ((%50 $2) $1))) ((%55 (%135 ((%91 $1) $0))) ((%61 (%121 ((%51 $2) $3))) ((%93 $1) $0))))) ((%61 (%121 ((%51 (%129 ((%50 $2) $1))) $3))) $0)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%36 (|%20. (%36 (|%23. ((%65 ((%55 (%123 $2)) (%118 ((%52 $2) ((%46 $1) $0))))) ((%55 ((%90 $1) (%81 (%126 $2)))) ((%90 $0) (%81 (%126 $2)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%36 (|%20. (%36 (|%23. ((%65 ((%55 (%123 $2)) (((%119 $2) $1) $0))) ((%90 $1) (%81 (%126 $2))))))))))"])
  val op scc_main_lemma_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. ((%65 ((%55 (%123 $1)) (%131 ((%50 $1) $0)))) ((%101 $0) (%81 (%126 $1))))))))"])
  val op scc_main_lemma_1_1_1_2 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 ((%55 (%135 ((%76 $1) $0))) ((%55 (%131 ((%50 $2) $1))) (%131 ((%50 $2) $0))))) ((%59 $1) $0))))))))"])
  val op scc_main_lemma_1_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. (%39 (|%25. ((%65 ((%55 (%123 $2)) ((%55 ((%101 (%81 (%126 $2))) (%69 $1))) ((%55 (%130 ((%51 $2) $1))) (%131 ((%50 $2) $0)))))) ((%91 $0) $1))))))))"])
  val op scc_main_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. (%41 (|%6. ((%65 ((%55 (%123 $1)) ((%55 ((%101 (%81 (%126 $1))) (%69 $0))) (%130 ((%51 $1) $0))))) ((%61 (%115 $1)) (%121 ((%51 $1) $0))))))))"])
  val op scc_main_lemma_1_2_1 =
    DT(["DISK_THM"],
       [read"(%43 (|%2. ((%65 (%123 $0)) ((%65 ((%59 (%81 (%126 $0))) %78)) (%39 (|%25. (%135 (%131 ((%50 $1) $0)))))))))"])
  val op scc_main_lemma_1_2_2_1 =
    DT(["cheat"],
       [read"(%43 (|%2. (%104 ((%98 (%106 (|%29. (|%30. (%120 ((%53 $2) ((%49 $0) $1))))))) (%128 $0)))))"])
  val op scc_main_lemma_1_2_2_2 =
    DT(["cheat"], [read"(%43 (|%2. (%83 (%128 $0))))"])
  val op scc_main_lemma_1_2_2_3 =
    DT(["cheat"],
       [read"(%43 (|%2. ((%65 ((%55 (%135 ((%59 (%81 (%126 $0))) %78))) (%123 $0))) (%67 (|%25. (%131 ((%50 $1) $0)))))))"])
  val op scc_main_lemma_1_2_2_4 =
    DT(["cheat"],
       [read"(%40 (|%3. (%39 (|%13. (%36 (|%12. ((%65 (%36 (|%31. ((%65 ((((%97 (%105 $3)) $2) $0) $1)) (%135 ((%90 $0) $2)))))) (%36 (|%33. ((%65 ((%90 $0) $2)) (%135 (($3 $0) $1))))))))))))"])
  val op scc_main_lemma_1_2_2 =
    DT(["cheat"],
       [read"(%43 (|%2. ((%65 ((%55 (%123 $0)) (%135 ((%59 (%81 (%126 $0))) %78)))) (%67 (|%25. ((%55 (%131 ((%50 $1) $0))) (%117 ((%50 $1) $0))))))))"])
  val op scc_main_lemma_1_2 =
    DT(["DISK_THM", "cheat"],
       [read"(%43 (|%2. ((%65 (%123 $0)) ((%58 ((%59 (%81 (%126 $0))) %78)) ((%61 (%115 $0)) %79)))))"])
  val op scc_main_lemma_1_3 =
    DT(["cheat"],
       [read"(%43 (|%2. (%41 (|%6. (%41 (|%7. ((%65 ((%55 (%130 ((%51 $2) $1))) ((%102 $0) $1))) (%130 ((%51 (%124 ((%50 $2) ((%75 (%81 (%126 $2))) (%69 $0))))) $1)))))))))"])
  val op scc_main_lemma_1_4 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%41 (|%6. ((%65 ((%55 (%130 ((%51 $2) $0))) ((%55 (%131 ((%50 $2) $1))) ((%101 (%81 (%126 $2))) (%69 $0))))) ((%102 (%132 ((%50 $2) $1))) $0))))))))"])
  val op scc_main_lemma_1_5 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%39 (|%27. ((%65 ((%101 (%81 (%126 $2))) $1)) ((%101 (%81 (%126 (%124 ((%50 $2) $0))))) $1))))))))"])
  val op scc_main_lemma_1_6 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. (%41 (|%6. (%41 (|%7. ((%65 ((%55 ((%61 (%121 ((%51 $3) $1))) ((%93 $2) $0))) (%135 ((%91 $2) $0)))) ((%63 (%134 ((%51 (%129 ((%50 $3) $2))) (%121 ((%51 (%129 ((%50 $3) $2))) $1))))) (%134 ((%51 $3) $0))))))))))))"])
  val op scc_main_lemma_1_7 =
    DT(["cheat"],
       [read"(%43 (|%2. (%39 (|%25. ((%65 ((%55 (%117 ((%50 $1) $0))) (%131 ((%50 $1) $0)))) ((%57 (%127 $1)) ((%45 (%127 (%129 ((%50 $1) $0)))) (%127 (%124 ((%50 $1) ((%107 $0) (%114 ((%50 $1) $0)))))))))))))"])
  val op scc_main_lemma_1 =
    DT(["DISK_THM", "cheat", "tactic_failed"],
       [read"(%41 (|%14. ((%65 (%83 $0)) (%41 (|%6. (%43 (|%2. ((%65 ((%55 (%123 $0)) ((%55 (%130 ((%51 $0) $1))) ((%55 ((%101 (%81 (%126 $0))) (%69 $1))) ((%55 ((%55 (%135 ((%61 $1) %79))) (%135 ((%61 $1) ((%93 %78) %79))))) ((%55 (%83 $1)) ((%61 $2) (%121 ((%51 $0) $1))))))))) ((%57 (%127 $0)) (%134 ((%51 $0) (%121 ((%51 $0) $1)))))))))))))"])
  val op scc_main_lemma =
    DT(["DISK_THM", "cheat", "tactic_failed"],
       [read"(%41 (|%6. (%43 (|%2. ((%65 ((%55 (%123 $0)) ((%55 (%130 ((%51 $0) $1))) ((%55 ((%101 (%81 (%126 $0))) (%69 $1))) ((%55 (%135 ((%59 (%69 $1)) %78))) (%83 $1)))))) ((%57 (%127 $0)) (%134 ((%51 $0) (%121 ((%51 $0) $1))))))))))"])
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
   ("scc_lemma_1_4_1_1_2_2",scc_lemma_1_4_1_1_2_2,DB.Thm),
   ("scc_lemma_1_4_1_1_2",scc_lemma_1_4_1_1_2,DB.Thm),
   ("scc_lemma_1_4_1_1",scc_lemma_1_4_1_1,DB.Thm),
   ("scc_lemma_1_4_1",scc_lemma_1_4_1,DB.Thm),
   ("scc_lemma_1_4_2",scc_lemma_1_4_2,DB.Thm),
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
