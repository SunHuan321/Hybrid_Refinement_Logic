theory Sync_Refine
  imports Par_Refine
begin

subsection \<open>fix length ode\<close>

definition exp_independ :: "exp \<Rightarrow> var \<Rightarrow> bool" where
  "exp_independ e x = (\<forall>s1 s2 v. e s1 = e s2 \<longrightarrow> e s1 = e (s2(x:= v)))"

lemma ODEsol_time:
  assumes "ODEsol (ODE f) p d"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
  shows "ODEsol (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>t. (p t)(T := t)) d"
proof-
  let ?p = "\<lambda>x. state2vec (p x)" and ?q = "\<lambda>x. state2vec (\<lambda>a. f a (p x))"
  and ?p' = "\<lambda>t. state2vec ((p t)(T := t))" and 
      ?q' = "\<lambda>t. state2vec (\<lambda>a. (f(T := \<lambda>_. 1)) a ((p t)(T := t)))"
  from assms obtain \<epsilon> where a0: "0 \<le> d" "\<epsilon> > 0" "(?p has_vderiv_on ?q) {- \<epsilon>..d + \<epsilon>}"
    using ODEsol_def by auto
  then have a1 : "\<forall>i. ((\<lambda>t. ?p t $ i) has_vderiv_on (\<lambda>t. ?q t $ i)) {- \<epsilon>..d + \<epsilon>}"
    using has_vderiv_on_proj[of ?p ?q "{- \<epsilon>..d + \<epsilon>}"] by auto
  have "\<forall>i. ((\<lambda>t. ?p' t $ i) has_vderiv_on (\<lambda>t. ?q' t $ i)) {- \<epsilon>..d + \<epsilon>}"
  proof-
    {
      fix i
      assume b0: "((\<lambda>t. ?p t $ i) has_vderiv_on (\<lambda>t. ?q t $ i)) {- \<epsilon>..d + \<epsilon>}"
      have "((\<lambda>t. ?p' t $ i) has_vderiv_on (\<lambda>t. ?q' t $ i)) {- \<epsilon>..d + \<epsilon>}"
      proof (case_tac "i = T")
        assume "i = T"
        then show ?thesis
          by (smt (verit, ccfv_SIG) fun_upd_same has_vderiv_on_cong has_vderiv_on_id vec2state_def vec_state_map1)
      next
        assume "i \<noteq> T"
        then have "\<forall>t. ?p' t $ i = ?p t $ i" and "\<forall>t. ?q' t $ i = ?q t $ i"
           using \<open>i \<noteq> T\<close> assms(2) apply (simp add: state2vec_def) 
           using \<open>i \<noteq> T\<close> assms(2) exp_independ_def state2vec_def by force
         then show ?thesis
           using b0  by presburger
       qed
     }
     with a1 show ?thesis by auto
   qed
   then show ?thesis
     unfolding ODEsol_def ODE2Vec.simps using a0(1) a0(2) has_vderiv_on_projI[of ?p' ?q' "{- \<epsilon>..d + \<epsilon>}"]
     by auto
 qed

lemma bigstep_fixed_length_ode:
  assumes "Period > 0"
      and "ODEsol (ODE f) p Period"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
      and "tr = [WaitBlk Period (\<lambda>\<tau>. State ((p \<tau>)(T := \<tau>))) ({}, {})]" 
      and "s0 = (p(0))(T := 0)"
      and "s1 = (p(Period))(T := Period)"
    shows "big_step (Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period)) s0 tr s1"
proof-
  from assms(1) assms(2) assms(3) have "ODEsol (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>t. (p t)(T := t)) Period"
    using ODEsol_time by blast
  then show ?thesis
    using ContB2[of "Period" "(ODE (f(T := (\<lambda>_. 1))))" "(\<lambda>t. (p t)(T := t))" "\<lambda>s. s T < Period" s0]
    by (simp add: assms(1) assms(4) assms(5) assms(6))
qed

subsection \<open>sync behvior\<close>

lemma big_step_wait_seq:
  assumes "e s > 0"
      and "big_step (Wait e; C) s tr s'"
    shows "\<exists>tr'. big_step C s tr' s' \<and> tr = WaitBlk (e s) (\<lambda>_. State s) ({}, {}) # tr'"
proof-
  from assms(1) obtain sm tr1 tr2 where "big_step (Wait e) s tr1 sm" "big_step C sm tr2 s'"
  "tr = tr1 @ tr2"
    by (meson assms(2) seqE)
  with assms(1) show ?thesis
    using waitE by fastforce
qed

lemma sync_out_in:
  assumes "ch \<in> chs"
      and "big_step (Cm (ch[!]e)) s1 tr1 s1'"
      and "big_step (Cm (ch[?]var)) s2 tr2 s2'"
      and "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
    shows "s1 = s1' \<and> s2' = s2(var := e s1) \<and> tr1 = [OutBlock ch (e s1)] \<and>
    tr2 = [InBlock ch (e s1)] \<and>
    (\<exists>tr'. combine_blocks chs tr1' tr2' tr' \<and> tr = IOBlock ch (e s1) # tr')" 
proof-
  from assms(2) have a1: "tr1 = [OutBlock ch (e s1)] \<or> (\<exists>d. d >0 \<and> 
  tr1 = [WaitBlk d (\<lambda>_. State s1) ({ch}, {}), OutBlock ch (e s1)])" "s1 = s1'"
    by (metis sendE)+
  from assms(3) have a2: "\<exists>v. (tr2 = [InBlock ch v] \<and> s2' = s2(var := v)) \<or> (\<exists>d v. d >0 \<and> 
  tr2 = [WaitBlk d (\<lambda>_. State s2) ({}, {ch}), InBlock ch v] \<and> s2' = s2(var := v))"
    by (metis receiveE)
  show ?thesis
  proof(cases "tr1 = [OutBlock ch (e s1)]")
    assume "tr1 = [OutBlock ch (e s1)]"
    with a1(2) a2 assms(1,4) show ?thesis
      by (metis append_Cons append_Nil combine_blocks_pairE combine_blocks_pairE2)      
  next
    assume "\<not> tr1 = [OutBlock ch (e s1)]"
    with a1 obtain d where b0: "d > 0" "tr1 = [WaitBlk d (\<lambda>_. State s1) ({ch}, {}), OutBlock ch (e s1)]"
      by blast
    then show ?thesis
    proof(cases "\<exists>v. tr2 = [InBlock ch v]")
      assume "\<exists>v. tr2 = [InBlock ch v]"
      then obtain v where "tr2 = [InBlock ch v]"
        by blast
      with assms(1,4) b0 show ?thesis
        using combine_blocks_pairE2' by (metis append_Cons)
    next
      assume "\<not> (\<exists>v. tr2 = [InBlock ch v])"
      with a2 obtain d' v where "d' > 0" "tr2 = [WaitBlk d' (\<lambda>_. State s2) ({}, {ch}), InBlock ch v]"
        by fastforce
      with assms(1,4) b0 show ?thesis
        using combine_blocks_waitE1[of chs d "(\<lambda>_. State s1)" "({ch}, {})" "[OutBlock ch (e s1)] @ tr1'"
        d' "(\<lambda>_. State s2)" "({}, {ch})" "[InBlock ch v] @ tr2'" tr]
        by auto
    qed
  qed
qed

lemma sync_in_out:
  assumes "ch \<in> chs"
      and "big_step (Cm (ch[?]var)) s1 tr1 s1'"
      and "big_step (Cm (ch[!]e)) s2 tr2 s2'"
      and "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
    shows "s2 = s2' \<and> s1' = s1(var := e s2) \<and> tr1 = [InBlock ch (e s2)] \<and>
    tr2 = [OutBlock ch (e s2)] \<and>
    (\<exists>tr'. combine_blocks chs tr1' tr2' tr' \<and> tr = IOBlock ch (e s2) # tr')" 
proof-
  from assms(2) have a1: "\<exists>v. (tr1 = [InBlock ch v] \<and> s1' = s1(var := v)) \<or> (\<exists>d v. d >0 \<and> 
  tr1 = [WaitBlk d (\<lambda>_. State s1) ({}, {ch}), InBlock ch v] \<and> s1' = s1(var := v))"
    by (metis receiveE)+
  from assms(3) have a2: "tr2 = [OutBlock ch (e s2)] \<or> (\<exists>d. d >0 \<and> 
  tr2 = [WaitBlk d (\<lambda>_. State s2) ({ch}, {}), OutBlock ch (e s2)])" "s2 = s2'"
    by (metis sendE)+
  show ?thesis
  proof(cases "tr2 = [OutBlock ch (e s2)]")
    assume "tr2 = [OutBlock ch (e s2)]"
    with a2(2) a1 assms(1,4) show ?thesis
      by (smt (verit, ccfv_threshold) append_Cons append_Nil combine_blocks_pairE combine_blocks_pairE2')      
  next
    assume "\<not> tr2 = [OutBlock ch (e s2)]"
    with a2 obtain d where b0: "d > 0" "tr2 = [WaitBlk d (\<lambda>_. State s2) ({ch}, {}), OutBlock ch (e s2)]"
      by blast
    then show ?thesis
    proof(cases "\<exists>v. tr1 = [InBlock ch v]")
      assume "\<exists>v. tr1 = [InBlock ch v]"
      then obtain v where "tr1 = [InBlock ch v]"
        by blast
      with assms(1,4) b0 show ?thesis
        by (metis append_Cons combine_blocks_pairE2)        
    next
      assume "\<not> (\<exists>v. tr1 = [InBlock ch v])"
      with a1 obtain d' v where "d' > 0" "tr1 = [WaitBlk d' (\<lambda>_. State s1) ({}, {ch}), InBlock ch v]"
        by fastforce
      with assms(1,4) b0 show ?thesis
        using combine_blocks_waitE1[of chs d' "\<lambda>_. State s1" "({}, {ch})" "InBlock ch v # tr1'"
        d "\<lambda>_. State s2" "({ch}, {})" "OutBlock ch (e s2) # tr2'" tr]
        by auto
    qed
  qed
qed

lemma sync_intout:
  assumes "Period > 0"
      and "ch \<in> chs"
      and "big_step (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) s1 tr1 s1'"
      and "big_step (Wait (\<lambda> s. Period); Cm (ch[?]var); C2) s2 tr2 s2'"
      and "combine_blocks chs tr1 tr2 tr"
    shows "\<exists>p tr1' tr2' tr'. ODEsol ode p Period \<and> p 0 = s1 \<and> big_step C1 (p Period) tr1' s1' \<and>
    big_step C2 (s2(var := e (p Period))) tr2' s2' \<and> combine_blocks chs tr1' tr2' tr' \<and>
    tr = (WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s2)) ({ch}, {})) # IOBlock ch (e (p Period)) # tr'"
proof-
  from assms(4) obtain s2m tr2m tr2m' where a0: "big_step (Cm (ch[?]var)) s2 tr2m s2m" 
  "big_step C2 s2m tr2m' s2'" "tr2 = WaitBlk Period (\<lambda>_. State s2) ({}, {}) # tr2m @ tr2m'"
    by (metis (no_types, lifting) assms(1) big_step_wait_seq seqE)
  from assms(3) show ?thesis
  proof(cases rule: interruptE, simp)
    fix d p i cha ea p2 tr2
    assume b0: "tr1 = OutBlock cha (ea s1) # tr2"
       and b1: "i < length [(ch[!]e, C1)]"
       and b2: "[(ch[!]e, C1)] ! i = (cha[!]ea, p2)"
    then have "i = 0" by simp
    with b1 b2 have b3: "cha = ch" "ea = e" "p2 = C1"
      by auto
    with assms(2,5) b0 a0(3) show ?thesis
      using combine_blocks_pairE2[of chs Out ch "e s1" tr2 Period "(\<lambda>_. State s2)" "({}, {})" 
      "tr2m @ tr2m'" tr] by auto
  next
    fix d p i cha ea p2 tr1'
    assume c0: "tr1 = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice [(ch[!]e, C1)]) # OutBlock cha (ea (p d)) # tr1'"
       and c1: "0 < d" "ODEsol ode p d" " p 0 = s1"
       and c2: "i < length [(ch[!]e, C1)]"
       and c3: "[(ch[!]e, C1)] ! i = (cha[!]ea, p2)"
       and c4: " big_step p2 (p d) tr1' s1'"
    then have "i = 0" by simp
    with c3 c4 have c5: "cha = ch" "ea = e" "p2 = C1" 
      by auto
    from a0(1) show ?thesis
    proof(cases rule: receiveE, simp)
      fix v
      assume c00: "tr2m = [InBlock ch v]"
         and c01: "s2m = s2(var := v)"
      with assms(2,5) a0(3) c0 c5 obtain tr' where "e (p d) = v" "d = Period" 
      "combine_blocks chs tr1' tr2m' tr'"
      "tr = WaitBlk d (\<lambda>t. ParState (State (p t)) (State s2)) (merge_rdy ({ch}, {}) ({}, {})) # IOBlock ch (e (p d)) # tr'"      
        using combine_blocks_waitE5[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" Out ch "e (p d)" tr1'
        Period "\<lambda>_. State s2" "({}, {})" In ch v tr2m' tr] by auto
      with c1(2,3) c4 a0(2) c01 c5(3) show ?thesis
        by (rule_tac x = p in exI, rule_tac x = tr1' in exI, rule_tac x = tr2m' in exI, rule_tac x = tr' in exI, simp)
    next
      fix d1 v
      assume c10: "tr2m = [WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}), InBlock ch v]"
         and c11: "s2m = s2(var := v)"
         and c12: "0 < d1"
      then show ?thesis
      proof(cases "Period > d")
        assume "Period > d"
        with assms(5) a0(3) c0 c1(1) c5 c10 obtain tr' where 
        "combine_blocks chs (OutBlock ch (e (p d)) # tr1') (WaitBlk (Period - d) (\<lambda>t. State s2) ({}, {}) 
         # WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m') tr'"
        using combine_blocks_waitE3[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" "OutBlock ch (e (p d)) # tr1'"
          Period "\<lambda>_. State s2" "({}, {})" "WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m'" tr]
          by auto
        with assms(2) show ?thesis
          by (meson combine_blocks_pairE2)
      next
        assume "\<not> Period > d"
        then show ?thesis
        proof(cases "Period = d")
          assume "Period = d"
          with assms(5) a0(3) c0 c1(1) c5 c10 obtain tr' where 
          "combine_blocks chs (OutBlock ch (e (p d)) # tr1') (WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m') tr'"
            using combine_blocks_waitE2[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" "OutBlock ch (e (p d)) # tr1'"
            "\<lambda>_. State s2" "({}, {})" "WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m'" tr]
            by auto
          with assms(2) show ?thesis
            by (meson combine_blocks_pairE2)
        next
          assume "\<not> Period = d"
          then have "Period < d"
            using \<open>\<not> d < Period\<close> by force
          with assms(1,5) a0(3) c0 c1(1) c5 c10 obtain tr' where 
          "combine_blocks chs (WaitBlk (d - Period) (\<lambda>t. State (p (t + Period))) ({ch}, {}) # OutBlock ch (e (p d)) # tr1')
           (WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m') tr'"
            using combine_blocks_waitE4[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" "OutBlock ch (e (p d)) # tr1'"
          Period "\<lambda>_. State s2" "({}, {})" "WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m'" tr]
            by auto
          then show ?thesis 
            using combine_blocks_waitE1[of chs "d - Period" "\<lambda>t. State (p (t + Period))" "({ch}, {})"
            "OutBlock ch (e (p d)) # tr1'" d1 "\<lambda>_. State s2" "({}, {ch})" "InBlock ch v # tr2m'" tr']
            by auto
        qed
      qed
    qed
  next
    fix i cha vara p2 v tr2
    assume "i < length [(ch[!]e, C1)]" "[(ch[!]e, C1)] ! i = (cha[?]vara, p2)"
    then show ?thesis by simp
  next
    fix d p i cha vara p2 v tr2
    assume "i < length [(ch[!]e, C1)]" "[(ch[!]e, C1)] ! i = (cha[?]vara, p2)"
    then show ?thesis by simp
  next
    assume "\<not> True"
    then show ?thesis by simp
  next
    fix d p
    assume "\<not> True"
    then show ?thesis by simp
  qed
qed

subsection \<open>Big step of sync program\<close>

lemma par_bigstep_2single:
  assumes "par_big_step (Parallel (Single C1) chs (Single C2)) s tr s'"
  shows "\<exists>s1 s2 s1' s2' tr1 tr2. big_step C1 s1 tr1 s1' \<and> big_step C2 s2 tr2 s2'
  \<and> s = ParState (State s1) (State s2) \<and> s' = ParState (State s1') (State s2') \<and>
  combine_blocks chs tr1 tr2 tr"
  by (smt (verit, best) ParallelE SingleE assms)

corollary par_bigstep_2skip:
  assumes "par_big_step (Parallel (Single Skip) chs (Single Skip)) s tr s'"
  shows "s = s' \<and> tr = []"
  by (smt (verit, best) assms combine_blocks_emptyE1 par_bigstep_2single skipE)

lemma bigstep_sim_Id_2single:
  assumes "(P\<^sub>1, s\<^sub>1) \<sqsubseteq> Id (P\<^sub>1', s\<^sub>1)"
      and "(P\<^sub>2, s\<^sub>2) \<sqsubseteq> Id (P\<^sub>2', s\<^sub>2)"
      and "par_big_step (Parallel (Single P\<^sub>1) chs (Single P\<^sub>2)) (ParState (State s\<^sub>1) (State s\<^sub>2)) tr s'"
    shows "par_big_step (Parallel (Single P\<^sub>1') chs (Single P\<^sub>2')) (ParState (State s\<^sub>1) (State s\<^sub>2)) tr s'"
proof-
  from assms(3) obtain s\<^sub>1' s\<^sub>2' tr\<^sub>1 tr\<^sub>2 where a0: "big_step P\<^sub>1 s\<^sub>1 tr\<^sub>1 s\<^sub>1'" "big_step P\<^sub>2 s\<^sub>2 tr\<^sub>2 s\<^sub>2'"
  "s' = ParState (State s\<^sub>1') (State s\<^sub>2')" "combine_blocks chs tr\<^sub>1 tr\<^sub>2 tr"
    using par_bigstep_2single by fastforce
  with assms(1,2) have "big_step P\<^sub>1' s\<^sub>1 tr\<^sub>1 s\<^sub>1'" "big_step P\<^sub>2' s\<^sub>2 tr\<^sub>2 s\<^sub>2'"
    by (simp add: hybrid_sim_single_Id)+
  with a0(3,4) show ?thesis
    using ParallelB SingleB by blast
qed

lemma bigstep_equiv_Id_2single:
  assumes "(P\<^sub>1, s\<^sub>1) \<sim> Id (P\<^sub>1', s\<^sub>1)"
      and "(P\<^sub>2, s\<^sub>2) \<sim> Id (P\<^sub>2', s\<^sub>2)"
    shows "par_big_step (Parallel (Single P\<^sub>1) chs (Single P\<^sub>2)) (ParState (State s\<^sub>1) (State s\<^sub>2)) tr s'
    \<longleftrightarrow> par_big_step (Parallel (Single P\<^sub>1') chs (Single P\<^sub>2')) (ParState (State s\<^sub>1) (State s\<^sub>2)) tr s'"
  using assms(1,2) bigstep_sim_Id_2single hybrid_equiv_single_def by blast

lemma par_bigstep_in_out:
  assumes "ch \<in> chs"
      and "par_big_step (Parallel (Single (Cm (ch[?]var); C1)) chs (Single (Cm (ch[!]e); C2))) 
           (ParState (State s\<^sub>p) (State s\<^sub>c)) tr s'"
    shows "\<exists>tr'. par_big_step (Parallel (Single C1) chs (Single C2)) (ParState (State (s\<^sub>p (var := e s\<^sub>c))) (State s\<^sub>c)) tr' s'
           \<and> tr = IOBlock ch (e s\<^sub>c) # tr'"
proof-
  from assms(2) obtain s\<^sub>p' tr\<^sub>p s\<^sub>c' tr\<^sub>c where a0: "big_step (Cm (ch[?]var); C1) s\<^sub>p tr\<^sub>p s\<^sub>p'"
  "big_step (Cm (ch[!]e); C2) s\<^sub>c tr\<^sub>c s\<^sub>c'" "s' = ParState (State s\<^sub>p') (State s\<^sub>c')"
  "combine_blocks chs tr\<^sub>p tr\<^sub>c tr"
    using par_bigstep_2single by fastforce
  then obtain s\<^sub>p\<^sub>m tr\<^sub>p\<^sub>m\<^sub>1 tr\<^sub>p\<^sub>m\<^sub>2 s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>m\<^sub>1 tr\<^sub>c\<^sub>m\<^sub>2 where a1: "big_step (Cm (ch[?]var)) s\<^sub>p tr\<^sub>p\<^sub>m\<^sub>1 s\<^sub>p\<^sub>m"
  "big_step C1 s\<^sub>p\<^sub>m tr\<^sub>p\<^sub>m\<^sub>2 s\<^sub>p'" "tr\<^sub>p = tr\<^sub>p\<^sub>m\<^sub>1 @ tr\<^sub>p\<^sub>m\<^sub>2" "big_step (Cm (ch[!]e)) s\<^sub>c tr\<^sub>c\<^sub>m\<^sub>1 s\<^sub>c\<^sub>m"
  "big_step C2 s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>m\<^sub>2 s\<^sub>c'" "tr\<^sub>c = tr\<^sub>c\<^sub>m\<^sub>1 @ tr\<^sub>c\<^sub>m\<^sub>2"
    by (meson seqE)
  with assms(1) a0(4) obtain tr' where a2: "s\<^sub>c = s\<^sub>c\<^sub>m" "s\<^sub>p\<^sub>m = s\<^sub>p(var := e s\<^sub>c)"
  "combine_blocks chs tr\<^sub>p\<^sub>m\<^sub>2 tr\<^sub>c\<^sub>m\<^sub>2 tr'" "tr = IOBlock ch (e s\<^sub>c) # tr'"
    using sync_in_out by blast
  with a0(3) a1(2,5) show ?thesis
    using ParallelB SingleB by blast
qed   

lemma par_bigstep_out_in:
  assumes "ch \<in> chs"
      and "par_big_step (Parallel (Single (Cm (ch[!]e); C1)) chs (Single (Cm (ch[?]var); C2))) 
           (ParState (State s\<^sub>p) (State s\<^sub>c)) tr s'"
    shows "\<exists>tr'. par_big_step (Parallel (Single C1) chs (Single C2)) (ParState (State s\<^sub>p) (State (s\<^sub>c (var := e s\<^sub>p)))) tr' s'
           \<and> tr = IOBlock ch (e s\<^sub>p) # tr'"
proof-
  from assms(2) obtain s\<^sub>p' tr\<^sub>p s\<^sub>c' tr\<^sub>c where a0: "big_step (Cm (ch[!]e); C1) s\<^sub>p tr\<^sub>p s\<^sub>p'"
  "big_step (Cm (ch[?]var); C2) s\<^sub>c tr\<^sub>c s\<^sub>c'" "s' = ParState (State s\<^sub>p') (State s\<^sub>c')"
  "combine_blocks chs tr\<^sub>p tr\<^sub>c tr"
    using par_bigstep_2single by fastforce
  then obtain s\<^sub>p\<^sub>m tr\<^sub>p\<^sub>m\<^sub>1 tr\<^sub>p\<^sub>m\<^sub>2 s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>m\<^sub>1 tr\<^sub>c\<^sub>m\<^sub>2 where a1: "big_step (Cm (ch[!]e)) s\<^sub>p tr\<^sub>p\<^sub>m\<^sub>1 s\<^sub>p\<^sub>m"
  "big_step C1 s\<^sub>p\<^sub>m tr\<^sub>p\<^sub>m\<^sub>2 s\<^sub>p'" "tr\<^sub>p = tr\<^sub>p\<^sub>m\<^sub>1 @ tr\<^sub>p\<^sub>m\<^sub>2" "big_step (Cm (ch[?]var)) s\<^sub>c tr\<^sub>c\<^sub>m\<^sub>1 s\<^sub>c\<^sub>m"
  "big_step C2 s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>m\<^sub>2 s\<^sub>c'" "tr\<^sub>c = tr\<^sub>c\<^sub>m\<^sub>1 @ tr\<^sub>c\<^sub>m\<^sub>2"
    by (meson seqE)
  with assms(1) a0(4) obtain tr' where "s\<^sub>p = s\<^sub>p\<^sub>m" "s\<^sub>c\<^sub>m = s\<^sub>c(var := e s\<^sub>p)"
  "combine_blocks chs tr\<^sub>p\<^sub>m\<^sub>2 tr\<^sub>c\<^sub>m\<^sub>2 tr'" "tr = IOBlock ch (e s\<^sub>p) # tr'"
    using sync_out_in by blast
  with a0(3) a1(2,5) show ?thesis
    using ParallelB SingleB  by blast
qed

lemma par_bigstep_out_in':
  assumes "ch \<in> chs"
      and "par_big_step (Parallel (Single C1) chs (Single C2)) (ParState (State s\<^sub>p) (State (s\<^sub>c (var := e s\<^sub>p)))) tr' s'"
           "tr = IOBlock ch (e s\<^sub>p) # tr'"
    shows "par_big_step (Parallel (Single (Cm (ch[!]e); C1)) chs (Single (Cm (ch[?]var); C2)))
           (ParState (State s\<^sub>p) (State s\<^sub>c)) tr s'"
proof-
  from assms(2) obtain s\<^sub>p' tr\<^sub>p s\<^sub>c' tr\<^sub>c where a0: "big_step C1 s\<^sub>p tr\<^sub>p s\<^sub>p'" "big_step C2 (s\<^sub>c (var := e s\<^sub>p)) tr\<^sub>c s\<^sub>c'"
  "combine_blocks chs tr\<^sub>p tr\<^sub>c tr'" "s' = ParState (State s\<^sub>p') (State s\<^sub>c')"
    using par_bigstep_2single by fastforce
  then have a1: "big_step (Cm (ch[!]e); C1) s\<^sub>p (OutBlock ch (e s\<^sub>p) # tr\<^sub>p) s\<^sub>p'"
  "big_step (Cm (ch[?]var); C2) s\<^sub>c (InBlock ch (e s\<^sub>p) # tr\<^sub>c) s\<^sub>c'"
    by (metis append_Cons append_Nil sendB1 receiveB1 seqB)+
  with assms(1,3) a0(3) have "combine_blocks chs (OutBlock ch (e s\<^sub>p) # tr\<^sub>p) (InBlock ch (e s\<^sub>p) # tr\<^sub>c) tr"
    using combine_blocks_pair2 by blast
  with a1 a0(4) show ?thesis
    using ParallelB SingleB by blast
qed

lemma par_bigstep_intout_in:
  assumes "Period > 0"
      and "ch \<in> chs"
      and "par_big_step (Parallel (Single (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)])) chs (Single (Wait (\<lambda> s. Period); Cm (ch[?]var); C2))) 
          (ParState (State s\<^sub>p) (State s\<^sub>c)) tr s'"
    shows "\<exists>p tr'. ODEsol ode p Period \<and> p 0 = s\<^sub>p \<and> par_big_step (Parallel (Single C1) chs (Single C2)) 
    (ParState (State (p Period)) (State (s\<^sub>c(var := e (p Period))))) tr' s' 
     \<and> tr = (WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s\<^sub>c)) ({ch}, {})) #IOBlock ch (e (p Period)) # tr'"
proof-
  from assms(3) obtain s\<^sub>p' tr\<^sub>p s\<^sub>c' tr\<^sub>c where a0: "big_step (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) s\<^sub>p tr\<^sub>p s\<^sub>p'"
  "big_step (Wait (\<lambda> s. Period); Cm (ch[?]var); C2) s\<^sub>c tr\<^sub>c s\<^sub>c'" "s' = ParState (State s\<^sub>p') (State s\<^sub>c')"
  "combine_blocks chs tr\<^sub>p tr\<^sub>c tr"
    using par_bigstep_2single by fastforce
  with assms(1,2) obtain p tr1' tr2' tr' where "ODEsol ode p Period" "p 0 = s\<^sub>p"
  "big_step C1 (p Period) tr1' s\<^sub>p'" "big_step C2 (s\<^sub>c(var := e (p Period))) tr2' s\<^sub>c'" 
  "combine_blocks chs tr1' tr2' tr'" 
  "tr = WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s\<^sub>c)) ({ch}, {}) # IOBlock ch (e (p Period)) # tr'"
    using sync_intout[of Period ch chs ode e C1 s\<^sub>p tr\<^sub>p s\<^sub>p' var C2 s\<^sub>c tr\<^sub>c s\<^sub>c' tr] by auto
  with a0(3) show ?thesis
    by (metis ParallelB SingleB)
qed


subsection \<open>Refine a Parallel HCSP to sequential one \<close>

text \<open>Definition of refinement\<close>

fun tblk_int :: "(gstate \<times> state) set \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where
  "tblk_int \<alpha> (WaitBlock d1 p1 _) (WaitBlock d2 p2 _) =
     (d1 = d2 \<and> (\<forall>t \<in> {0..d1}. \<exists>s. p2 t = State s \<and> (p1 t, s) \<in> \<alpha>))"
| "tblk_int _ b1 b2 = (b1 = b2)"

lemma tblk_int_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tblk_int \<alpha> blk1 blk2"
    shows "tblk_int \<beta> blk1 blk2"
  using assms
  apply (cases blk1, cases blk2, simp_all)
  apply (cases blk2, simp)
  by auto

fun filter_comm_blocks :: "trace \<Rightarrow> trace" where
  "filter_comm_blocks [] = []"
| "filter_comm_blocks (WaitBlock d p r # tr) = WaitBlock d p r # filter_comm_blocks tr"
| "filter_comm_blocks (blk # tr) = filter_comm_blocks tr"

lemma filter_comm_blocks_append: "filter_comm_blocks (tr1 @ tr2) = filter_comm_blocks tr1 @ filter_comm_blocks tr2"
  apply (induct tr1, simp)
  by (case_tac a, simp_all)

definition tr_int :: "(gstate \<times> state) set \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "tr_int \<alpha> tr1 tr2 = list_all2 (tblk_int \<alpha>) (filter_comm_blocks tr1) (filter_comm_blocks tr2)"

lemma tr_int_append:
  assumes "tr_int \<alpha> tr1 tr2" "tr_int \<alpha> tr1' tr2'"
  shows "tr_int \<alpha> (tr1 @ tr1') (tr2 @ tr2')"
  by (metis assms filter_comm_blocks_append list_all2_appendI tr_int_def)

lemma tr_single_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tr_int \<alpha> tr1 tr2"
    shows "tr_int \<beta> tr1 tr2"
  using assms
  by (simp add: list_all2_mono tblk_int_weaken tr_int_def)

definition hybrid_sim_int :: "pproc \<Rightarrow> gstate \<Rightarrow> (gstate \<times> state) set \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" 
  ("'(_, _') \<sqsubseteq>\<^sub>I _ '(_, _')") where
  "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a, s\<^sub>a) = ((s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and> (\<forall>s\<^sub>c' tr\<^sub>c. par_big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longrightarrow> 
   (\<exists>s\<^sub>a' tr\<^sub>a. big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_int \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>)))"

lemma hybrid_sim_intI:
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a, s\<^sub>a)"
      and "par_big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c'"
    shows "(s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and> (\<exists>s\<^sub>a' tr\<^sub>a. big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_int \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>)"
  using assms hybrid_sim_int_def by fastforce

text \<open>Refinement rules\<close>
theorem sim_int_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a, s\<^sub>a)"
    shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>I \<beta> (P\<^sub>a, s\<^sub>a)"
  using assms
  by (meson tr_single_weaken hybrid_sim_int_def subsetD)

theorem sim_int_cons:
  assumes "(P\<^sub>c\<^sub>1', s\<^sub>c\<^sub>1) \<sqsubseteq> Id (P\<^sub>c\<^sub>1, s\<^sub>c\<^sub>1)"
      and "(P\<^sub>c\<^sub>2', s\<^sub>c\<^sub>2) \<sqsubseteq> Id (P\<^sub>c\<^sub>2, s\<^sub>c\<^sub>2)"
      and "(P\<^sub>a, s\<^sub>a) \<sqsubseteq> Id (P\<^sub>a', s\<^sub>a)"
      and "(Parallel (Single P\<^sub>c\<^sub>1) chs (Single P\<^sub>c\<^sub>2), ParState (State s\<^sub>c\<^sub>1) (State s\<^sub>c\<^sub>2)) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a, s\<^sub>a)"
    shows "(Parallel (Single P\<^sub>c\<^sub>1') chs (Single P\<^sub>c\<^sub>2'), ParState (State s\<^sub>c\<^sub>1) (State s\<^sub>c\<^sub>2)) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a', s\<^sub>a)"
  by (meson assms bigstep_sim_Id_2single hybrid_sim_int_def hybrid_sim_single_Id)

theorem sim_int_equiv:
  assumes "(P\<^sub>c\<^sub>1', s\<^sub>c\<^sub>1) \<sim> Id (P\<^sub>c\<^sub>1, s\<^sub>c\<^sub>1)"
      and "(P\<^sub>c\<^sub>2', s\<^sub>c\<^sub>2) \<sim> Id (P\<^sub>c\<^sub>2, s\<^sub>c\<^sub>2)"
      and "(P\<^sub>a, s\<^sub>a) \<sim> Id (P\<^sub>a', s\<^sub>a)"
    shows "(Parallel (Single P\<^sub>c\<^sub>1) chs (Single P\<^sub>c\<^sub>2), ParState (State s\<^sub>c\<^sub>1) (State s\<^sub>c\<^sub>2)) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a, s\<^sub>a)
    \<longleftrightarrow> (Parallel (Single P\<^sub>c\<^sub>1') chs (Single P\<^sub>c\<^sub>2'), ParState (State s\<^sub>c\<^sub>1) (State s\<^sub>c\<^sub>2)) \<sqsubseteq>\<^sub>I \<alpha> (P\<^sub>a', s\<^sub>a)"
  by (meson assms hybrid_equiv_single_def sim_int_cons)

theorem sim_int_2skip:
  assumes "(ParState (State s\<^sub>1) (State s\<^sub>2), s\<^sub>a) \<in> \<alpha>"
  shows "(Parallel (Single Skip) chs (Single Skip), ParState (State s\<^sub>1) (State s\<^sub>2)) \<sqsubseteq>\<^sub>I \<alpha> (Skip, s\<^sub>a)"
proof-
  {
    fix s\<^sub>c' tr\<^sub>c
    assume "par_big_step (Parallel (Single Skip) chs (Single Skip)) (ParState (State s\<^sub>1) (State s\<^sub>2))
            tr\<^sub>c s\<^sub>c'"
    then have "tr\<^sub>c = [] \<and> s\<^sub>c' = ParState (State s\<^sub>1) (State s\<^sub>2)"
      using par_bigstep_2skip by blast
    with assms have "\<exists>s\<^sub>a' tr\<^sub>a. big_step Skip s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_int \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
      by (metis filter_comm_blocks.simps(1) list_all2_Nil skipB tr_int_def)      
  }
  with assms show ?thesis
    by (simp add: hybrid_sim_int_def)
qed

theorem sim_comm_in_out:
  assumes "ch \<in> chs"
      and "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
      and "(Parallel (Single P\<^sub>p) chs (Single P\<^sub>c), ParState (State (s\<^sub>p(var := e s\<^sub>c))) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           (P, s\<^sub>p'(var := e s\<^sub>c))"
    shows "(Parallel (Single (Cm (ch[?]var); P\<^sub>p)) chs (Single (Cm (ch[!]e); P\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           ((var ::= (\<lambda>_. e s\<^sub>c); P), s\<^sub>p')"
proof-
  {
    fix tr\<^sub>p\<^sub>a\<^sub>r s\<^sub>p\<^sub>a\<^sub>r'
    assume "par_big_step (Parallel (Single (Cm (ch[?]var); P\<^sub>p)) chs (Single (Cm (ch[!]e); P\<^sub>c))) 
            (ParState (State s\<^sub>p) (State s\<^sub>c)) tr\<^sub>p\<^sub>a\<^sub>r s\<^sub>p\<^sub>a\<^sub>r'"
    with assms(1) obtain tr\<^sub>p\<^sub>a\<^sub>r' where a0: "par_big_step (Parallel (Single P\<^sub>p) chs (Single P\<^sub>c)) 
    (ParState (State (s\<^sub>p(var := e s\<^sub>c))) (State s\<^sub>c)) tr\<^sub>p\<^sub>a\<^sub>r' s\<^sub>p\<^sub>a\<^sub>r'" "tr\<^sub>p\<^sub>a\<^sub>r = IOBlock ch (e s\<^sub>c) # tr\<^sub>p\<^sub>a\<^sub>r'"
      using par_bigstep_in_out by blast
    then obtain tr s' where a1: "big_step P (s\<^sub>p'(var := e s\<^sub>c)) tr s'" "tr_int \<alpha> tr\<^sub>p\<^sub>a\<^sub>r' tr" "(s\<^sub>p\<^sub>a\<^sub>r', s') \<in> \<alpha>"
      using assms(3) hybrid_sim_intI by blast
    then have a3: "big_step (var ::= (\<lambda>_. e s\<^sub>c); P) s\<^sub>p' tr s'"
      using assignB seqB by fastforce
    with a0(2) a1(2) have "tr_int \<alpha> tr\<^sub>p\<^sub>a\<^sub>r tr"
      by (simp add: tr_int_def)
    with a1(3) a3 have "\<exists>s\<^sub>a' tr\<^sub>a. big_step (var ::= (\<lambda>_. e s\<^sub>c); P) s\<^sub>p' tr\<^sub>a s\<^sub>a' \<and> tr_int \<alpha> tr\<^sub>p\<^sub>a\<^sub>r tr\<^sub>a \<and> (s\<^sub>p\<^sub>a\<^sub>r', s\<^sub>a') \<in> \<alpha>"
      by blast
  }
  with assms(2) show ?thesis
    by (simp add: hybrid_sim_int_def)
qed

theorem sim_comm_out_in:
  assumes "ch \<in> chs"
      and "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
      and "(Parallel (Single P\<^sub>p) chs (Single P\<^sub>c), ParState (State s\<^sub>p) (State (s\<^sub>c(var := e s\<^sub>p)))) \<sqsubseteq>\<^sub>I \<alpha> 
           (P, s\<^sub>p')"
    shows "(Parallel (Single (Cm (ch[!]e); P\<^sub>p)) chs (Single (Cm (ch[?]var); P\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           (P, s\<^sub>p')"
proof-
  {
    fix tr\<^sub>p\<^sub>a\<^sub>r s\<^sub>p\<^sub>a\<^sub>r'
    assume "par_big_step (Parallel (Single (Cm (ch[!]e); P\<^sub>p)) chs (Single (Cm (ch[?]var); P\<^sub>c))) 
            (ParState (State s\<^sub>p) (State s\<^sub>c)) tr\<^sub>p\<^sub>a\<^sub>r s\<^sub>p\<^sub>a\<^sub>r'"
    with assms(1) obtain tr\<^sub>p\<^sub>a\<^sub>r' where a0: "par_big_step (Parallel (Single P\<^sub>p) chs (Single P\<^sub>c)) (ParState (State s\<^sub>p) (State (s\<^sub>c(var := e s\<^sub>p)))) 
     tr\<^sub>p\<^sub>a\<^sub>r' s\<^sub>p\<^sub>a\<^sub>r'" "tr\<^sub>p\<^sub>a\<^sub>r = IOBlock ch (e s\<^sub>p) # tr\<^sub>p\<^sub>a\<^sub>r'"
      using par_bigstep_out_in by blast
    then obtain tr s' where a1: "big_step P s\<^sub>p' tr s'" "tr_int \<alpha> tr\<^sub>p\<^sub>a\<^sub>r' tr" "(s\<^sub>p\<^sub>a\<^sub>r', s') \<in> \<alpha>"
      using assms(3) hybrid_sim_intI by blast
    with a0(2) have "\<exists>s\<^sub>a' tr\<^sub>a. big_step P s\<^sub>p' tr\<^sub>a s\<^sub>a' \<and> tr_int \<alpha> tr\<^sub>p\<^sub>a\<^sub>r tr\<^sub>a \<and> (s\<^sub>p\<^sub>a\<^sub>r', s\<^sub>a') \<in> \<alpha>"
      using a0(2) tr_int_def by auto
  }
  with assms(2) show ?thesis
    by (simp add: hybrid_sim_int_def)
qed

theorem sim_intout:
  assumes "0 < Period"
      and "ch \<in> chs"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
      and "\<forall>s\<^sub>p s\<^sub>c t. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) \<in> \<alpha>"
      and "\<forall>s\<^sub>p t. (Parallel (Single (Cm (ch[!]e); P\<^sub>p)) chs (Single (Cm (ch[?]var); P\<^sub>c)), 
      (ParState (State s\<^sub>p) (State s\<^sub>c))) \<sqsubseteq>\<^sub>I \<alpha> (P, s\<^sub>p(T := t))"
    shows "(Parallel (Single (Interrupt (ODE f) (\<lambda>s. True) [(ch[!]e, P\<^sub>p)])) chs (Single (Wait (\<lambda>s. Period); Cm (ch[?]var); P\<^sub>c)),
          ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P, s\<^sub>p (T := t))"
proof-
  from assms(4) have "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p (T := t)) \<in> \<alpha>"
    by blast
  {
    fix s' tr
    assume "par_big_step (Parallel (Single (Interrupt (ODE f) (\<lambda>s. True) [(ch[!]e, P\<^sub>p)])) chs 
            (Single (Wait (\<lambda>s. Period); Cm (ch[?]var); P\<^sub>c))) (ParState (State s\<^sub>p) (State s\<^sub>c)) tr s'"
    with assms(1,2) obtain p tr1 where a0: "ODEsol (ODE f) p Period" "p 0 = s\<^sub>p"
    "par_big_step (Parallel (Single P\<^sub>p) chs (Single P\<^sub>c)) (ParState (State (p Period)) 
    (State (s\<^sub>c(var := e (p Period))))) tr1 s'"
    "tr = WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s\<^sub>c)) ({ch}, {}) # IOBlock ch (e (p Period)) # tr1"
      using par_bigstep_intout_in[of Period ch chs "ODE f" e P\<^sub>p var P\<^sub>c s\<^sub>p s\<^sub>c tr s'] by auto
    with assms(2) have a0': "par_big_step (Parallel (Single (Cm (ch[!]e); P\<^sub>p)) chs (Single (Cm (ch[?]var); P\<^sub>c))) 
    (ParState (State (p Period)) (State s\<^sub>c)) (IOBlock ch (e (p Period)) # tr1) s'"
      using par_bigstep_out_in' by auto
    let ?tr = "[WaitBlk Period (\<lambda>\<tau>. State ((p \<tau>)(T := \<tau>))) ({}, {})]" and ?s\<^sub>p = "(p Period)(T := Period)"
    from assms(4,5) a0' obtain tr\<^sub>a\<^sub>1 s\<^sub>a' where a1: "big_step P ?s\<^sub>p tr\<^sub>a\<^sub>1 s\<^sub>a'" "(s', s\<^sub>a') \<in> \<alpha>" "tr_int \<alpha> tr1 tr\<^sub>a\<^sub>1"
      using hybrid_sim_intI[of "Parallel (Single (Cm (ch[!]e); P\<^sub>p)) chs (Single (Cm (ch[?]var); P\<^sub>c))"
      "ParState (State (p Period)) (State s\<^sub>c)" \<alpha> P ?s\<^sub>p "IOBlock ch (e (p Period)) # tr1" s']
      unfolding WaitBlk_def tr_int_def by auto
    from assms(1,3) a0(1,2,3) have a2: "big_step (Cont (ODE (f(T := \<lambda>_. 1))) (\<lambda>s. s T < Period)) (s\<^sub>p(T := 0)) ?tr ?s\<^sub>p"
      using bigstep_fixed_length_ode[of Period f p T ?tr "s\<^sub>p(T :=0)" ?s\<^sub>p] by auto     
    with a1(1) have a3: "big_step (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P)
    (s\<^sub>p(T := t)) (?tr @ tr\<^sub>a\<^sub>1) s\<^sub>a'"
      by (metis (mono_tags, lifting) append_Nil assignB fun_upd_upd seqB)
    with a0(4) assms(4) a1(2, 3) have "\<exists>s\<^sub>a' tr\<^sub>a. big_step (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P)
    (s\<^sub>p(T := t)) tr\<^sub>a s\<^sub>a' \<and> tr_int \<alpha> tr tr\<^sub>a \<and> (s', s\<^sub>a') \<in> \<alpha>"
      by (rule_tac x = s\<^sub>a' in exI, rule_tac x = "?tr @ tr\<^sub>a\<^sub>1" in exI, simp add: tr_int_def WaitBlk_def)
  }
  with \<open>(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p (T := t)) \<in> \<alpha>\<close> show ?thesis
    using hybrid_sim_int_def by presburger
qed

text \<open>Multiple inputs and outputs\<close>

fun inputs :: "cname \<Rightarrow> var list \<Rightarrow> proc" where
  "inputs ch [] = Skip"
| "inputs ch (v # xs) = Cm (ch[?]v); inputs ch xs"

fun outputs :: "cname \<Rightarrow> exp list \<Rightarrow> proc" where
  "outputs ch [] = Skip"
| "outputs ch (e # xs) = Cm (ch[!]e); outputs ch xs"

fun inputs_trace :: "state \<Rightarrow> cname \<Rightarrow> var list \<Rightarrow> real list \<Rightarrow> trace set" where
  "inputs_trace s ch [] [] = {[]}" |
  "inputs_trace s ch (x # xs) (v # vs) =
     { WaitBlk d (\<lambda>_. State s) ({}, {ch}) # InBlock ch v # tr
       | d tr. d \<ge> 0 \<and> tr \<in> inputs_trace (s(x := v)) ch xs vs }" |
  "inputs_trace _ _ _ _ = {}"

fun outputs_trace :: "state \<Rightarrow> cname \<Rightarrow> exp list \<Rightarrow> trace set" where
  "outputs_trace _ _ [] = {[]}" |
  "outputs_trace s ch (e # es) =
     { WaitBlk d (\<lambda>_. State s) ({ch}, {}) # OutBlock ch (e s) # tr
       | d tr. d \<ge> 0 \<and> tr \<in> outputs_trace s ch es }"

fun apply_inputs :: "state \<Rightarrow> var list \<Rightarrow> real list \<Rightarrow> state" where
  "apply_inputs s [] [] = s" |
  "apply_inputs s (v # vs) (val # vals) =
     apply_inputs (s(v := val)) vs vals" |
  "apply_inputs s _ _ = s"

fun update_vars :: "state \<Rightarrow> state \<Rightarrow> (var \<times> exp) list \<Rightarrow> state" where
  "update_vars s1 s2 [] = s1"
| "update_vars s1 s2 ((x, e) # xs) = update_vars (s1(x := e s2)) s2 xs"

lemma update_vars_cons:
  "update_vars s1 s2 (param # params) = update_vars (s1(fst param := (snd param) s2)) s2 params"
  by (metis prod.exhaust_sel update_vars.simps(2))

lemma update_vars_notchange:
  assumes "x \<notin> set (map fst params)"
  shows "(update_vars s1 s2 params) x = s1 x"
  using assms
proof(induct params arbitrary: s1)
  case Nil
  then show ?case by simp
next
  case (Cons param params)
  then have "x \<noteq> fst param" "x \<notin> set (map fst params)"
    by simp_all
  with Cons.hyps[of "s1(fst param := snd param s2)"] show ?case
    by (simp add: fun_upd_def update_vars_cons)
qed

lemma update_vars_distinct:
  assumes "distinct (map fst params)"
      and "(x, e) \<in> set params"
  shows "(update_vars s1 s2 params) x = e s2"
  using assms
proof(induct params arbitrary: s1)
  case Nil
  then show ?case by simp
next
  case (Cons param params)
  then show ?case
  proof(cases "(x, e) = param")
    assume "(x, e) = param"
    with Cons.prems(1) have "(x, e) \<notin> set params" "distinct (map fst params)"
      by auto    
    with \<open>(x, e) = param\<close> Cons.prems(1) show ?thesis
      using update_vars_notchange[of x params "s1(fst param := snd param s2)" s2] update_vars_cons
      by force
  next
    assume "(x, e) \<noteq> param"
    with Cons.prems(1,2) have "(x, e) \<in> set params" "distinct (map fst params)" "fst param \<noteq> x"
      using image_iff by fastforce+
    with Cons.hyps[of "s1(fst param := snd param s2)"] show ?thesis
      by (simp add: fun_upd_def update_vars_cons)
  qed
qed

fun assign_vars :: "state \<Rightarrow> (var \<times> exp) list  \<Rightarrow> proc" where
  "assign_vars s [] = Skip"
| "assign_vars s ((x, e) # xs) = (x ::= (\<lambda>_. e s); assign_vars s xs)"

fun assign_vars_independ :: "(var \<times> exp) list  \<Rightarrow> proc" where
  "assign_vars_independ [] = Skip"
| "assign_vars_independ ((x, e) # xs) = (x ::= e; assign_vars_independ xs)"

lemma assign_vars_cons:
  "assign_vars s (param # params) = (fst param ::= (\<lambda>_. snd param s); assign_vars s params) "
  by (metis assign_vars.simps(2) prod.collapse)

definition apply_func :: "(real list \<Rightarrow> real) \<Rightarrow> exp list \<Rightarrow> state \<Rightarrow> real" where
  "apply_func f es s = f (map (\<lambda>e. e s) es)"

lemma apply_func_equiv:
  assumes "\<forall>e \<in> set es. e s = e s'"
  shows "apply_func f es s = apply_func f es s'"
  by (smt (verit, ccfv_SIG) apply_func_def assms map_eq_conv)

definition vars2exps :: "var list \<Rightarrow> exp list" where
  "vars2exps vs = map (\<lambda>v. \<lambda>s. s v) vs"

definition eval_vars :: "var list \<Rightarrow> state \<Rightarrow> real list" where
  "eval_vars vs s = map (\<lambda>v. s v) vs"

definition eval_exps :: "exp list \<Rightarrow> state \<Rightarrow> real list" where
  "eval_exps es s = map (\<lambda>e. e s) es"

lemma apply_func_on_vars:
  "apply_func f (vars2exps vs) s = f (eval_vars vs s)"
  apply (simp add: vars2exps_def apply_func_def eval_vars_def)
  by (metis comp_apply)

definition construct_params :: "(var \<times> (real list \<Rightarrow> real)) list \<Rightarrow> exp list \<Rightarrow> (var \<times> exp) list" where
  "construct_params params exps = map (\<lambda>(v, f). (v, apply_func f exps)) params"

lemma construct_params_fst: "map fst (construct_params params exps) = map fst params"
  apply (simp add: construct_params_def)
  by auto

lemma construct_params_snd: "map snd (construct_params params exps) = 
                             map (\<lambda>f. apply_func f exps) (map snd params)"
  apply (simp add: construct_params_def)
  by auto

text \<open>send [e1 ... en] to [v1, ..., vn], then receive fi [v1 ... vn]\<close>
theorem sim_ins_outs_correspond:
  assumes "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "funs\<^sub>c = map snd params\<^sub>2"
      and "distinct vars\<^sub>c" 
      and "\<forall>e \<in> set exps\<^sub>p. e s\<^sub>p = e s\<^sub>p'"
      and "\<forall>e v. e \<in> set exps\<^sub>p \<longrightarrow> v \<in> set vars\<^sub>p \<longrightarrow> exp_independ e v"
    shows "(assign_vars (update_vars s\<^sub>c s\<^sub>p params\<^sub>1) (construct_params params\<^sub>2 (vars2exps vars\<^sub>c)), s\<^sub>p') \<sqsubseteq> Id 
           (assign_vars_independ (construct_params params\<^sub>2 exps\<^sub>p), s\<^sub>p')"
  using assms(3,4,6,7)
proof(induct params\<^sub>2 arbitrary: vars\<^sub>p vars\<^sub>p funs\<^sub>c s\<^sub>p' s\<^sub>p)
  case Nil
  then show ?case 
    apply (simp add: construct_params_def)
    using refl_Id sim_refl by blast
next
  case (Cons a params\<^sub>2)
  let ?s\<^sub>c = "update_vars s\<^sub>c s\<^sub>p params\<^sub>1"
  from assms(1,2,5) have "\<forall>i < length params\<^sub>1. ?s\<^sub>c (vars\<^sub>c ! i) = (exps\<^sub>p ! i) s\<^sub>p"
    using update_vars_distinct by auto
  with assms(1,2) have a0: "eval_vars vars\<^sub>c ?s\<^sub>c = eval_exps exps\<^sub>p s\<^sub>p"
    by (smt (verit, del_insts) eval_exps_def eval_vars_def length_map map_equality_iff)
  obtain v f where a1: "a = (v, f)"
    using old.prod.exhaust by blast
  with a0 have a2: "assign_vars ?s\<^sub>c (construct_params (a # params\<^sub>2) (vars2exps vars\<^sub>c)) = 
  v ::= (\<lambda>_. f (eval_exps exps\<^sub>p s\<^sub>p)); assign_vars ?s\<^sub>c (construct_params params\<^sub>2 (vars2exps vars\<^sub>c))"
    by (simp add: construct_params_def apply_func_on_vars)
  with a1 have a3: "assign_vars_independ (construct_params (a # params\<^sub>2) exps\<^sub>p) = 
  v ::= apply_func f exps\<^sub>p; assign_vars_independ (construct_params params\<^sub>2 exps\<^sub>p)"
    by (simp add: construct_params_def)
  with Cons.prems(3) have a4: "(v ::= (\<lambda>_. f (eval_exps exps\<^sub>p s\<^sub>p)), s\<^sub>p') \<sqsubseteq> Id (v ::= apply_func f exps\<^sub>p, s\<^sub>p')"
    by (metis (lifting) apply_func_def apply_func_equiv assignB assignE eval_exps_def hybrid_sim_single_Id)
  with a2 a3 show ?case
    apply (simp, rule_tac sim_seq_Id, simp_all)
    by (smt (verit, ccfv_threshold) Cons.hyps Cons.prems(1,3,4) a1 assignE fst_conv
        list.set_intros(1,2) list.simps(9) reachable_def exp_independ_def)
qed

lemma sim_comm_outs:
  assumes "ch \<in> chs"
      and "\<forall>s\<^sub>c. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
      and "vars = map fst params" "exps = map snd params"
      and "(Parallel (Single P\<^sub>p) chs (Single P\<^sub>c), ParState (State s\<^sub>p) (State (update_vars s\<^sub>c s\<^sub>p params))) \<sqsubseteq>\<^sub>I \<alpha> 
           (P, s\<^sub>p')"
    shows "(Parallel (Single (outputs ch exps; P\<^sub>p)) chs (Single (inputs ch vars; P\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           (P, s\<^sub>p')"
  using assms(3,4,5)
proof(induct params arbitrary: s\<^sub>c vars exps)
  case Nil
  then show ?case
    using sim_int_equiv[of P\<^sub>p s\<^sub>p "Skip; P\<^sub>p" P\<^sub>c s\<^sub>c "Skip; P\<^sub>c" P s\<^sub>p' P chs \<alpha>] 
          equiv_Id_single_skipl hybrid_equiv_single_Id 
    by auto   
next
  case (Cons param params)
  from Cons.hyps Cons.prems have 
  "(Parallel (Single (outputs ch (map snd params); P\<^sub>p)) chs (Single (inputs ch (map fst params); P\<^sub>c)), 
   ParState (State s\<^sub>p) (State (s\<^sub>c(fst param := snd param s\<^sub>p)))) \<sqsubseteq>\<^sub>I \<alpha> (P, s\<^sub>p')"
    by (simp only: update_vars_cons)
  with assms(1,2)  have "(Parallel (Single (Cm (ch[!]snd param); outputs ch (map snd params); P\<^sub>p)) chs
  (Single (Cm (ch[?]fst param); inputs ch (map fst params); P\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> (P, s\<^sub>p')"
    using sim_comm_out_in[of ch chs s\<^sub>p s\<^sub>c s\<^sub>p' \<alpha> "outputs ch (map snd params); P\<^sub>p" "inputs ch (map fst params); P\<^sub>c"
    "fst param" "snd param" P]
    by auto
  with Cons.prems show ?case
    by (rule_tac sim_int_cons, simp_all add: big_step_seq_assoc hybrid_sim_single_Id)    
qed

definition gstate_single_rel :: "state \<Rightarrow> (gstate \<times> state) set \<Rightarrow> bool" where
  "gstate_single_rel s\<^sub>c \<alpha>  = (\<forall>V v s\<^sub>p s\<^sub>p'. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha> \<longrightarrow> 
  (ParState (State (s\<^sub>p(V := v))) (State s\<^sub>c), s\<^sub>p'(V := v)) \<in> \<alpha>)"

lemma update_sat_rel:
  assumes "gstate_single_rel s\<^sub>c \<alpha>"
      and "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
    shows "(ParState (State (update_vars s\<^sub>p s\<^sub>c params)) (State s\<^sub>c), update_vars s\<^sub>p' s\<^sub>c params) \<in> \<alpha>" 
  using assms(2)
proof(induct params arbitrary: s\<^sub>p s\<^sub>p')
  case Nil
  with assms(2) show ?case by simp
next
  case (Cons param params)
  from Cons.hyps[of "s\<^sub>p(fst param := (snd param) s\<^sub>c)" "s\<^sub>p'(fst param := (snd param) s\<^sub>c)"]
  Cons.prems assms(1) show ?case 
    by (metis gstate_single_rel_def update_vars_cons)
qed

lemma sim_comm_ins:
  assumes "ch \<in> chs"
      and "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
      and "gstate_single_rel s\<^sub>c \<alpha>"
      and "vars = map fst params" "exps = map snd params"
      and "(Parallel (Single P\<^sub>p) chs (Single P\<^sub>c), ParState (State (update_vars s\<^sub>p s\<^sub>c params)) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           (P, update_vars s\<^sub>p' s\<^sub>c params)"
    shows "(Parallel (Single (inputs ch vars; P\<^sub>p)) chs (Single (outputs ch exps; P\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           (assign_vars s\<^sub>c params; P, s\<^sub>p')"
  using assms(2,4,5,6)
proof(induct params arbitrary: s\<^sub>p s\<^sub>p' vars exps)
  case Nil
  then show ?case
using sim_int_equiv[of P\<^sub>p s\<^sub>p "Skip; P\<^sub>p" P\<^sub>c s\<^sub>c "Skip; P\<^sub>c" P s\<^sub>p P chs \<alpha>] 
          equiv_Id_single_skipl hybrid_equiv_single_Id 
    apply (rule_tac sim_int_cons, simp_all) using hybrid_equiv_single_def by blast+
next
  case (Cons param params)
  with assms(3) have "(ParState (State (s\<^sub>p(fst param := snd param s\<^sub>c))) (State s\<^sub>c), s\<^sub>p'(fst param := snd param s\<^sub>c)) \<in> \<alpha>"
    by (simp add: gstate_single_rel_def)
  with Cons.hyps[of "s\<^sub>p(fst param := (snd param) s\<^sub>c)" "s\<^sub>p'(fst param := (snd param) s\<^sub>c)"
  "map fst params" "map snd params"] Cons.prems have
  "(Parallel (Single (inputs ch (map fst params); P\<^sub>p)) chs
   (Single (outputs ch (map snd params); P\<^sub>c)), ParState (State (s\<^sub>p(fst param := snd param s\<^sub>c))) (State s\<^sub>c)) 
   \<sqsubseteq>\<^sub>I \<alpha> (assign_vars s\<^sub>c params; P, s\<^sub>p'(fst param := snd param s\<^sub>c))"
    by (simp only: update_vars_cons)
  with assms(1) Cons.prems(1) have "(Parallel (Single (Cm (ch[?]fst param); inputs ch (map fst params); P\<^sub>p)) chs
  (Single (Cm (ch[!]snd param); outputs ch (map snd params); P\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) 
  \<sqsubseteq>\<^sub>I \<alpha> (fst param ::= (\<lambda>_. snd param s\<^sub>c); assign_vars s\<^sub>c params; P, s\<^sub>p')"
    using sim_comm_in_out[of ch chs s\<^sub>p s\<^sub>c s\<^sub>p' \<alpha> "inputs ch (map fst params); P\<^sub>p" "outputs ch (map snd params); P\<^sub>c"
    "fst param" "snd param" "assign_vars s\<^sub>c params; P"] by auto
  with Cons.prems show ?case
    by (rule_tac sim_int_cons, simp_all add: big_step_seq_assoc hybrid_sim_single_Id assign_vars_cons)
qed

corollary sim_comm_ins':
  assumes "ch \<in> chs"
      and "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
      and "gstate_single_rel s\<^sub>c \<alpha>"
      and "vars = map fst params" "exps = map snd params"
    shows "(Parallel (Single (inputs ch vars)) chs (Single (outputs ch exps)), ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
           (assign_vars s\<^sub>c params, s\<^sub>p')"
proof-
  from assms have "(Parallel (Single (inputs ch vars; Skip)) chs (Single (outputs ch exps; Skip)), 
  ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> (assign_vars s\<^sub>c params; Skip, s\<^sub>p')"
    apply (rule_tac sim_comm_ins, simp_all)
    using update_sat_rel sim_int_2skip by auto
  then show ?thesis
    apply (rule_tac sim_int_cons, simp_all)
    using equiv_Id_single_skipr hybrid_equiv_single_def by blast+
qed

lemma sim_comm_outs_ins:
  assumes "ch\<^sub>p\<^sub>2\<^sub>c \<in> chs" "ch\<^sub>c\<^sub>2\<^sub>p \<in> chs"
      and "\<forall>s\<^sub>c. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
      and "gstate_single_rel (update_vars s\<^sub>c s\<^sub>p params\<^sub>1) \<alpha>"
      and "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "exps\<^sub>c = map snd params\<^sub>2"
    shows "(Parallel (Single (outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)) chs 
                     (Single (inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), ParState (State s\<^sub>p) (State s\<^sub>c)) 
     \<sqsubseteq>\<^sub>I \<alpha> (assign_vars (update_vars s\<^sub>c s\<^sub>p params\<^sub>1) params\<^sub>2, s\<^sub>p')"
  using assms
  apply (rule_tac sim_comm_outs, simp_all)
  using sim_comm_ins'[of ch\<^sub>c\<^sub>2\<^sub>p chs s\<^sub>p "update_vars s\<^sub>c s\<^sub>p params\<^sub>1" s\<^sub>p' \<alpha> vars\<^sub>p params\<^sub>2 exps\<^sub>c]
  by auto

text \<open>Refinement rule for single loop body\<close>
lemma sim_single_control_loop:
  assumes "ch\<^sub>p\<^sub>2\<^sub>c \<in> chs" "ch\<^sub>c\<^sub>2\<^sub>p \<in> chs"
      and "\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"
      and "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "exps\<^sub>c = map snd params\<^sub>2"
      and "0 < Period"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
      and "\<forall>s\<^sub>p s\<^sub>p' s\<^sub>c. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha> \<longrightarrow> 
          (assign_vars (update_vars s\<^sub>c s\<^sub>p ((var, e) # params\<^sub>1)) params\<^sub>2, s\<^sub>p') \<sqsubseteq> Id (P, s\<^sub>p')"
    shows "(Parallel (Single (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)])) 
    chs (Single (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)),
    ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
    (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P, s\<^sub>p (T := t))"
proof-
  {
    fix s\<^sub>p' t 
    from assms(3) have a0: "\<forall>s\<^sub>c. (ParState (State s\<^sub>p') (State s\<^sub>c), s\<^sub>p'(T := t)) \<in> \<alpha>"
      by blast
    from assms(3) have a1: "gstate_single_rel (update_vars s\<^sub>c s\<^sub>p' ((var, e) # params\<^sub>1)) \<alpha>"
      apply (simp add: gstate_single_rel_def, clarsimp)
      by (metis fun_upd_twist fun_upd_upd)
    with a0 assms have "(Parallel (Single (outputs ch\<^sub>p\<^sub>2\<^sub>c (e # exps\<^sub>p); inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)) chs
    (Single (inputs ch\<^sub>p\<^sub>2\<^sub>c (var # vars\<^sub>c); outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), ParState (State s\<^sub>p') (State s\<^sub>c)) 
    \<sqsubseteq>\<^sub>I \<alpha> (assign_vars (update_vars s\<^sub>c s\<^sub>p' ((var, e) # params\<^sub>1)) params\<^sub>2, s\<^sub>p'(T := t))"
      using sim_comm_outs_ins[of ch\<^sub>p\<^sub>2\<^sub>c chs ch\<^sub>c\<^sub>2\<^sub>p s\<^sub>p' "s\<^sub>p'(T := t)" \<alpha> s\<^sub>c "(var, e) # params\<^sub>1" "var # vars\<^sub>c" 
      "e # exps\<^sub>p" vars\<^sub>p params\<^sub>2 exps\<^sub>c] by auto
    then have "(Parallel (Single (Cm (ch\<^sub>p\<^sub>2\<^sub>c[!]e); outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)) chs
    (Single (Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), ParState (State s\<^sub>p') (State s\<^sub>c)) 
    \<sqsubseteq>\<^sub>I \<alpha> (assign_vars (update_vars s\<^sub>c s\<^sub>p' ((var, e) # params\<^sub>1)) params\<^sub>2, s\<^sub>p'(T := t))"
      by (rule_tac sim_int_cons, simp_all add: big_step_seq_assoc hybrid_sim_single_Id)
    with assms(10) a0 have "(Parallel (Single (Cm (ch\<^sub>p\<^sub>2\<^sub>c[!]e); outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)) chs
    (Single (Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), ParState (State s\<^sub>p') (State s\<^sub>c)) 
    \<sqsubseteq>\<^sub>I \<alpha> (P, s\<^sub>p'(T := t))"
      by (meson hybrid_sim_single_Id sim_int_cons)
  }
  with assms show ?thesis
    using sim_intout[of Period ch\<^sub>p\<^sub>2\<^sub>c chs T f \<alpha> e "outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p" var
    "inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c" s\<^sub>c "P" s\<^sub>p t]
    by auto
qed

corollary sim_single_control_loop':
  assumes "ch\<^sub>p\<^sub>2\<^sub>c \<in> chs" "ch\<^sub>c\<^sub>2\<^sub>p \<in> chs"
      and "\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"
      and "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "exps\<^sub>c = map snd params\<^sub>2"
      and "0 < Period"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
      and "\<forall>s\<^sub>p s\<^sub>p' s\<^sub>c. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha> \<longrightarrow> 
          (assign_vars (update_vars s\<^sub>c s\<^sub>p ((var, e) # params\<^sub>1)) params\<^sub>2, s\<^sub>p') \<sqsubseteq> Id (P, s\<^sub>p')"
    shows "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<longrightarrow>
    (Parallel (Single (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)]))
    chs (Single (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> 
    (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P, s\<^sub>a)"
proof-
  {
    fix s\<^sub>c s\<^sub>a
    assume "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
    with assms(3) obtain s\<^sub>p' s\<^sub>c' t where "s\<^sub>c = (ParState (State s\<^sub>p') (State s\<^sub>c'))" "s\<^sub>a = s\<^sub>p'(T := t)"
      by blast
    with assms have "(Parallel (Single (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)])) 
    chs (Single (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> 
    (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P, s\<^sub>a)"
      using sim_single_control_loop[of ch\<^sub>p\<^sub>2\<^sub>c chs ch\<^sub>c\<^sub>2\<^sub>p \<alpha> T vars\<^sub>c params\<^sub>1 exps\<^sub>p vars\<^sub>p params\<^sub>2 exps\<^sub>c Period
      f var e P s\<^sub>p' s\<^sub>c' t] by auto
  }
  then show ?thesis
    by blast
qed

subsection \<open>loop rules for P1 || P2 \<sqsubseteq> P \<Longrightarrow> Rep P1 || Rep P2 \<sqsubseteq> Rep P\<close>

text \<open>can not execute without other threads help\<close>

definition wait_sync :: "proc \<Rightarrow> cname set \<Rightarrow>  bool" where
  "wait_sync P chs = (\<forall>s s' tr tr' tr''. big_step P s tr s' \<longrightarrow> \<not> combine_blocks chs (tr @ tr') [] tr'')"

lemma wait_sync_seq:
  assumes "wait_sync P chs"
  shows "wait_sync (P;Q) chs"
proof-
  {
    fix s s' tr tr' tr''
    assume "big_step (P;Q) s tr s'"
    then obtain tr1 tr2 sm where "big_step P s tr1 sm" "big_step Q sm tr2 s'" "tr = tr1 @ tr2"
      by (metis seqE)
    with assms have "\<not> combine_blocks chs (tr @ tr') [] tr''"
      by (simp add: wait_sync_def)
  }
  then show ?thesis
    by (simp add: wait_sync_def)
qed

lemma wait_sync_seq_assoc:
  assumes "wait_sync ((P1; P2); P3) chs"
  shows "wait_sync (P1; P2; P3) chs"
  using assms big_step_seq_assoc wait_sync_def by force

lemma wait_sync_intout:
  assumes "ch \<in> chs"
  shows "wait_sync (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) chs"
proof-
  {
    fix s s' tr tr' tr''
    assume "big_step (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) s tr s'"
    then have "\<not> combine_blocks chs (tr @ tr') [] tr''"
    proof(cases rule: interruptE, simp)
      fix i cha ea p2 tr2
      assume "tr = OutBlock cha (ea s) # tr2"
         and "i < length [(ch[!]e, C1)]"
         and "[(ch[!]e, C1)] ! i = (cha[!]ea, p2)"
      then have "tr = OutBlock ch (ea s) # tr2" by simp
      then show ?thesis
        by (metis append_Cons assms combine_blocks_emptyE3)
    next
      fix d p i cha ea p2 tr2
      assume "tr = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice [(ch[!]e, C1)]) # OutBlock cha (ea (p d)) # tr2"
         and "i < length [(ch[!]e, C1)]"
         and "[(ch[!]e, C1)] ! i = (cha[!]ea, p2)"
      then have "tr = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({ch}, {}) # OutBlock ch (ea (p d)) # tr2" by simp
      then show ?thesis
        by (metis append_Cons combine_blocks_emptyE2)
    next
      fix i cha var p2 v tr2
      assume "i < length [(ch[!]e, C1)]" "[(ch[!]e, C1)] ! i = (cha[?]var, p2)"
      then show ?thesis by simp
    next
      fix d p i cha var p2 v tr2
      assume "i < length [(ch[!]e, C1)]" "[(ch[!]e, C1)] ! i = (cha[?]var, p2)"
      then show ?thesis by simp
    next
      assume "\<not> True"
      then show ?thesis by simp
    next
      fix d p
      assume "\<not> True"
      then show ?thesis by simp
    qed
  }
  then show ?thesis
    by (simp add: wait_sync_def)
qed

lemma wait_sync_wait_in:
  assumes "ch \<in> chs"
      and "Period > 0"
    shows "wait_sync (Wait (\<lambda>s. Period); Cm (ch[?]var)) chs"
proof-
  {
    fix s s' tr tr' tr''
    assume "big_step (Wait (\<lambda>s. Period); Cm (ch[?]var)) s tr s'"
    with assms(2) obtain tr1 where "big_step (Cm (ch[?]var)) s tr1 s'" "tr = WaitBlk Period (\<lambda>_. State s) ({}, {}) # tr1"
      by (metis (mono_tags, lifting) assms(2) big_step_wait_seq)
    then have "\<not> combine_blocks chs (tr @ tr') [] tr''"
    proof(cases rule: receiveE, simp)
      fix v
      assume "tr1 = [InBlock ch v]"
         and "tr = WaitBlk Period (\<lambda>_. State s) ({}, {}) # tr1"
      then show ?thesis
        by (metis append_Cons combine_blocks_emptyE2)
    next
      fix d v
      assume "tr1 = [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v]"
         and "tr = WaitBlk Period (\<lambda>_. State s) ({}, {}) # tr1"
      then show ?thesis
        by (metis append_Cons combine_blocks_emptyE2)
    qed
  }
  then show ?thesis
    by (simp add: wait_sync_def)
qed

text \<open>synchronized program must execute in a lock step manner, execute simultaneously, and then execute remaining\<close>

definition sync_prog :: "proc \<Rightarrow> cname set \<Rightarrow> proc \<Rightarrow> bool" where
  "sync_prog P1 chs P2 = (\<forall>s1 s2 tr1 tr2 s1' s2' tr tr1' tr2'. 
  big_step P1 s1 tr1 s1' \<longrightarrow> big_step P2 s2 tr2 s2' \<longrightarrow> 
  combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr \<longrightarrow> 
  (\<exists>tr' tr''. tr = tr' @ tr'' \<and> combine_blocks chs tr1 tr2 tr' \<and> combine_blocks chs tr1' tr2' tr''))"

lemma sync_lockstep:
  assumes "wait_sync P1 chs" "wait_sync P2 chs"
      and "sync_prog P1 chs P2"
      and "iterate_bigstep m (s1, []) P1 (s1', tr1)"
      and "iterate_bigstep n (s2, []) P2 (s2', tr2)"
      and "combine_blocks chs tr1 tr2 tr"
    shows "m = n"
  using assms
proof(induct m arbitrary: n s1 s2 tr1 tr2 tr)
  case 0
  then have a0: "tr1 = []"
    by simp
  then show ?case
  proof(cases "n = 0")
    case True
    then show ?thesis by auto
  next
    case False
    then obtain n' where "n = Suc n'"
      by (meson old.nat.exhaust)
    with "0.prems"(5) obtain s2m tr2m tr2' where b0:
    "big_step P2 s2 tr2m s2m"  "tr2 = tr2m @ tr2'"
      using iterate_bigstep_converse[of n' s2 Nil P2 s2' tr2] iterate_bigstep_init'
      by blast
    from "0.prems"(6) obtain tr' where b1: "combine_blocks chs tr2 tr1 tr'"
      using combine_blocks_symmetric by blast
    with "0.prems"(2) a0 b0 show ?thesis
      by (simp add: wait_sync_def)
  qed
next
  case (Suc m)
  then obtain s1m tr1m trm1' where c0: "big_step P1 s1 tr1m s1m" 
  "iterate_bigstep m (s1m, []) P1 (s1', trm1')" "tr1 = tr1m @ trm1'"
    using iterate_bigstep_converse[of m s1 Nil P1 s1' tr1] iterate_bigstep_init' 
    by blast  
  then show ?case
  proof(cases "n = 0")
    case True
    with Suc.prems(5) have d0: "tr2 = []"
      by simp
    with c0(1,3) Suc.prems(1,6) show ?thesis
      using wait_sync_def by blast
  next
    case False
    then obtain n' where e0: "n = Suc n'"
      by (meson old.nat.exhaust)
    with Suc.prems(5) obtain s2m tr2m trm2' where e1: "big_step P2 s2 tr2m s2m"  
    "iterate_bigstep n' (s2m, []) P2 (s2', trm2')" "tr2 = tr2m @ trm2'"
      using iterate_bigstep_converse[of n' s2 Nil P2 s2' tr2] iterate_bigstep_init'
      by blast
    with Suc.prems(3,6) c0(1,3) obtain tr'' where "combine_blocks chs trm1' trm2' tr''"
      using sync_prog_def by blast
    with Suc.prems(1,2,3,6) c0(2) e1(2) Suc.hyps[of s1m trm1' n' s2m trm2' tr''] have "m = n'"
      by fastforce
    with e0 show ?thesis
      by auto
  qed
qed

lemma sync_lockstep_sim:
  assumes "sync_prog P1 chs P2"
      and "iterate_bigstep n (s1, []) P1 (s1', tr1)"
      and "iterate_bigstep n (s2, []) P2 (s2', tr2)"
      and "combine_blocks chs tr1 tr2 tr"
      and "(ParState (State s1) (State s2), sa) \<in> \<alpha>"
      and "\<forall>s1 s2 sa. (ParState (State s1) (State s2), sa) \<in> \<alpha> \<longrightarrow> (\<forall>s1' s2' tr1 tr2 tr. 
      big_step P1 s1 tr1 s1' \<longrightarrow> big_step P2 s2 tr2 s2' \<longrightarrow> combine_blocks chs tr1 tr2 tr \<longrightarrow>
      (\<exists>sa' tra. big_step P sa tra sa' \<and> tr_int \<alpha> tr tra \<and> (ParState (State s1') (State s2'), sa') \<in> \<alpha>))"
    shows "\<exists>sa' tra. iterate_bigstep n (sa, []) P (sa', tra) \<and> tr_int \<alpha> tr tra \<and> (ParState (State s1') (State s2'), sa') \<in> \<alpha>"
  using assms
proof(induct n arbitrary: s1 tr1 s2 tr2 sa tr)
  case 0
  then have "tr1 = []" "s1 = s1'" "tr2 = []" "s2 = s2'"
    by simp_all
  with "0.prems"(4,5) show ?case
    using combine_blocks_emptyE1 tr_int_def by fastforce
next
  case (Suc n)
  then obtain s1m tr1m tr1m' s2m tr2m tr2m' where a0: "big_step P1 s1 tr1m s1m" 
  "iterate_bigstep n (s1m, []) P1 (s1', tr1m')" "tr1 = tr1m @ tr1m'"
  "big_step P2 s2 tr2m s2m"  "iterate_bigstep n (s2m, []) P2 (s2', tr2m')" "tr2 = tr2m @ tr2m'"
    using iterate_bigstep_converse[of n s1 Nil P1 s1' tr1] 
          iterate_bigstep_converse[of n s2 Nil P2 s2' tr2] iterate_bigstep_init'
    by (metis append_Nil)
  with Suc.prems(1,4) obtain trm trm' where a1: "tr = trm @ trm'" "combine_blocks chs tr1m tr2m trm" 
  "combine_blocks chs tr1m' tr2m' trm'"
    by (smt (verit, ccfv_threshold) sync_prog_def)
  with a0(1,4) Suc.prems(5,6) obtain sam tram where a2: "big_step P sa tram sam" "tr_int \<alpha> trm tram"
  "(ParState (State s1m) (State s2m), sam) \<in> \<alpha>"
    by blast
  with Suc.hyps[of s1m tr1m' s2m tr2m' trm' sam] Suc.prems(1,6) a0(2,5) a1(3)
  obtain sa' tram' where a3: "iterate_bigstep n (sam, []) P (sa', tram')" 
  "tr_int \<alpha> trm' tram'" "(ParState (State s1') (State s2'), sa') \<in> \<alpha>" 
    by auto
  with a2(1) have a4: "iterate_bigstep (Suc n) (sa, []) P (sa', tram @ tram')"
    by (metis append_Nil iterate_bigstep_converse iterate_bigstep_init)
  from a3(2) a2(2) a1(1) have a5: "tr_int \<alpha> tr (tram @ tram')"
    by (simp add: tr_int_append)
  with a4 a3(3) show ?case
  by blast
qed

theorem sim_rep_sync:
  assumes "sync_prog P1 chs P2"
      and "wait_sync P1 chs" "wait_sync P2 chs"
      and "(ParState (State s1) (State s2), s) \<in> \<alpha>"
      and "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<longrightarrow> (Parallel (Single P1) chs (Single P2), s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> (P, s\<^sub>a)"
    shows "(Parallel (Single (Rep P1)) chs (Single (Rep P2)), (ParState (State s1) (State s2))) \<sqsubseteq>\<^sub>I \<alpha> (Rep P, s)"
proof-
  {
    fix s\<^sub>c' tr\<^sub>c
    assume "par_big_step (Parallel (Single (Rep P1)) chs (Single (Rep P2))) (ParState (State s1) (State s2)) tr\<^sub>c s\<^sub>c'"
    then obtain s1' s2' tr1 tr2 where a0: "big_step (Rep P1) s1 tr1 s1'" "big_step (Rep P2) s2 tr2 s2'"
    "s\<^sub>c' = ParState (State s1') (State s2')" "combine_blocks chs tr1 tr2 tr\<^sub>c"
      using par_bigstep_2single by fastforce
    then obtain m n where a1: "iterate_bigstep m (s1, []) P1 (s1', tr1)" "iterate_bigstep n (s2, []) P2 (s2', tr2)"
      by (metis append_Nil big_step_while)  
    with assms(1,2,3) a0(4) have a2: "m = n"
      using sync_lockstep by blast
      {
        fix s1 s2 sa s1' s2' tr1 tr2 tr
        assume b0: "(ParState (State s1) (State s2), sa) \<in> \<alpha>"
           and b1: "big_step P1 s1 tr1 s1'" "big_step P2 s2 tr2 s2'" 
           and b2: "combine_blocks chs tr1 tr2 tr"
        then have "par_big_step (Parallel (Single P1) chs (Single P2)) 
        (ParState (State s1) (State s2)) tr (ParState (State s1') (State s2'))"
          using ParallelB SingleB by blast
        with b0 assms(5) have  "\<exists>sa' tra. big_step P sa tra sa' \<and> tr_int \<alpha> tr tra \<and> 
        (ParState (State s1') (State s2'), sa') \<in> \<alpha>"
          using hybrid_sim_intI by blast
      }
      with a0(3,4) assms(1,4) a1 a2 have "\<exists>s' tr. big_step (Rep P) s tr s' \<and> 
      tr_int \<alpha> tr\<^sub>c tr \<and> (s\<^sub>c', s') \<in> \<alpha>"
        using sync_lockstep_sim[of P1 chs P2 n s1 s1' tr1 s2 s2' tr2 tr\<^sub>c s \<alpha> P]
        by (metis append_Nil big_step_while)        
    }
    then show ?thesis
      by (simp add: assms(4) hybrid_sim_int_def)
  qed


text \<open>Original sync_prog is not seqential compositional, the reason lies in cases when the wait time
before IO event is incompatible, sync_prog (wait d1; ch[!]v) chs (wait d2; ch[?]var) is true,
but sync_prog (wait d1; ch[!]v; C1) chs wait (d2; ch[?]var; C2) is not necesarrily true. We stregthen the 
combine_blocks to forbid this situation\<close>

inductive combine_blocks_compat :: "cname set \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  \<comment> \<open>Empty case\<close>
  combine_blocks_compat_empty:
  "combine_blocks_compat comms [] [] []"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_compat_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks_compat comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks_compat comms (InBlock ch v # blks1) (OutBlock ch v # blks2) (IOBlock ch v # blks)"
| combine_blocks_compat_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks_compat comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks_compat comms (OutBlock ch v # blks1) (InBlock ch v # blks2) (IOBlock ch v # blks)"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_compat_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks_compat comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks_compat comms (CommBlock ch_type ch v # blks1) blks2 (CommBlock ch_type ch v # blks)"
| combine_blocks_compat_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks_compat comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks_compat comms blks1 (CommBlock ch_type ch v # blks2) (CommBlock ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_compat_wait1:
  "combine_blocks_compat comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks_compat comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy # blks)"

lemma combine_blocks_implies:
  assumes "combine_blocks_compat chs tr1 tr2 tr"
  shows "combine_blocks chs tr1 tr2 tr"
  using assms
  apply (induct rule: combine_blocks_compat.induct)
       apply (simp add: combine_blocks_empty)
      apply (simp add: combine_blocks_pair1)
     apply (simp add: combine_blocks_pair2)
    apply (simp add: combine_blocks_unpair1)
   apply (simp add: combine_blocks_unpair2)
  by (simp add: combine_blocks_wait1)

lemma combine_blocks_compat_append:
  assumes "combine_blocks_compat chs tr1 tr2 tr"
      and "combine_blocks_compat chs tr1' tr2' tr'"
    shows "combine_blocks_compat chs (tr1 @ tr1') (tr2 @ tr2') (tr @ tr')"
  using assms
  apply(induct rule: combine_blocks_compat.induct, simp)
      apply (simp add: combine_blocks_compat_pair1)
     apply (simp add: combine_blocks_compat_pair2)
    apply (simp add: combine_blocks_compat_unpair1)
   apply (simp add: combine_blocks_compat_unpair2)
  using combine_blocks_compat_wait1 by auto

text \<open>Stronger property that enable sequential composition\<close>

definition sync_prog_compat :: "proc \<Rightarrow> cname set \<Rightarrow> proc \<Rightarrow> bool" where
  "sync_prog_compat P1 chs P2 = (\<forall>s1 s2 tr1 tr2 s1' s2' tr tr1' tr2'. 
  big_step P1 s1 tr1 s1' \<longrightarrow> big_step P2 s2 tr2 s2' \<longrightarrow> 
  combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr \<longrightarrow> 
  (\<exists>tr' tr''. tr = tr' @ tr'' \<and> combine_blocks_compat chs tr1 tr2 tr' \<and> combine_blocks chs tr1' tr2' tr''))"

lemma sync_prog_implies:
  assumes "sync_prog_compat P1 chs P2"
  shows "sync_prog P1 chs P2"
  using assms
  apply (simp add: sync_prog_compat_def sync_prog_def)
  using combine_blocks_implies by meson

definition dense :: "proc \<Rightarrow> bool" where
  "dense P = (\<forall>s tr s'. big_step P s tr s' \<longrightarrow> tr = [])"

lemma sync_prog_compat_dense:
  assumes "dense P1" "dense P2"
  shows "sync_prog_compat P1 chs P2"
  using assms
  apply (simp add: dense_def sync_prog_compat_def)
  by (metis append_Nil combine_blocks_compat_empty)

text \<open>dense program means pure computational program, which produce no trace\<close>
lemma dense_skip: "dense Skip"
  using dense_def skipE by blast

lemma dense_assign: "dense (x ::= e)"
  using assignE dense_def by blast

lemma dense_havoc: "dense (x ::= *)"
  using HavocE dense_def by blast

lemma dense_assume: "dense (Assume b)"
  using AssumeE dense_def by blast

lemma dense_ichoice:
  assumes "dense P1"
      and "dense P2"
    shows "dense (IChoice P1 P2)"
  using assms
  by (meson dense_def ichoiceE)

lemma dense_seq:
  assumes "dense P1"
      and "dense P2"
    shows "dense (P1;P2)"
  using assms
  by (metis append_Nil dense_def seqE) 

lemma sync_prog_seq:
  assumes "sync_prog_compat P1 chs P2" "sync_prog_compat Q1 chs Q2"
  shows "sync_prog_compat (P1;Q1) chs (P2;Q2)"
proof-
  {
    fix s1 s2 tr1 tr2 s1' s2' tr tr1' tr2'
    assume a0: "big_step (P1;Q1) s1 tr1 s1'" "big_step (P2;Q2) s2 tr2 s2'"
       and a1: "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
    then obtain s1m tr1m tr1m' s2m tr2m tr2m' where a2:
    "big_step P1 s1 tr1m s1m" "big_step Q1 s1m tr1m' s1'" "tr1 = tr1m @ tr1m'"
    "big_step P2 s2 tr2m s2m" "big_step Q2 s2m tr2m' s2'" "tr2 = tr2m @ tr2m'"
      by (meson seqE)
    with assms a1 obtain trm trm' tr' where a3: "combine_blocks_compat chs tr1m tr2m trm"
    "combine_blocks_compat chs tr1m' tr2m' trm'" "combine_blocks chs tr1' tr2' tr'"
    "tr = trm @ trm' @ tr'"
      by (smt (verit, best) append_assoc sync_prog_compat_def)
    then have "combine_blocks_compat chs (tr1m @ tr1m') (tr2m @ tr2m') (trm @ trm')"
      using combine_blocks_compat_append by auto
    with a2(3,6) a3(3,4) have "\<exists>tr' tr''. tr = tr' @ tr'' \<and> combine_blocks_compat chs tr1 tr2 tr' \<and>
    combine_blocks chs tr1' tr2' tr''"
      by (metis append_assoc)     
  }
  then show ?thesis
    by (simp add: sync_prog_compat_def)
qed

lemma sync_compat_out_in: 
  assumes "ch \<in> chs"
  shows "sync_prog_compat (Cm (ch[!]e)) chs (Cm (ch[?]var))"
proof-
  {
    fix s1 s2 tr1 tr2 s1' s2' tr tr1' tr2'
    assume "big_step (Cm (ch[!]e)) s1 tr1 s1'"
       and "big_step (Cm (ch[?]var)) s2 tr2 s2'" 
       and "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
    with assms obtain tr' where "tr1 = [OutBlock ch (e s1)]" "tr2 = [InBlock ch (e s1)]" 
    "combine_blocks chs tr1' tr2' tr'" "tr = IOBlock ch (e s1) # tr'"
      using sync_out_in by blast
    with assms have "\<exists>tr' tr''. tr = tr' @ tr'' \<and> combine_blocks_compat chs tr1 tr2 tr' 
              \<and> combine_blocks chs tr1' tr2' tr''"
      apply (rule_tac x = "[IOBlock ch (e s1)]" in exI, rule_tac x = tr' in exI, simp)
      using combine_blocks_compat_empty combine_blocks_compat_pair2 by blast
  }
  then show ?thesis
    by (simp add: sync_prog_compat_def)
qed

lemma sync_compat_outs_ins:
  assumes "ch \<in> chs"
      and "vars = map fst params" "exps = map snd params"
    shows "sync_prog_compat (outputs ch exps) chs (inputs ch vars)"
  using assms
  apply (induct params arbitrary: vars exps)
  apply (simp add: dense_skip sync_prog_compat_dense)
  by (simp add: sync_compat_out_in sync_prog_seq)

lemma sync_compat_in_out: 
  assumes "ch \<in> chs"
  shows "sync_prog_compat (Cm (ch[?]var)) chs (Cm (ch[!]e))"
proof-
  {
    fix s1 s2 tr1 tr2 s1' s2' tr tr1' tr2'
    assume "big_step (Cm (ch[?]var)) s1 tr1 s1'"
       and "big_step (Cm (ch[!]e)) s2 tr2 s2'" 
       and "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
    with assms obtain tr' where "tr1 = [InBlock ch (e s2)]" "tr2 = [OutBlock ch (e s2)]" 
    "combine_blocks chs tr1' tr2' tr'" "tr = IOBlock ch (e s2) # tr'"
      using sync_in_out by blast
    with assms have "\<exists>tr' tr''. tr = tr' @ tr'' \<and> combine_blocks_compat chs tr1 tr2 tr' 
              \<and> combine_blocks chs tr1' tr2' tr''"
      apply (rule_tac x = "[IOBlock ch (e s2)]" in exI, rule_tac x = tr' in exI, simp)
      using combine_blocks_compat_empty combine_blocks_compat_pair1 by blast
  }
  then show ?thesis
    by (simp add: sync_prog_compat_def)
qed

lemma sync_compat_ins_outs:
  assumes "ch \<in> chs"
      and "vars = map fst params" "exps = map snd params"
    shows "sync_prog_compat (inputs ch vars) chs (outputs ch exps)"
  using assms
  apply (induct params arbitrary: vars exps)
  apply (simp add: dense_skip sync_prog_compat_dense)
  by (simp add: sync_compat_in_out sync_prog_seq)

lemma sync_intout':
  assumes "Period > 0"
      and "ch \<in> chs"
      and "big_step (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) s1 tr1 s1'"
      and "big_step (Wait (\<lambda> s. Period); Cm (ch[?]var); C2) s2 tr2 s2'"
      and "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
      and "sync_prog C1 chs C2"
    shows "\<exists>p tr1m tr2m trm tr'. ODEsol ode p Period \<and> p 0 = s1 \<and> big_step C1 (p Period) tr1m s1' \<and>
    big_step C2 (s2(var := e (p Period))) tr2m s2' \<and> combine_blocks chs tr1m tr2m trm \<and>
    tr1 = WaitBlk Period (\<lambda>\<tau>. State (p \<tau>)) ({ch}, {}) # OutBlock ch (e (p Period)) # tr1m \<and> 
    tr2 = WaitBlk Period (\<lambda>_. State s2) ({}, {}) # [InBlock ch (e (p Period))] @ tr2m \<and>
    combine_blocks chs tr1' tr2' tr' \<and>  tr = (WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s2)) ({ch}, {})) 
    # IOBlock ch (e (p Period)) # trm @ tr'"
proof-
  from assms(4) obtain s2m tr2m tr2m' where a0: "big_step (Cm (ch[?]var)) s2 tr2m s2m" 
  "big_step C2 s2m tr2m' s2'" "tr2 = WaitBlk Period (\<lambda>_. State s2) ({}, {}) # tr2m @ tr2m'"
    by (metis (no_types, lifting) assms(1) big_step_wait_seq seqE)
  from assms(3) show ?thesis
  proof(cases rule: interruptE, simp)
    fix d p i cha ea p2 tr1m
    assume b0: "tr1 = OutBlock cha (ea s1) # tr1m"
       and b1: "i < length [(ch[!]e, C1)]"
       and b2: "[(ch[!]e, C1)] ! i = (cha[!]ea, p2)"
    then have "i = 0" by simp
    with b1 b2 have b3: "cha = ch" "ea = e" "p2 = C1"
      by auto
    with assms(2,5) b0 a0(3) show ?thesis
      using combine_blocks_pairE2[of chs Out ch "e s1" "tr1m @ tr1'" Period "(\<lambda>_. State s2)" "({}, {})" 
      "tr2m @ tr2m' @ tr2'" tr] by auto
  next
    fix d p i cha ea p2 tr1m
    assume c0: "tr1 = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice [(ch[!]e, C1)]) # OutBlock cha (ea (p d)) # tr1m"
       and c1: "0 < d" "ODEsol ode p d" " p 0 = s1"
       and c2: "i < length [(ch[!]e, C1)]"
       and c3: "[(ch[!]e, C1)] ! i = (cha[!]ea, p2)"
       and c4: " big_step p2 (p d) tr1m s1'"
    then have "i = 0" by simp
    with c3 c4 have c5: "cha = ch" "ea = e" "p2 = C1" 
      by auto
    from a0(1) show ?thesis
    proof(cases rule: receiveE, simp)
      fix v
      assume c00: "tr2m = [InBlock ch v]"
         and c01: "s2m = s2(var := v)"
      with assms(2,5) a0(3) c0 c5 obtain tr' where c02: "e (p d) = v" "d = Period" 
      "combine_blocks chs (tr1m @ tr1') (tr2m' @ tr2') tr'"
      "tr = WaitBlk d (\<lambda>t. ParState (State (p t)) (State s2)) (merge_rdy ({ch}, {}) ({}, {})) # IOBlock ch (e (p d)) # tr'"
        using combine_blocks_waitE5[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" Out ch "e (p d)" "tr1m @ tr1'"
        Period "\<lambda>_. State s2" "({}, {})" In ch v "tr2m' @ tr2'" tr] by auto
      from c02(3) a0(2) assms(6) c4 c5(3) obtain trm tr'' where "combine_blocks chs tr1m tr2m' trm" 
      "combine_blocks chs tr1' tr2' tr''" "tr' = trm @ tr''"
        using sync_prog_def by blast
      with a0(3) c00 c0 c1(2,3) c4 a0(2) c01 c02 c5 show ?thesis
        by (rule_tac x = p in exI, rule_tac x = tr1m in exI,rule_tac x = tr2m' in exI,
        rule_tac x = trm in exI, rule_tac x = tr'' in exI, simp)
    next
      fix d1 v
      assume c10: "tr2m = [WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}), InBlock ch v]"
         and c11: "s2m = s2(var := v)"
         and c12: "0 < d1"
      then show ?thesis
      proof(cases "Period > d")
        assume "Period > d"
        with assms(5) a0(3) c0 c1(1) c5 c10 obtain tr' where 
        "combine_blocks chs (OutBlock ch (e (p d)) # tr1m @ tr1')
        (WaitBlk (Period - d) (\<lambda>t. State s2) ({}, {}) # WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m' @ tr2') tr'"
        using combine_blocks_waitE3[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" "OutBlock ch (e (p d)) # tr1m @ tr1'"
          Period "\<lambda>_. State s2" "({}, {})" "WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m' @ tr2'" tr]
          by auto
        with assms(2) show ?thesis
          by (meson combine_blocks_pairE2)
      next
        assume "\<not> Period > d"
        then show ?thesis
        proof(cases "Period = d")
          assume "Period = d"
          with assms(5) a0(3) c0 c1(1) c5 c10 obtain tr' where 
          "combine_blocks chs (OutBlock ch (e (p d)) # tr1m @ tr1') (WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m' @ tr2') tr'"
            using combine_blocks_waitE2[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" "OutBlock ch (e (p d)) # tr1m @ tr1'"
            "\<lambda>_. State s2" "({}, {})" "WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m' @ tr2'" tr]
            by auto
          with assms(2) show ?thesis
            by (meson combine_blocks_pairE2)
        next
          assume "\<not> Period = d"
          then have "Period < d"
            using \<open>\<not> d < Period\<close> by force
          with assms(1,5) a0(3) c0 c1(1) c5 c10 obtain tr' where 
          "combine_blocks chs (WaitBlk (d - Period) (\<lambda>t. State (p (t + Period))) ({ch}, {}) # OutBlock ch (e (p d)) # tr1m @ tr1')
             (WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m' @ tr2') tr'"
            using combine_blocks_waitE4[of chs d "\<lambda>\<tau>. State (p \<tau>)" "({ch}, {})" "OutBlock ch (e (p d)) # tr1m @ tr1'"
          Period "\<lambda>_. State s2" "({}, {})" "WaitBlk d1 (\<lambda>_. State s2) ({}, {ch}) # InBlock ch v # tr2m' @ tr2'" tr]
            by auto
          then show ?thesis 
            using combine_blocks_waitE1[of chs "d - Period" "\<lambda>t. State (p (t + Period))" "({ch}, {})"
            "OutBlock ch (e (p d)) # tr1m @ tr1'" d1 "\<lambda>_. State s2" "({}, {ch})" "InBlock ch v # tr2m' @ tr2'" tr']
            by auto
        qed
      qed
    qed
  next
    fix i cha vara p2 v tr2
    assume "i < length [(ch[!]e, C1)]" "[(ch[!]e, C1)] ! i = (cha[?]vara, p2)"
    then show ?thesis by simp
  next
    fix d p i cha vara p2 v tr2
    assume "i < length [(ch[!]e, C1)]" "[(ch[!]e, C1)] ! i = (cha[?]vara, p2)"
    then show ?thesis by simp
  next
    assume "\<not> True"
    then show ?thesis by simp
  next
    fix d p
    assume "\<not> True"
    then show ?thesis by simp
  qed
qed

lemma sync_prog_intout:
  assumes "Period > 0"
      and "ch \<in> chs"
      and "sync_prog C1 chs C2"
    shows "sync_prog (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) chs (Wait (\<lambda> s. Period); Cm (ch[?]var); C2)"
proof-
  {
    fix s1 s2 tr1 tr2 s1' s2' tr tr1' tr2'
    assume "big_step (Interrupt ode (\<lambda>s. True) [(ch[!]e, C1)]) s1 tr1 s1'"
       and "big_step (Wait (\<lambda> s. Period); Cm (ch[?]var); C2) s2 tr2 s2'" 
       and "combine_blocks chs (tr1 @ tr1') (tr2 @ tr2') tr"
    with assms obtain p tr1m tr2m trm tr' where "big_step C1 (p Period) tr1m s1'"
    "big_step C2 (s2(var := e (p Period))) tr2m s2'" "combine_blocks chs tr1m tr2m trm"
    "combine_blocks chs tr1' tr2' tr'"
    "tr1 = WaitBlk Period (\<lambda>\<tau>. State (p \<tau>)) ({ch}, {}) # OutBlock ch (e (p Period)) # tr1m"
    "tr2 = WaitBlk Period (\<lambda>_. State s2) ({}, {}) # [InBlock ch (e (p Period))] @ tr2m"
    "tr = WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s2)) ({ch}, {}) # IOBlock ch (e (p Period)) # trm @ tr'"
      using sync_intout'[of Period ch chs ode e C1 s1 tr1 s1' var C2 s2 tr2 s2' tr1' tr2' tr]
      by auto
    with assms(1,2) have "\<exists>tr' tr''. tr = tr' @ tr'' \<and> combine_blocks chs tr1 tr2 tr' \<and> combine_blocks chs tr1' tr2' tr''"
      apply (rule_tac x = " WaitBlk Period (\<lambda>\<tau>. ParState (State (p \<tau>)) (State s2)) ({ch}, {}) # IOBlock ch (e (p Period)) # trm" in exI, 
      rule_tac x = tr' in exI, simp)
      using combine_blocks_pair2[of ch chs tr1m tr2m trm "e (p Period)"]
      combine_blocks_wait1[of chs "OutBlock ch (e (p Period)) # tr1m" "InBlock ch (e (p Period)) # tr2m"
      "IOBlock ch (e (p Period)) # trm" "({ch}, {})" "({}, {})" "\<lambda>\<tau>. ParState (State (p \<tau>)) (State s2)"
      "\<lambda>\<tau>. State (p \<tau>)" "\<lambda>_. State s2" "({ch}, {})" Period] by auto   
  }
  then show ?thesis
    by (simp add: sync_prog_def)
qed

lemma sync_prog_control: 
  assumes "ch\<^sub>p\<^sub>2\<^sub>c \<in> chs" "ch\<^sub>c\<^sub>2\<^sub>p \<in> chs"
      and "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "exps\<^sub>c = map snd params\<^sub>2"
      and "0 < Period"
    shows "sync_prog (Interrupt ode (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)])
    chs (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)"
  using assms
  by (simp add: sync_compat_ins_outs sync_compat_outs_ins sync_prog_implies sync_prog_intout sync_prog_seq)

text \<open>Compelete theorem for control loop\<close>
theorem sim_control_loop:
  assumes "ch\<^sub>p\<^sub>2\<^sub>c \<in> chs" "ch\<^sub>c\<^sub>2\<^sub>p \<in> chs"
      and "\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"
      and "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "exps\<^sub>c = map snd params\<^sub>2"
      and "0 < Period"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
      and "\<forall>s\<^sub>p s\<^sub>p' s\<^sub>c. (ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha> \<longrightarrow> 
          (assign_vars (update_vars s\<^sub>c s\<^sub>p ((var, e) # params\<^sub>1)) params\<^sub>2, s\<^sub>p') \<sqsubseteq> Id (P, s\<^sub>p')"
    shows "(Parallel (Single (Rep (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)]))) 
    chs (Single (Rep (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c))),
    ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
    (Rep (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P), s\<^sub>p)"
proof-
  from assms have a0: "\<forall>s\<^sub>c s\<^sub>a. (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<longrightarrow>
    (Parallel (Single (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)]))
    chs (Single (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)), s\<^sub>c) \<sqsubseteq>\<^sub>I \<alpha> 
    (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); P, s\<^sub>a)"
    by (rule sim_single_control_loop')
  from assms(1) have a1: "wait_sync (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)]) chs"
    by (simp add: wait_sync_intout)
  from assms(1,8) have a2: "wait_sync (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c) chs"
    by (simp add:  wait_sync_seq wait_sync_seq_assoc wait_sync_wait_in)
  from assms(1,2,4,5,6,7,8) have "sync_prog (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)])
    chs (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c)"
    using sync_prog_control by auto
  with assms(3) a0 a1 a2 show ?thesis
    apply (rule_tac sim_rep_sync, simp_all)
    by (metis fun_upd_triv)
qed

theorem sim_control_loop_correspond:
  assumes "ch\<^sub>p\<^sub>2\<^sub>c \<in> chs" "ch\<^sub>c\<^sub>2\<^sub>p \<in> chs"
      and "\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"
      and "vars\<^sub>c = map fst params\<^sub>1" "exps\<^sub>p = map snd params\<^sub>1"
      and "vars\<^sub>p = map fst params\<^sub>2" "funs\<^sub>c = map snd params\<^sub>2"
      and "exps\<^sub>c = map (\<lambda>f. apply_func f (vars2exps (var # vars\<^sub>c))) funs\<^sub>c"
      and "distinct (var # vars\<^sub>c)"
      and "\<forall>e' \<in> set (e # exps\<^sub>p). exp_independ e' T \<and> (\<forall>v \<in> set vars\<^sub>p. exp_independ e' v)"
      and "0 < Period"
      and "\<forall>x. x \<noteq> T \<longrightarrow> exp_independ (f x) T"
    shows "(Parallel (Single (Rep (Interrupt (ODE f) (\<lambda>s. True) [(ch\<^sub>p\<^sub>2\<^sub>c[!]e, outputs ch\<^sub>p\<^sub>2\<^sub>c exps\<^sub>p; inputs ch\<^sub>c\<^sub>2\<^sub>p vars\<^sub>p)]))) 
    chs (Single (Rep (Wait (\<lambda>s. Period); Cm (ch\<^sub>p\<^sub>2\<^sub>c[?]var); inputs ch\<^sub>p\<^sub>2\<^sub>c vars\<^sub>c; outputs ch\<^sub>c\<^sub>2\<^sub>p exps\<^sub>c))),
    ParState (State s\<^sub>p) (State s\<^sub>c)) \<sqsubseteq>\<^sub>I \<alpha> 
    (Rep (T ::= (\<lambda>_. 0); Cont (ODE (f(T := (\<lambda>_. 1)))) (\<lambda>s. s T < Period); 
     assign_vars_independ (construct_params params\<^sub>2 (e # exps\<^sub>p))), s\<^sub>p)"
proof-
  let ?params\<^sub>2 = "construct_params params\<^sub>2 (vars2exps (var # vars\<^sub>c))"
  from assms(6) have a0: "map fst ?params\<^sub>2 = vars\<^sub>p"
    by (simp add: construct_params_fst)
  from assms(7,8) have a1: "map snd ?params\<^sub>2 = exps\<^sub>c"
    by (simp add: construct_params_snd)
  {
    fix s\<^sub>p s\<^sub>p' s\<^sub>c
    assume "(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p') \<in> \<alpha>"
    with assms(3) obtain t where b0: "s\<^sub>p = s\<^sub>p'(T := t)"
      using prod.inject by fastforce
    with assms(10) have b1: "\<forall>e'\<in> set (e # exps\<^sub>p). e' s\<^sub>p = e' s\<^sub>p'"
      using exp_independ_def by fastforce
    from assms(10) have "\<forall>ea v. ea \<in> set (e # exps\<^sub>p) \<longrightarrow> v \<in> set vars\<^sub>p \<longrightarrow> exp_independ ea v"
      by blast
    with b1 assms(4,5,6,7,9,10) have "(assign_vars (update_vars s\<^sub>c s\<^sub>p ((var, e) # params\<^sub>1)) 
    (construct_params params\<^sub>2 (vars2exps (var # vars\<^sub>c))), s\<^sub>p') \<sqsubseteq> Id 
    (assign_vars_independ (construct_params params\<^sub>2 (e # exps\<^sub>p)), s\<^sub>p')"
    using sim_ins_outs_correspond[of "var # vars\<^sub>c" "(var, e) # params\<^sub>1" "e # exps\<^sub>p" vars\<^sub>p params\<^sub>2 funs\<^sub>c
    s\<^sub>p s\<^sub>p' s\<^sub>c] by auto
}
  with assms a0 a1 show ?thesis
    using sim_control_loop[of ch\<^sub>p\<^sub>2\<^sub>c chs ch\<^sub>c\<^sub>2\<^sub>p \<alpha> T vars\<^sub>c params\<^sub>1 exps\<^sub>p vars\<^sub>p ?params\<^sub>2 exps\<^sub>c Period f var
    e "assign_vars_independ (construct_params params\<^sub>2 (e # exps\<^sub>p))" s\<^sub>p s\<^sub>c]
    by auto
qed


text \<open>Some useful lemmas\<close>

(*
lemma output1_inputs1:
  assumes "s\<^sub>p X = s\<^sub>p' X"
  shows "(assign_vars (update_vars s\<^sub>c s\<^sub>p [(M, (\<lambda>s. s X))]) [(Y, (\<lambda>s. f (s M)))], s\<^sub>p') \<sqsubseteq> Id ( Y ::= (\<lambda>s. f (s X)), s\<^sub>p')"
  using assms
  apply simp

lemma output2_inputs1:
  assumes "s\<^sub>p X1 = s\<^sub>p' X1" "s\<^sub>p X2 = s\<^sub>p' X2" "M1 \<noteq> M2"
  shows "(assign_vars (update_vars s\<^sub>c s\<^sub>p [(M1, (\<lambda>s. s X1)), (M2, (\<lambda>s. s X2))]) [(Y, (\<lambda>s. f (s M1) (s M2)))], s\<^sub>p') 
  \<sqsubseteq> Id ( Y ::= (\<lambda>s. f (s X1) (s X2)), s\<^sub>p')"
  using assms
  sorry
*)


end                                                 