theory Par_Refine
  imports Language
begin

fun tblk_single :: "state rel \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where
  "tblk_single \<alpha> (WaitBlock d1 p1 r1) (WaitBlock d2 p2 r2) = (
     d1 = d2 \<and> r1 = r2 \<and> (\<forall>t\<in>{0..d1}.
       (\<exists>s1 s2. p1 t = State s1 \<and> p2 t = State s2 \<and> (s1, s2) \<in> \<alpha>)
     ))"
| "tblk_single _ b1 b2 = (b1 = b2)"

lemma restrict_iff: "(\<lambda>\<tau>\<in>{0..d}. p \<tau>) = (\<lambda>\<tau>\<in>{0..d}. p' \<tau>) \<longleftrightarrow> (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> p t = p' t)"
  by (metis atLeastAtMost_iff restrict_apply' restrict_ext)

lemma tblk_single_Id:
  assumes "wf_tblk_single blk1" "wf_tblk_single blk2"
      and "tblk_single Id blk1 blk2"
    shows "blk1 = blk2"
proof(cases blk1)
  case (CommBlock x11 x12 x13)
  with assms(3) show ?thesis by simp
next
  case (WaitBlock d p1 r)
  with assms(3) obtain p2 where "blk2 = WaitBlock d p2 r \<and> (\<forall>t\<in>{0..d}. p1 t = p2 t)"
    by (smt (verit) pair_in_Id_conv tblk_single.elims(2) trace_block.inject(2))
  with assms(1,2) show ?thesis
    using WaitBlock wf_tblk_single.simps(1) by force
qed

lemma tblk_single_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tblk_single \<alpha> blk1 blk2"
    shows "tblk_single \<beta> blk1 blk2"
  using assms
  apply (cases blk1, cases blk2, simp_all)
  apply (cases blk2, simp)
  apply auto
  by (meson atLeastAtMost_iff subsetD)

lemma tblk_single_refl:
  assumes "refl \<alpha>"
      and "wf_tblk_single blk"
  shows "tblk_single \<alpha> blk blk"
proof(cases blk)
  case (CommBlock c ch v)
  then show ?thesis by auto
next
  case (WaitBlock d p r)
  then show ?thesis
    using assms(1) assms(2) reflD by fastforce
qed

lemma tblk_single_compose:
  assumes "tblk_single \<alpha> blk1 blk2"
      and "tblk_single \<beta> blk2 blk3"
    shows "tblk_single (\<alpha> O \<beta>) blk1 blk3"
  using assms
  apply (cases blk1, cases blk2, cases blk3, simp_all)
  apply (cases blk2, cases blk3, simp_all)
  apply (cases blk3, simp)
  apply auto
  by (metis (no_types, opaque_lifting) atLeastAtMost_iff gstate.inject(1) 
      relcomp.relcompI)

lemma tblk_single_trans:
  assumes "trans \<alpha>"
      and "tblk_single \<alpha> blk1 blk2"
      and "tblk_single \<alpha> blk2 blk3"
    shows "tblk_single \<alpha> blk1 blk3"
  using assms
  by (meson tblk_single_compose tblk_single_weaken trans_O_subset)

definition tr_single :: "state rel \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "tr_single \<alpha> tr1 tr2 \<equiv> list_all2 (tblk_single \<alpha>) tr1 tr2"

lemma tr_single_Id:
  assumes "tr_single Id tr1 tr2"
      and "wf_tr_single tr1" "wf_tr_single tr2"
    shows "tr1 = tr2"
  using assms
proof(induct tr1 arbitrary: tr2)
  case Nil
  then show ?case
    by (simp add: tr_single_def)
next
  case (Cons blk1 tr1)
  then obtain blk2 tr2' where a0: "tr2 = blk2 # tr2'" "tr_single Id tr1 tr2'" "tblk_single Id blk1 blk2"
    by (metis list_all2_Cons1 tr_single_def)
  with Cons.hyps Cons.prems(2,3) have a1: "tr1 = tr2'"
    using  wf_tr_single_def by auto
  from a0(1,3) Cons.prems(2,3) have "blk1 = blk2"
    using tblk_single_Id wf_tr_single_def by auto
  with a1 a0(1) show ?case by simp
qed

lemma tr_single_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tr_single \<alpha> tr1 tr2"
    shows "tr_single \<beta> tr1 tr2"
  using assms
  by (metis list_all2_conv_all_nth tblk_single_weaken tr_single_def)

lemma tr_single_refl:
  assumes "refl \<alpha>"
      and "wf_tr_single tr"
    shows "tr_single \<alpha> tr tr"
  using assms
  by (metis in_set_conv_decomp list.rel_refl_strong list_all_append list_all_simps(1) 
      tblk_single_refl tr_single_def wf_tr_single_def)

lemma tr_single_compose:
  assumes "trans \<alpha>"
      and "tr_single \<alpha> tr1 tr2"
      and "tr_single \<beta> tr2 tr3"
    shows "tr_single (\<alpha> O \<beta>) tr1 tr3"
  using assms
  by (smt (verit, best) list_all2_conv_all_nth tblk_single_compose tr_single_def)

lemma tr_single_trans:
  assumes "trans \<alpha>"
      and "tr_single \<alpha> tr1 tr2"
      and "tr_single \<alpha> tr2 tr3"
    shows "tr_single \<alpha> tr1 tr3"
  using assms
  by (meson tr_single_compose tr_single_weaken trans_O_subset)
  
definition hybrid_sim_single :: "proc \<Rightarrow> state \<Rightarrow> (state rel) \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" 
  ("'(_, _') \<sqsubseteq> _ '(_, _')") where
  "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a) = ((s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and> (\<forall>s\<^sub>c' tr\<^sub>c. big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longrightarrow> 
   (\<exists>s\<^sub>a' tr\<^sub>a. big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>)))"

definition hybrid_equiv_single :: "proc \<Rightarrow> state \<Rightarrow> (state rel) \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool"
  ("'(_, _') \<sim> _ '(_, _')") where
  "(P\<^sub>c, s\<^sub>c) \<sim> \<alpha> (P\<^sub>a, s\<^sub>a) = ((P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a) \<and> (P\<^sub>a, s\<^sub>a) \<sqsubseteq> \<alpha> (P\<^sub>c, s\<^sub>c))"
 
theorem hybrid_sim_single_Id:
  "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> Id (P\<^sub>a, s\<^sub>a) \<longleftrightarrow> (s\<^sub>c = s\<^sub>a \<and> (\<forall>s\<^sub>c' tr\<^sub>c. big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longrightarrow> big_step P\<^sub>a s\<^sub>a tr\<^sub>c s\<^sub>c'))"
  by (metis (no_types, lifting) hybrid_sim_single_def pair_in_Id_conv proc_wf_tr_single refl_Id tr_single_Id tr_single_refl)

theorem hybrid_equiv_single_Id:
  "(P\<^sub>c, s\<^sub>c) \<sim> Id (P\<^sub>a, s\<^sub>a)  \<longleftrightarrow> (s\<^sub>c = s\<^sub>a \<and> (\<forall>s\<^sub>c' tr\<^sub>c. big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longleftrightarrow> big_step P\<^sub>a s\<^sub>a tr\<^sub>c s\<^sub>c'))"
  by (meson hybrid_equiv_single_def hybrid_sim_single_Id)  

theorem equiv_Id_single_refl:
  assumes "(P\<^sub>c, s\<^sub>c) \<sim> Id (P\<^sub>a, s\<^sub>a)"
  shows "(P\<^sub>a, s\<^sub>a) \<sim> Id (P\<^sub>c, s\<^sub>c)"
  using assms hybrid_equiv_single_Id by auto

lemma big_step_skipl: "big_step P s tr s' \<longleftrightarrow> big_step (Skip; P) s tr s'"
  by (metis append_self_conv2 seqB seqE skipB skipE)

lemma big_step_skipr: "big_step P s tr s' \<longleftrightarrow> big_step (P; Skip) s tr s'"
  by (metis append_Nil2 seqB seqE skipB skipE)

theorem equiv_Id_single_skipl: "(P, s) \<sim> Id (Skip; P, s)"
  using big_step_skipl hybrid_equiv_single_Id by force

theorem equiv_Id_single_skipr: "(P, s) \<sim> Id (P; Skip, s)"
  using big_step_skipr hybrid_equiv_single_Id by presburger

lemma big_step_seq_assoc: "big_step ((C1; C2); C3) s tr s' \<longleftrightarrow> big_step (C1; (C2; C3)) s tr s'"
  by (smt (verit, ccfv_SIG) append.assoc seqB seqE)

theorem equiv_Id_single_seq: "((C1; C2); C3, s) \<sim> Id (C1; (C2; C3), s)"
  by (simp add: big_step_seq_assoc hybrid_equiv_single_Id)

definition reachable :: "proc \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "reachable C s s' = (\<exists>tr. big_step C s tr s')"

definition finish :: "proc \<Rightarrow> state \<Rightarrow> bool" where
  "finish C s = (\<exists>s'. reachable C s s')"

theorem sim_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
    shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<beta> (P\<^sub>a, s\<^sub>a)"
  using assms hybrid_sim_single_def
  by (meson subsetD tr_single_weaken)

theorem sim_refl: 
  assumes "refl \<alpha>"
  shows "(C, s) \<sqsubseteq> \<alpha> (C, s)"
  using assms hybrid_sim_single_def
  by (meson proc_wf_tr_single reflD tr_single_refl)

theorem sim_compose:
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>m, s\<^sub>m)"
      and "(P\<^sub>m, s\<^sub>m) \<sqsubseteq> \<beta> (P\<^sub>a, s\<^sub>a)"
    shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> (\<alpha> O \<beta>) (P\<^sub>a, s\<^sub>a)"
  using assms hybrid_sim_single_def
  by (smt (verit) list_all2_trans relcomp.simps tblk_single_compose tr_single_def)

theorem sim_trans:
  assumes "trans \<alpha>"
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>m, s\<^sub>m)"
      and "(P\<^sub>m, s\<^sub>m) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
    shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
  using assms hybrid_sim_single_def
  by (meson sim_compose sim_weaken trans_O_subset)

theorem sim_havoc: 
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      and "(s\<^sub>c (x := e s\<^sub>c), s\<^sub>a (y := v)) \<in> \<alpha>"
    shows "((x ::= e), s\<^sub>c) \<sqsubseteq> \<alpha> ((y ::= *), s\<^sub>a)"
  using assms
  apply (simp add: hybrid_sim_single_def, clarify)
  apply (rule_tac x = "s\<^sub>a (y := v)" in exI)
  apply (rule_tac x = tr\<^sub>c in exI, simp add: tr_single_def)
  using HavocB assignE by blast

corollary sim_havoc_Id: "((x ::= e), s) \<sqsubseteq> Id ((x ::= *), s)"
  by (rule sim_havoc, simp_all)

theorem sim_assign_Id: 
  assumes "e s = v"
  shows "(x ::= (\<lambda>_. v), s) \<sqsubseteq> Id (x ::= e, s)"
  by (metis assignB assignE assms hybrid_sim_single_Id)

theorem sim_ichoice_l:
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      and "(P\<^sub>c\<^sub>1, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)" "(P\<^sub>c\<^sub>2, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
  shows "(IChoice P\<^sub>c\<^sub>1 P\<^sub>c\<^sub>2, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
  using assms
  apply (simp add: hybrid_sim_single_def, clarify)
  by (metis ichoiceE)

corollary sim_ichoice_l_Id:
  assumes "(P\<^sub>c\<^sub>1, s) \<sqsubseteq> Id (P\<^sub>a, s)" 
      and "(P\<^sub>c\<^sub>2, s) \<sqsubseteq> Id (P\<^sub>a, s)"
    shows "(IChoice P\<^sub>c\<^sub>1 P\<^sub>c\<^sub>2, s) \<sqsubseteq> Id (P\<^sub>a, s)"
  by (simp add: assms sim_ichoice_l)

theorem sim_ichoice_r:
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a\<^sub>1, s\<^sub>a) \<or> (P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a\<^sub>2, s\<^sub>a)"
  shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (IChoice P\<^sub>a\<^sub>1 P\<^sub>a\<^sub>2, s\<^sub>a)"
  using assms
  apply (simp add: hybrid_sim_single_def)
  using IChoiceB1 IChoiceB2 by blast

corollary sim_ichoice_r_Id:
  assumes "(P\<^sub>c, s) \<sqsubseteq> Id (P\<^sub>a\<^sub>1, s) \<or> (P\<^sub>c, s) \<sqsubseteq> Id (P\<^sub>a\<^sub>2, s)"
  shows "(P\<^sub>c, s) \<sqsubseteq> Id (IChoice P\<^sub>a\<^sub>1 P\<^sub>a\<^sub>2, s)"
  using assms sim_ichoice_r by force

theorem sim_assume:
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      and "b\<^sub>c s\<^sub>c \<longrightarrow> b\<^sub>a s\<^sub>a"
  shows "(Assume b\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (Assume b\<^sub>a, s\<^sub>a)"
  using assms
  apply (simp add: hybrid_sim_single_def, clarify)
  by (metis AssumeB AssumeE list_all2_Nil2 tr_single_def)
  
corollary sim_assume_Id:
  assumes "b1 s \<longrightarrow> b2 s"
  shows "(Assume b1, s) \<sqsubseteq> Id (Assume b2, s)"
  by (simp add: assms sim_assume)

theorem sim_seq:
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      and "(P\<^sub>c\<^sub>1, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a\<^sub>1, s\<^sub>a)"
      and "\<forall>s\<^sub>c' s\<^sub>a'. reachable P\<^sub>c\<^sub>1 s\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> \<alpha> \<longrightarrow> (P\<^sub>c\<^sub>2, s\<^sub>c') \<sqsubseteq> \<alpha> (P\<^sub>a\<^sub>2, s\<^sub>a')"
  shows "(P\<^sub>c\<^sub>1;P\<^sub>c\<^sub>2, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a\<^sub>1; P\<^sub>a\<^sub>2, s\<^sub>a)"
proof-
    {
      fix s\<^sub>c' tr\<^sub>c
      assume "big_step (P\<^sub>c\<^sub>1;P\<^sub>c\<^sub>2) s\<^sub>c tr\<^sub>c s\<^sub>c'"
      then obtain s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>2 where a0: "big_step P\<^sub>c\<^sub>1 s\<^sub>c tr\<^sub>c\<^sub>1 s\<^sub>c\<^sub>m" "big_step P\<^sub>c\<^sub>2 s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>2 s\<^sub>c'" "tr\<^sub>c = tr\<^sub>c\<^sub>1 @ tr\<^sub>c\<^sub>2"
        by (meson seqE)
      from a0(1) assms(2) obtain s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>1 where a1: "big_step P\<^sub>a\<^sub>1 s\<^sub>a tr\<^sub>a\<^sub>1 s\<^sub>a\<^sub>m" 
      "tr_single \<alpha> tr\<^sub>c\<^sub>1 tr\<^sub>a\<^sub>1" "(s\<^sub>c\<^sub>m, s\<^sub>a\<^sub>m) \<in> \<alpha>"
        by (metis hybrid_sim_single_def)      
      from assms(3) a0(1) a0(2) a1(3) obtain s\<^sub>a' tr\<^sub>a\<^sub>2 where "big_step P\<^sub>a\<^sub>2 s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>2 s\<^sub>a'"
      "tr_single \<alpha> tr\<^sub>c\<^sub>2 tr\<^sub>a\<^sub>2" "(s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis hybrid_sim_single_def reachable_def)
      with a0(3) a1(1) a1(2) have "\<exists>tr\<^sub>a s\<^sub>a'. big_step (P\<^sub>a\<^sub>1; P\<^sub>a\<^sub>2) s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis list_all2_appendI seqB tr_single_def)
    }
    with assms(1) show ?thesis
      by (metis hybrid_sim_single_def)          
  qed

corollary sim_seq_Id:
  assumes "(P\<^sub>c\<^sub>1, s) \<sqsubseteq> Id (P\<^sub>a\<^sub>1, s)"
      and "\<forall>s'. reachable P\<^sub>c\<^sub>1 s s' \<longrightarrow> (P\<^sub>c\<^sub>2, s') \<sqsubseteq> Id (P\<^sub>a\<^sub>2, s')"
    shows "(P\<^sub>c\<^sub>1;P\<^sub>c\<^sub>2, s) \<sqsubseteq> Id (P\<^sub>a\<^sub>1; P\<^sub>a\<^sub>2, s)"
  by (rule sim_seq, simp_all add: assms)

theorem sim_loop_l_Id:
  assumes "\<forall>s'. reachable (Rep P\<^sub>c\<^sub>1) s s' \<longrightarrow> (P\<^sub>c\<^sub>1; P\<^sub>a, s') \<sqsubseteq> Id (P\<^sub>a, s')"
      and "\<forall>s'. reachable (Rep P\<^sub>c\<^sub>1) s s' \<longrightarrow> (P\<^sub>c\<^sub>2, s') \<sqsubseteq> Id (P\<^sub>a, s')"
    shows "(Rep P\<^sub>c\<^sub>1; P\<^sub>c\<^sub>2, s) \<sqsubseteq> Id (P\<^sub>a, s)"
proof-
  {
    fix s' tr
    assume "big_step (Rep P\<^sub>c\<^sub>1; P\<^sub>c\<^sub>2) s tr s'"
    then obtain sm tr1 tr2 where a0: "big_step (Rep P\<^sub>c\<^sub>1) s tr1 sm" "big_step P\<^sub>c\<^sub>2 sm tr2 s'" "tr = tr1 @ tr2"
      by (meson seqE)
    with assms(2) have a1: "big_step P\<^sub>a sm tr2 s'"
      using hybrid_sim_single_Id reachable_def by auto
    from a0(1) obtain n where "iterate_bigstep n (s, []) P\<^sub>c\<^sub>1 (sm, tr1)"
      by (metis append_Nil big_step_while)
    with a0(3) a1 have "big_step P\<^sub>a s tr s'"
    proof(induct n arbitrary: sm tr1 tr2)
      case 0
      with assms(2) show ?case
        by simp
    next
      case (Suc n)
      from Suc.prems(3) obtain sm1 trm1 trm2 where b0: "iterate_bigstep n (s, []) P\<^sub>c\<^sub>1 (sm1, trm1)"
      "big_step P\<^sub>c\<^sub>1 sm1 trm2 sm" "tr1 = trm1 @ trm2"
        by auto
      with Suc.prems(2) have "big_step (P\<^sub>c\<^sub>1; P\<^sub>a) sm1 (trm2 @ tr2) s'"
        using seqB by auto
      with b0(1) assms(1) have "big_step P\<^sub>a sm1 (trm2 @ tr2) s'"
        by (metis append_Nil big_step_while hybrid_sim_single_Id reachable_def)
      with b0(1,3) Suc.prems(1) Suc.hyps[of trm1 "trm2 @ tr2" sm1] show ?case by auto
    qed
  }
  then show ?thesis
    using hybrid_sim_single_Id by force
qed

theorem sim_loop_r_Id:
  assumes "(P\<^sub>c\<^sub>2, s) \<sqsubseteq> Id (P\<^sub>a, s)"
      and "(P\<^sub>a; P\<^sub>c\<^sub>1, s) \<sqsubseteq> Id (P\<^sub>a, s)"
    shows "(P\<^sub>c\<^sub>2; Rep P\<^sub>c\<^sub>1, s) \<sqsubseteq> Id (P\<^sub>a, s)"
proof-
  {
    fix s' tr
    assume "big_step (P\<^sub>c\<^sub>2; Rep P\<^sub>c\<^sub>1) s tr s'"
    then obtain sm tr1 tr2 where a0: "big_step P\<^sub>c\<^sub>2 s tr1 sm" "big_step (Rep P\<^sub>c\<^sub>1) sm tr2 s'" "tr = tr1 @ tr2"
      by (meson seqE)
    with assms(1) have a1: "big_step P\<^sub>a s tr1 sm"
      by (simp add: hybrid_sim_single_Id)
    from a0(2,3) obtain n where "iterate_bigstep n (sm, tr1) P\<^sub>c\<^sub>1 (s', tr)"
      by (metis big_step_while)
    with  a1 have "big_step P\<^sub>a s tr s'"
    proof(induct n arbitrary: sm tr1 tr2)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      from Suc.prems(2) obtain sm1 trm1 where b0: "big_step P\<^sub>c\<^sub>1 sm trm1 sm1" 
      "iterate_bigstep n (sm1, tr1 @ trm1) P\<^sub>c\<^sub>1 (s', tr)"
        using iterate_bigstep_converse by blast
      with Suc.prems(1) have "big_step (P\<^sub>a; P\<^sub>c\<^sub>1) s (tr1 @ trm1) sm1"
        by (simp add: seqB)
      with assms(2) have "big_step P\<^sub>a s (tr1 @ trm1) sm1"
        by (simp add: hybrid_sim_single_Id)
      with b0(2) Suc.hyps[of "tr1 @ trm1" sm1] show ?case by auto
    qed
  }
  then show ?thesis
    using hybrid_sim_single_Id by force
qed

theorem sim_unloop:
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      and "\<forall>s\<^sub>c' s\<^sub>a'. reachable (Rep P\<^sub>c) s\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> \<alpha> \<longrightarrow> (P\<^sub>c, s\<^sub>c') \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a')"
    shows "(Rep P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (Rep P\<^sub>a, s\<^sub>a)"
proof-
  {
    fix s\<^sub>c' tr\<^sub>c
    assume "big_step (Rep P\<^sub>c) s\<^sub>c tr\<^sub>c s\<^sub>c'"
    then obtain n where "iterate_bigstep n (s\<^sub>c, []) P\<^sub>c (s\<^sub>c', tr\<^sub>c)"
      by (metis append_Nil big_step_while)
    then have "\<exists>s\<^sub>a' tr\<^sub>a. big_step (Rep P\<^sub>a) s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
    proof(induct n arbitrary: s\<^sub>c' tr\<^sub>c)
      case 0
      then have "s\<^sub>c = s\<^sub>c' \<and> tr\<^sub>c = []"
        by simp
      with assms(1) show ?case
        by (rule_tac x = s\<^sub>a in exI, rule_tac x = "[]" in exI, simp add: RepetitionB1 tr_single_def) 
    next
      case (Suc n)
      from Suc.prems obtain s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>2 where b0: "iterate_bigstep n (s\<^sub>c, []) P\<^sub>c (s\<^sub>c\<^sub>m, tr\<^sub>c\<^sub>1)"
      "big_step P\<^sub>c s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>2 s\<^sub>c'" "tr\<^sub>c = tr\<^sub>c\<^sub>1 @ tr\<^sub>c\<^sub>2"
        by auto
      with Suc.hyps[of s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>1] obtain s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>1 where b1: "big_step (Rep P\<^sub>a) s\<^sub>a tr\<^sub>a\<^sub>1 s\<^sub>a\<^sub>m" 
           "tr_single \<alpha> tr\<^sub>c\<^sub>1 tr\<^sub>a\<^sub>1" "(s\<^sub>c\<^sub>m, s\<^sub>a\<^sub>m) \<in> \<alpha>"
        by auto
      from b0(1) b0(2) assms(2) b1(3) obtain tr\<^sub>a\<^sub>2 s\<^sub>a' where b2: "big_step P\<^sub>a s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>2 s\<^sub>a'" 
           "tr_single \<alpha> tr\<^sub>c\<^sub>2 tr\<^sub>a\<^sub>2" "(s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis big_step_while hybrid_sim_single_def reachable_def self_append_conv2)
      with b0(3) b1 show ?case
        by (rule_tac x = s\<^sub>a' in exI, rule_tac x = "tr\<^sub>a\<^sub>1 @ tr\<^sub>a\<^sub>2" in exI, simp add: 
               big_step_RepetitionB3 tr_single_def list_all2_appendI)
    qed
  }
  with assms(1) show ?thesis
    using hybrid_sim_single_def by force
qed

theorem sim_unloop_Id:
  assumes "\<forall>s'. reachable (Rep P\<^sub>c) s s' \<longrightarrow> (P\<^sub>c, s') \<sqsubseteq> Id (P\<^sub>a, s')"
  shows "(Rep P\<^sub>c, s) \<sqsubseteq> Id (Rep P\<^sub>a, s)"
  by (rule sim_unloop, simp_all add: assms)

thm hybrid_sim_single_Id

theorem sim_interrupt_Id:
  assumes "map fst cs = map fst cs'" 
     and "\<forall>i < length cs. (\<forall>s. (snd (cs ! i), s) \<sqsubseteq> Id (snd (cs' ! i), s))"
   shows "(Interrupt ode b cs, s) \<sqsubseteq> Id (Interrupt ode b cs', s)"
proof-
  from assms(1) have a: "length cs = length cs'" 
    by (metis length_map)
  from assms(1) have b: "rdy_of_echoice cs = rdy_of_echoice cs'"
    using rdy_of_choice_fst by blast
  {
    fix s' tr
    assume "big_step (Interrupt ode b cs) s tr s'"
    then have "big_step (Interrupt ode b cs') s tr s'"
    proof(cases rule: interruptE, simp)
      fix i ch e p2 tr2
      assume a0: "tr = OutBlock ch (e s) # tr2" 
         and a1: "i < length cs" 
         and a2:"cs ! i = (ch[!]e, p2)" 
         and a3:"big_step p2 s tr2 s'"
      with assms(1) have "fst (cs' ! i) = ch[!]e"
        by (metis fstI length_map nth_map)
      then have a4: "(cs' ! i) = (ch[!]e, snd (cs' ! i))"
        by (simp add: split_pairs2)
      from assms(2) a1 a2 a3 have "big_step (snd (cs' ! i)) s tr2 s'"
        using hybrid_sim_single_Id by auto
      with a0 a1 a4 a show ?thesis
        by (metis InterruptSendB1 prod.exhaust_sel)
    next
      fix d p i ch e p2 tr2
      assume a0: "tr = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2"
         and a1: "0 < d" " ODEsol ode p d" "p 0 = s" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" 
         and a2: "i < length cs"
         and a3: "cs ! i = (ch[!]e, p2)" 
         and a4: "big_step p2 (p d) tr2 s'"
      with assms(1) have "fst (cs' ! i) = ch[!]e"
        by (metis fstI length_map nth_map)
      then have a5: "(cs' ! i) = (ch[!]e, snd (cs' ! i))"
        by (simp add: split_pairs2)
      from assms(2) a2 a3 a4 have "big_step (snd (cs' ! i)) (p d) tr2 s'"
        using hybrid_sim_single_Id by auto
      with a0 a1 a2 a5 a b show ?thesis
        using InterruptSendB2[of d ode p s b i cs' ch e "snd (cs' ! i)" "rdy_of_echoice cs" tr2 s']
        by auto
    next
      fix i ch var p2 v tr2
      assume c0: "tr = InBlock ch v # tr2" 
         and c1: "i < length cs" 
         and c2: "cs ! i = (ch[?]var, p2)" 
         and c3: "big_step p2 (s(var := v)) tr2 s'"
      with assms(1) have "fst (cs' ! i) = ch[?]var"
        by (metis fstI length_map nth_map)
      then have c4: "(cs' ! i) = (ch[?]var, snd (cs' ! i))"
        by (simp add: split_pairs2)
      from assms(2) c1 c2 c3 have "big_step (snd (cs' ! i)) (s(var := v)) tr2 s'"
        using hybrid_sim_single_Id by auto
      with c0 c1 c4 a show ?thesis
        by (simp add: InterruptReceiveB1)
    next
      fix d p i ch var p2 v tr2
      assume d0: "tr = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2"
         and d1: "0 < d" "ODEsol ode p d" "p 0 = s" " \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
         and d2: "i < length cs" 
         and d3: "cs ! i = (ch[?]var, p2)" 
         and d4: "big_step p2 ((p d)(var := v)) tr2 s'"
      with assms(1) have "fst (cs' ! i) = ch[?]var"
        by (metis fstI length_map nth_map)
      then have d5: "(cs' ! i) = (ch[?]var, snd (cs' ! i))"
        by (simp add: split_pairs2)
      from assms(2) d2 d3 d4 have "big_step (snd (cs' ! i)) ((p d)(var := v)) tr2 s'"
        using hybrid_sim_single_Id by auto
      with d0 d1 d2 d5 a b show ?thesis
        using InterruptReceiveB2[of d ode p s b i cs' ch var "snd (cs' ! i)" "rdy_of_echoice cs" v tr2 s']
        by auto
    next
      assume "tr = []" "s' = s" "\<not> b s"
      then show ?thesis
        by (simp add: InterruptB1)
    next
      fix d p
      assume "tr = [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)]" "0 < d" "ODEsol ode p d"
      "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" " \<not> b s'" "p 0 = s" "p d = s'"
      then show ?thesis
        by (simp add: InterruptB2 b)
    qed
  }
  then show ?thesis
    by (simp add: hybrid_sim_single_Id)
qed

text \<open>ODE with invariant\<close>
type_synonym tassn = "trace \<Rightarrow> bool"

inductive ode_inv_assn :: "(state \<Rightarrow> bool) \<Rightarrow> tassn" where
  "\<forall>t\<in>{0..d::real}. f (p t) \<Longrightarrow> ode_inv_assn f [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"

inductive_cases ode_inv_assn_elim: "ode_inv_assn f tr"

lemma ode_inv_imp:
  assumes "ode_inv_assn f [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
  shows "\<forall>t\<in>{0..d}. f (p t)"
  by (metis (no_types, lifting) WaitBlk_cong WaitBlk_cong2 assms atLeastAtMost_iff gstate.inject(1) list.inject ode_inv_assn.cases)

lemma sim_cont_DC:
  assumes "\<forall>s' tr. big_step (Cont ode b1) s tr s' \<longrightarrow> tr \<noteq> [] \<longrightarrow> ode_inv_assn b2 tr"
  shows "(Cont ode b1, s) \<sqsubseteq> Id (Cont ode (\<lambda>s. b1 s \<and> b2 s), s)"
proof-
  {
    fix s' tr
    assume a0: "big_step (Cont ode b1) s tr s'"
    then have "big_step (Cont ode (\<lambda>s. b1 s \<and> b2 s)) s tr s'"
    proof (rule contE)
      assume "tr = []" "s' = s" "\<not> b1 s"
      then show ?thesis
        using ContB1 by auto
    next
      fix d p
      assume a1: "tr = [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]" "s' = p d" "0 < d"
      "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b1 (p t)" "\<not> b1 (p d)" "p 0 = s"
      from a0 a1(1) assms have "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b2 (p t)" 
        using ode_inv_imp[of b2 d p] by auto
      with a1 show ?thesis
        using ContB2[of d ode p "\<lambda>s. b1 s \<and> b2 s" s] by auto 
    qed
  }
  then show ?thesis
    by (meson hybrid_sim_single_def pair_in_Id_conv proc_wf_tr_single refl_Id tr_single_refl)
qed

fun tblk_par :: "gstate rel \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where
  "tblk_par \<alpha> (WaitBlock d1 p1 r1) (WaitBlock d2 p2 r2) =
     (d1 = d2 \<and> r1 = r2 \<and> (\<forall>t\<in>{0..d1}. (p1 t, p2 t) \<in> \<alpha>))"
| "tblk_par _ b1 b2 = (b1 = b2)"

lemma tblk_par_waitblk:
  assumes "tblk_par \<alpha> (WaitBlock d p r) blk"
      and "wf_tblk_par blk"
    shows "\<exists>p'. blk = WaitBlk d p' r \<and> (\<forall>t\<in>{0..d}. (p t, p' t) \<in> \<alpha>)"
proof-
  from assms(1) obtain p' where "blk = WaitBlock d p' r" "\<forall>t\<in>{0..d}. (p t, p' t) \<in> \<alpha>"
    using tblk_par.elims(2) by force
  with assms(2) show ?thesis
    using WaitBlk_def by auto
qed

lemma tblk_par_waitblk':
  assumes "tblk_par \<alpha> (WaitBlk d p r) blk"
      and "wf_tblk_par blk"
    shows "\<exists>p'. blk = WaitBlk d p' r \<and> (\<forall>t\<in>{0..d}. (p t, p' t) \<in> \<alpha>)"
  by (smt (verit) WaitBlk_def assms(1,2) restrict_def tblk_par_waitblk)

lemma tblk_par_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tblk_par \<alpha> blk1 blk2"
    shows "tblk_par \<beta> blk1 blk2"
  using assms
  apply (cases blk1, cases blk2, simp_all)
  apply (cases blk2, simp)
  by auto

lemma tblk_par_refl:
  assumes "refl \<alpha>"
  shows "tblk_par \<alpha> blk blk"
proof(cases blk)
  case (CommBlock c ch v)
  then show ?thesis by auto
next
  case (WaitBlock d p r)
  then show ?thesis
    using assms(1) reflD by fastforce
qed

lemma tblk_par_compose:
  assumes "tblk_par \<alpha> blk1 blk2"
      and "tblk_par \<beta> blk2 blk3"
    shows "tblk_par (\<alpha> O \<beta>) blk1 blk3"
  using assms
  apply (cases blk1, cases blk2, cases blk3, simp_all)
  apply (cases blk2, cases blk3, simp_all)
  apply (cases blk3, simp)
  by auto

lemma tblk_par_trans:
  assumes "trans \<alpha>"
      and "tblk_par \<alpha> blk1 blk2"
      and "tblk_par \<alpha> blk2 blk3"
    shows "tblk_par \<alpha> blk1 blk3"
  using assms
  by (meson tblk_par_compose tblk_par_weaken trans_O_subset)

definition tr_par :: "gstate rel \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "tr_par \<alpha> tr1 tr2 = list_all2 (tblk_par \<alpha>) tr1 tr2"

lemma tr_par_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tr_par \<alpha> tr1 tr2"
    shows "tr_par \<beta> tr1 tr2"
  using assms
  by (simp add: list_all2_conv_all_nth tblk_par_weaken tr_par_def)

lemma tr_par_refl:
  assumes "refl \<alpha>"
    shows "tr_par \<alpha> tr tr"
  using assms
  by (simp add: list_all2_conv_all_nth tblk_par_refl tr_par_def)

lemma tr_par_compose:
  assumes "trans \<alpha>"
      and "tr_par \<alpha> tr1 tr2"
      and "tr_par \<beta> tr2 tr3"
    shows "tr_par (\<alpha> O \<beta>) tr1 tr3"
  using assms
  by (smt (verit, best) list_all2_trans tblk_par_compose tr_par_def)

lemma tr_par_trans:
  assumes "trans \<alpha>"
      and "tr_par \<alpha> tr1 tr2"
      and "tr_par \<alpha> tr2 tr3"
    shows "tr_par \<alpha> tr1 tr3"
  using assms
  using tr_par_compose tr_par_weaken trans_O_subset by blast
  
definition hybrid_sim_par :: "pproc \<Rightarrow> gstate \<Rightarrow> (gstate rel) \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> bool" 
  ("'(_, _') \<sqsubseteq>\<^sub>p _ '(_, _')") where
  "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>p \<alpha> (P\<^sub>a, s\<^sub>a) = (\<forall>s\<^sub>c' tr\<^sub>c. par_big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>
   (\<exists>s\<^sub>a' tr\<^sub>a. par_big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_par \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>))"

definition lift_rel_single :: "(state rel) \<Rightarrow> (gstate rel)" ( "\<Up>\<^sub>s _" [80] 80) where 
  "\<Up>\<^sub>s \<alpha> = {(State s1, State s2) |s1 s2. (s1, s2) \<in> \<alpha>}"

definition lift_rel_par :: "(gstate rel) \<Rightarrow> (gstate rel) \<Rightarrow> (gstate rel)" (infixr "\<uplus>\<^sub>p" 80) where 
  "\<alpha> \<uplus>\<^sub>p \<beta> = {(ParState s1 s2, ParState s1' s2') |s1 s2 s1' s2'. (s1, s1') \<in> \<alpha> \<and> (s2, s2') \<in> \<beta>}"

lemma tblk_lift_rel_single:
  assumes "tblk_single \<alpha> tr1 tr2"
    shows "tblk_par (\<Up>\<^sub>s \<alpha>) tr1 tr2"
  using assms
  apply (cases tr1, cases tr2, simp_all)
  by (cases tr2, simp_all add: lift_rel_single_def)

lemma tr_lift_rel_single:
  assumes "tr_single \<alpha> tr1 tr2"
  shows "tr_par (\<Up>\<^sub>s \<alpha>) tr1 tr2"
  by (metis assms list_all2_mono tblk_lift_rel_single tr_par_def tr_single_def)

lemma tr_par_cons_waitblk:
  assumes "tr_par \<alpha> ((WaitBlk d p rdy) # blks) tr'"
      and "wf_tr_par tr'"
    shows "\<exists>p' blks'. tr' = (WaitBlk d p' rdy) # blks' \<and> (\<forall>t\<in>{0..d}. (p t, p' t) \<in> \<alpha>) \<and> tr_par \<alpha> blks blks'"
proof-
  from assms(1) obtain wait blks' where a0: "tr' = wait # blks'" "tr_par \<alpha> blks blks'"
  "tblk_par \<alpha> (WaitBlk d p rdy) wait"
    by (metis list_all2_Cons1 tr_par_def)
  with assms(2) have "wf_tblk_par wait"
    using wf_tr_par_cons by blast
  with a0(3) obtain p' where "wait = WaitBlk d p' rdy" "\<forall>t\<in>{0..d}. (p t, p' t) \<in> \<alpha>"
    by (metis tblk_par_waitblk')
  with a0 show ?thesis
    by auto
qed

lemma restrict_slide:
  assumes "t1 < t2" "t1 > 0"
      and "(\<lambda>\<tau>\<in>{0..t2}. p \<tau>) = (\<lambda>\<tau>\<in>{0..t2}. p' \<tau>)"
    shows "(\<lambda>\<tau>\<in>{0..t2 - t1}. p (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2 - t1}. p (\<tau> + t1))"
  by blast

lemma wf_tblk_par_slide:
  assumes "wf_tblk_par (WaitBlk t2 p rdy)"
      and "t1 > 0"
    shows "wf_tblk_par (WaitBlk (t2 - t1) (\<lambda> \<tau>. p(\<tau> + t1)) rdy)"
  using assms
  apply (simp add: WaitBlk_def, clarsimp)
  apply (rule_tac x = "\<lambda>\<tau>. f (\<tau> + t1)" in exI)
  by (simp add: restrict_iff)

lemma tr_combine_sim: 
  assumes "combine_blocks chs tr1 tr2 tr3"
      and "tr_par \<alpha> tr1 tr1'"
      and "tr_par \<beta> tr2 tr2'"
      and "wf_tr_par tr1'"
      and "wf_tr_par tr2'"
    shows "\<exists>tr3'. combine_blocks chs tr1' tr2' tr3' \<and> tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) tr3 tr3'"
  using assms
proof(induction arbitrary: tr1' tr2' rule: combine_blocks.induct)
  case (combine_blocks_empty comms)
  then show ?case 
    by (simp add: combine_blocks.combine_blocks_empty tr_par_def)
next
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  then obtain blks1' blks2' where a0: "tr1' = InBlock ch v # blks1'" "tr_par \<alpha> blks1 blks1'"
  "tr2' = OutBlock ch v # blks2'" "tr_par \<beta> blks2 blks2'"
    by (metis list_all2_Cons1 tblk_par.simps(2) tr_par_def)
  with combine_blocks_pair1.IH obtain blks' where "combine_blocks comms blks1' blks2' blks'" 
  "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    using combine_blocks_pair1.prems(3,4) wf_tr_par_cons by blast
  with combine_blocks_pair1.hyps(1) a0 show ?case
    using combine_blocks.combine_blocks_pair1[of ch comms blks1' blks2' blks' v] tr_par_def by auto
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  then obtain blks1' blks2' where b0: "tr1' = OutBlock ch v # blks1'" "tr_par \<alpha> blks1 blks1'"
  "tr2' = InBlock ch v # blks2'" "tr_par \<beta> blks2 blks2'"
    by (metis list_all2_Cons1 tblk_par.simps(2) tr_par_def)
  with combine_blocks_pair2.IH obtain blks' where "combine_blocks comms blks1' blks2' blks'" 
  "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    using combine_blocks_pair2.prems(3,4) wf_tr_par_cons by blast
  with combine_blocks_pair2.hyps(1) b0 show ?case
    using combine_blocks.combine_blocks_pair2[of ch comms blks1' blks2' blks' v] tr_par_def by auto
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ch_type v)
  then obtain blks1' where c0: "tr1' = CommBlock ch_type ch v # blks1'" "tr_par \<alpha> blks1 blks1'"
    by (metis list_all2_Cons1 tblk_par.simps(2) tr_par_def)
  with combine_blocks_unpair1.IH[of blks1' tr2'] obtain blks' where 
  "combine_blocks comms blks1' tr2' blks'" "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    using combine_blocks_unpair1.prems(2,3,4) wf_tr_par_cons by blast
  with c0 combine_blocks_unpair1.hyps(1) show ?case
    using combine_blocks.combine_blocks_unpair1[of ch comms blks1' tr2' blks' ch_type v] tr_par_def by auto
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ch_type v)
  then obtain blks2' where d0: "tr2' = CommBlock ch_type ch v # blks2'" "tr_par \<beta> blks2 blks2'"
    by (metis list_all2_Cons1 tblk_par.simps(2) tr_par_def)
  with combine_blocks_unpair2.IH[of tr1' blks2'] obtain blks' where
  "combine_blocks comms tr1' blks2' blks'" "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    using combine_blocks_unpair2.prems(1,3,4) wf_tr_par_cons by blast
  with d0 combine_blocks_unpair2.hyps(1) show ?case
    using combine_blocks.combine_blocks_unpair2[of ch comms tr1' blks2' blks' ch_type v] tr_par_def by auto
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy d)
  then obtain hist1' blks1' hist2' blks2' where e0:
  "tr1' = (WaitBlk d hist1' rdy1) # blks1'" "tr_par \<alpha> blks1 blks1'" "\<forall>t\<in>{0..d}. (hist1 t, hist1' t) \<in> \<alpha>"
  "tr2' = (WaitBlk d hist2' rdy2) # blks2'" "tr_par \<beta> blks2 blks2'" "\<forall>t\<in>{0..d}. (hist2 t, hist2' t) \<in> \<beta>"
    by (metis (lifting) tr_par_cons_waitblk)
  with combine_blocks_wait1.IH obtain blks' where e1: "combine_blocks comms blks1' blks2' blks'"
    "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    using combine_blocks_wait1.prems(3,4) wf_tr_par_cons by blast
  from e0(3,6) combine_blocks_wait1.hyps(3) have 
    "tblk_par (\<alpha> \<uplus>\<^sub>p \<beta>) (WaitBlk d hist rdy) (WaitBlk d (\<lambda>\<tau>. ParState (hist1' \<tau>) (hist2' \<tau>)) rdy)"
    by (simp add: WaitBlk_def lift_rel_par_def restrict_def)
  with e0 e1 combine_blocks_wait1.hyps show ?case
    using combine_blocks.combine_blocks_wait1[of comms blks1' blks2' blks' rdy1 rdy2
    "\<lambda>\<tau>. ParState (hist1' \<tau>) (hist2' \<tau>)" hist1' hist2' rdy d]
    using tr_par_def by auto
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  then obtain hist1' blks1' hist2' blks2' where f0:
  "tr1' = (WaitBlk t1 hist1' rdy1) # blks1'" "tr_par \<alpha> blks1 blks1'" "\<forall>t\<in>{0..t1}. (hist1 t, hist1' t) \<in> \<alpha>"
  "tr2' = (WaitBlk t2 hist2' rdy2) # blks2'"  "tr_par \<beta> blks2 blks2'" "\<forall>t\<in>{0..t2}. (hist2 t, hist2' t) \<in> \<beta>"
    by (metis (no_types, opaque_lifting) tr_par_cons_waitblk)
  then have f1: "tr_par \<beta> (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2' (\<tau> + t1)) rdy2 # blks2')"
    by (simp add: WaitBlk_def tr_par_def combine_blocks_wait2.hyps(4) order_less_imp_le)
  with combine_blocks_wait2.IH combine_blocks_wait2.prems(3,4) f0 obtain blks' where f2:
  "combine_blocks comms blks1' (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2' (\<tau> + t1)) rdy2 # blks2') blks'"
  "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    by (metis WaitBlk_def list_all_simps(1) wf_tblk_par.simps(1) wf_tr_par_def)
  from f0(3,6) \<open>t1 < t2\<close>  have "tblk_par (\<alpha> \<uplus>\<^sub>p \<beta>) (WaitBlk t1 hist rdy) (WaitBlk t1 (\<lambda>\<tau>. ParState (hist1' \<tau>) (hist2' \<tau>)) rdy)"
    by (simp add: WaitBlk_def combine_blocks_wait2.hyps(5) lift_rel_par_def)
  with f0 f1 f2 combine_blocks_wait2.hyps show ?case 
    using combine_blocks.combine_blocks_wait2[of comms blks1' t2 t1 hist2' rdy2 blks2' blks' rdy1 
    "\<lambda>\<tau>. ParState (hist1' \<tau>) (hist2' \<tau>)" hist1' rdy] tr_par_def by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  then obtain hist1' blks1' hist2' blks2' where g0:
  "tr1' = (WaitBlk t1 hist1' rdy1) # blks1'" "tr_par \<alpha> blks1 blks1'" "\<forall>t\<in>{0..t1}. (hist1 t, hist1' t) \<in> \<alpha>" 
  "tr2' = (WaitBlk t2 hist2' rdy2) # blks2'" "tr_par \<beta> blks2 blks2'" "\<forall>t\<in>{0..t2}. (hist2 t, hist2' t) \<in> \<beta>"
    by (metis (no_types, opaque_lifting) tr_par_cons_waitblk)
  then have g1: "tr_par \<alpha> (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1' (\<tau> + t2)) rdy1 # blks1')"
    by (simp add: WaitBlk_def tr_par_def combine_blocks_wait3.hyps(4) order_less_imp_le)
  with combine_blocks_wait3.IH g0(1,4,5) combine_blocks_wait3.prems(3,4) obtain blks' where g2:
    "combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1' (\<tau> + t2)) rdy1 # blks1') blks2' blks'"
    "tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) blks blks'"
    by (metis WaitBlk_def list_all_simps(1) wf_tblk_par.simps(1) wf_tr_par_def)
  from g0(3,6) \<open>t2 < t1\<close>  have "tblk_par (\<alpha> \<uplus>\<^sub>p \<beta>) (WaitBlk t2 hist rdy) (WaitBlk t2 (\<lambda>\<tau>. ParState (hist1' \<tau>) (hist2' \<tau>)) rdy)"
    by (simp add: WaitBlk_def combine_blocks_wait3.hyps(5) lift_rel_par_def)
  with g0 g1 g2 combine_blocks_wait3.hyps show ?case 
    using combine_blocks.combine_blocks_wait3[of comms t1 t2 hist1' rdy1 blks1' blks2' blks' rdy2
    "\<lambda>\<tau>. ParState (hist1' \<tau>) (hist2' \<tau>)" hist2' rdy]
    tr_par_def by auto
qed

theorem sim_Single:
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
  shows "(Single P\<^sub>c, State s\<^sub>c) \<sqsubseteq>\<^sub>p \<Up>\<^sub>s \<alpha> (Single P\<^sub>a, State s\<^sub>a)"
proof-
  {
    fix s' tr\<^sub>c
    assume "par_big_step (Single P\<^sub>c) (State s\<^sub>c) tr\<^sub>c s'"
    then obtain s\<^sub>c' where a0: "big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c'" "s' = State s\<^sub>c'"
      by (metis SingleE gstate.inject(1))
    with assms obtain s\<^sub>a' tr\<^sub>a where "big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a'" "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>" "(s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
    "tr_single \<alpha> tr\<^sub>c tr\<^sub>a"
      by (meson hybrid_sim_single_def)
    with a0 have "(State s\<^sub>c, State s\<^sub>a) \<in> \<Up>\<^sub>s \<alpha> \<and> (\<exists>s'' tr\<^sub>a. par_big_step (Single P\<^sub>a) (State s\<^sub>a) tr\<^sub>a s'' 
     \<and> tr_par (\<Up>\<^sub>s \<alpha>) tr\<^sub>c tr\<^sub>a \<and> (s', s'') \<in> \<Up>\<^sub>s \<alpha>)"
      by (metis (mono_tags, lifting) CollectI SingleB lift_rel_single_def tr_lift_rel_single)
  }
  then show ?thesis
    by (simp add: hybrid_sim_par_def)
qed

theorem sim_Par:
  assumes "(P\<^sub>c\<^sub>1, s\<^sub>c\<^sub>1) \<sqsubseteq>\<^sub>p \<alpha> (P\<^sub>a\<^sub>1, s\<^sub>a\<^sub>1)"
      and "(P\<^sub>c\<^sub>2, s\<^sub>c\<^sub>2) \<sqsubseteq>\<^sub>p \<beta> (P\<^sub>a\<^sub>2, s\<^sub>a\<^sub>2)"
    shows "(Parallel P\<^sub>c\<^sub>1 chs P\<^sub>c\<^sub>2, ParState s\<^sub>c\<^sub>1 s\<^sub>c\<^sub>2) \<sqsubseteq>\<^sub>p \<alpha> \<uplus>\<^sub>p \<beta> (Parallel P\<^sub>a\<^sub>1 chs P\<^sub>a\<^sub>2, ParState s\<^sub>a\<^sub>1 s\<^sub>a\<^sub>2)"
proof-
  {
    fix s\<^sub>c' tr\<^sub>c
    assume "par_big_step (Parallel P\<^sub>c\<^sub>1 chs P\<^sub>c\<^sub>2) (ParState s\<^sub>c\<^sub>1 s\<^sub>c\<^sub>2) tr\<^sub>c s\<^sub>c'"
    then obtain s\<^sub>c\<^sub>1' s\<^sub>c\<^sub>2' tr\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>2 where a0: "par_big_step P\<^sub>c\<^sub>1 s\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>1 s\<^sub>c\<^sub>1'" "par_big_step P\<^sub>c\<^sub>2 s\<^sub>c\<^sub>2 tr\<^sub>c\<^sub>2 s\<^sub>c\<^sub>2'"
    "combine_blocks chs tr\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>2 tr\<^sub>c" "s\<^sub>c' = ParState s\<^sub>c\<^sub>1' s\<^sub>c\<^sub>2'"
      by (smt (verit, best) ParallelE gstate.inject(2))
    with assms obtain s\<^sub>a\<^sub>1' s\<^sub>a\<^sub>2' tr\<^sub>a\<^sub>1 tr\<^sub>a\<^sub>2 where 
    "(s\<^sub>c\<^sub>1, s\<^sub>a\<^sub>1) \<in> \<alpha> \<and> par_big_step P\<^sub>a\<^sub>1 s\<^sub>a\<^sub>1 tr\<^sub>a\<^sub>1 s\<^sub>a\<^sub>1' \<and> tr_par \<alpha> tr\<^sub>c\<^sub>1 tr\<^sub>a\<^sub>1 \<and> (s\<^sub>c\<^sub>1', s\<^sub>a\<^sub>1') \<in> \<alpha>"
    "(s\<^sub>c\<^sub>2, s\<^sub>a\<^sub>2) \<in> \<beta> \<and> par_big_step P\<^sub>a\<^sub>2 s\<^sub>a\<^sub>2 tr\<^sub>a\<^sub>2 s\<^sub>a\<^sub>2' \<and> tr_par \<beta> tr\<^sub>c\<^sub>2 tr\<^sub>a\<^sub>2 \<and> (s\<^sub>c\<^sub>2', s\<^sub>a\<^sub>2') \<in> \<beta>"
      by (meson hybrid_sim_par_def)
    with a0 have "(ParState s\<^sub>c\<^sub>1 s\<^sub>c\<^sub>2, ParState s\<^sub>a\<^sub>1 s\<^sub>a\<^sub>2) \<in> \<alpha> \<uplus>\<^sub>p \<beta> \<and> 
    (\<exists>s\<^sub>a' tr\<^sub>a. par_big_step (Parallel P\<^sub>a\<^sub>1 chs P\<^sub>a\<^sub>2) (ParState s\<^sub>a\<^sub>1 s\<^sub>a\<^sub>2) tr\<^sub>a s\<^sub>a' \<and> 
     tr_par (\<alpha> \<uplus>\<^sub>p \<beta>) tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha> \<uplus>\<^sub>p \<beta>)"
      by (smt (verit, ccfv_threshold) ParallelB lift_rel_par_def mem_Collect_eq pproc_wf_tr_single tr_combine_sim)
  }
  then show ?thesis
    using hybrid_sim_par_def by presburger
qed

lemma loop_inv: 
  assumes "\<forall>s s'. b s \<longrightarrow> reachable C s s' \<longrightarrow> b s'"
      and "b s" "reachable (Rep C) s s'"
    shows "b s'"
proof-
  from assms(3) obtain tr n where "iterate_bigstep n (s, []) C (s', tr)"
    by (metis big_step_while reachable_def)
  then show ?thesis
  proof(induct n arbitrary: s' tr)
    case 0
    with assms(2) show ?case
      by simp
  next
    case (Suc n)
    then obtain sm tr1 tr2 where a0: "iterate_bigstep n (s, []) C (sm, tr1)" 
    "big_step C sm tr2 s'" "tr = tr1 @ tr2"
      by auto
    with Suc.hyps[of sm tr1] have "b sm"
      by auto
    with a0(2) assms(1) show ?case
      using reachable_def by blast
  qed
qed

lemma loop_inv_control:
  assumes "\<forall>s s'. b2 s \<longrightarrow> reachable C1 s s' \<longrightarrow> b2 s'"
      and "\<forall>s s'. b2 s \<longrightarrow> reachable C2 s s' \<longrightarrow> b2 s'"
      and "\<forall>s s' tr. b2 s \<longrightarrow> big_step (Cont ode b1) s tr s' \<longrightarrow> tr \<noteq> [] \<longrightarrow> ode_inv_assn b2 tr"
      and "b2 s"
      and "reachable (Rep (C1; Cont ode b1; C2)) s s'"
    shows "b2 s'"
proof-
  {
    fix s s'
    assume a0: "b2 s" 
       and a1: "reachable (C1; Cont ode b1; C2) s s'"
    then obtain tr1 s1 tr2 s2 tr3 where a2: "big_step C1 s tr1 s1" "big_step (Cont ode b1) s1 tr2 s2"
    "big_step C2 s2 tr3 s'"
      by (meson reachable_def seqE)
      with assms(1) a0 have "b2 s1"
        using reachable_def by blast
      with a2(2) assms(3) have "b2 s2"
        apply (cases rule: contE, simp)
         apply blast
        by (metis atLeastAtMost_iff less_eq_real_def list.distinct(1) ode_inv_imp)
      with assms(2) a2(3) have "b2 s'"
        using reachable_def by blast
    }
    with assms(4,5) show ?thesis
      using loop_inv by blast
  qed

theorem sim_control:
  assumes "\<forall>s s'. b2 s \<longrightarrow> reachable C1 s s' \<longrightarrow> b2 s'"
      and "\<forall>s s'. b2 s \<longrightarrow> reachable C2 s s' \<longrightarrow> b2 s'"
      and "\<forall>s s' tr. b2 s \<longrightarrow> big_step (Cont ode b1) s tr s' \<longrightarrow> tr \<noteq> [] \<longrightarrow> ode_inv_assn b2 tr"
      and "b2 s"
    shows "(Rep (C1; (Cont ode b1); C2), s) \<sqsubseteq> Id (Rep (C1; (Cont ode (\<lambda>s. b1 s \<and> b2 s)); C2), s)"
  apply (rule sim_unloop_Id, clarify)
  subgoal for s1
    apply (rule sim_seq_Id, simp add: refl_Id sim_refl, clarify)
    subgoal for s2
      apply (rule sim_seq_Id, rule sim_cont_DC, clarify)
      using assms loop_inv_control apply blast
      using refl_Id sim_refl by blast
    done
  done

end