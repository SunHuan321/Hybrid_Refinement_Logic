theory Refine
  imports Language
begin

type_synonym tassn = "trace \<Rightarrow> bool"
(*
fun traceblock_extends :: "gstate rel \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where
  "traceblock_extends \<alpha> (WaitBlock d1 p1 r1) (WaitBlock d2 p2 r2) =
     (d1 \<le> d2 \<and> r1 = r2 \<and> (\<forall>t\<in>{0..d1}. (p1 t, p2 t) \<in> \<alpha>))"
| "traceblock_extends _ b1 b2 = (b1 = b2)"

definition strel_trans_single :: "state rel \<Rightarrow> gstate rel" where 
  "strel_trans_single \<alpha> = {(State s1, State s2) | s1 s2. (s1, s2) \<in> \<alpha>}"

definition traceblock_extends_single :: "state rel \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where  
  "traceblock_extends_single \<alpha> t1 t2 = traceblock_extends (strel_trans_single \<alpha>) t1 t2"

fun trace_extends :: "gstate rel \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "trace_extends \<alpha> [] [] = True"
| "trace_extends \<alpha> (b1 # tr1) (b2 # tr2) = (
     traceblock_extends \<alpha> b1 b2 \<and> trace_extends \<alpha> tr1 tr2
   )"
| "trace_extends _ _ _ = False"

definition trace_extends_single :: "state rel \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool"
  where "trace_extends_single \<alpha> = trace_extends (strel_trans_single \<alpha>)"

lemma trace_extends_append: "\<lbrakk>trace_extends \<alpha> l1 l1'; trace_extends \<alpha> l2 l2'\<rbrakk> \<Longrightarrow> 
      trace_extends \<alpha> (l1 @ l2) (l1' @ l2')"
  sorry
*)

fun tblk_extends_single :: "state rel \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where
  "tblk_extends_single \<alpha> (WaitBlock d1 p1 r1) (WaitBlock d2 p2 r2) = (
     d1 \<le> d2 \<and> r1 = r2 \<and> (\<forall>t\<in>{0..d1}.
       (\<exists>s1 s2. p1 t = State s1 \<and> p2 t = State s2 \<and> (s1, s2) \<in> \<alpha>)
     ))"
| "tblk_extends_single _ b1 b2 = (b1 = b2)"

lemma tblk_extends_single_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tblk_extends_single \<alpha> blk1 blk2"
    shows "tblk_extends_single \<beta> blk1 blk2"
  using assms
  apply (cases blk1, cases blk2, simp_all)
  apply (cases blk2, simp)
  apply auto
  by (meson atLeastAtMost_iff subsetD)

lemma tblk_extends_single_refl:
  assumes "refl \<alpha>"
      and "wf_tblk_single blk"
  shows "tblk_extends_single \<alpha> blk blk"
proof(cases blk)
  case (CommBlock c ch v)
  then show ?thesis by auto
next
  case (WaitBlock d p r)
  then show ?thesis
    using assms(1) assms(2) reflD by fastforce
qed

lemma tblk_extends_single_compose:
  assumes "tblk_extends_single \<alpha> blk1 blk2"
      and "tblk_extends_single \<beta> blk2 blk3"
    shows "tblk_extends_single (\<alpha> O \<beta>) blk1 blk3"
  using assms
  apply (cases blk1, cases blk2, cases blk3, simp_all)
  apply (cases blk2, cases blk3, simp_all)
  apply (cases blk3, simp)
  apply auto
  by (metis (no_types, opaque_lifting) atLeastAtMost_iff gstate.inject(1) 
      order.trans relcomp.relcompI)

lemma tblk_extends_single_trans:
  assumes "trans \<alpha>"
      and "tblk_extends_single \<alpha> blk1 blk2"
      and "tblk_extends_single \<alpha> blk2 blk3"
    shows "tblk_extends_single \<alpha> blk1 blk3"
  using assms
  by (meson tblk_extends_single_compose tblk_extends_single_weaken trans_O_subset)

definition tr_extends_single :: "state rel \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "tr_extends_single \<alpha> tr1 tr2 \<equiv> list_all2 (tblk_extends_single \<alpha>) tr1 tr2"

lemma tr_extends_single_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "tr_extends_single \<alpha> tr1 tr2"
    shows "tr_extends_single \<beta> tr1 tr2"
  using assms
  by (metis list_all2_conv_all_nth tblk_extends_single_weaken tr_extends_single_def)

lemma tr_extends_single_refl:
  assumes "refl \<alpha>"
      and "wf_tr_single tr"
    shows "tr_extends_single \<alpha> tr tr"
  using assms
  by (simp add: list_all2_conv_all_nth list_all_length tblk_extends_single_refl 
      tr_extends_single_def)

lemma tr_extends_single_compose:
  assumes "trans \<alpha>"
      and "tr_extends_single \<alpha> tr1 tr2"
      and "tr_extends_single \<beta> tr2 tr3"
    shows "tr_extends_single (\<alpha> O \<beta>) tr1 tr3"
  using assms
  by (smt (verit, best) list_all2_conv_all_nth tblk_extends_single_compose tr_extends_single_def)

lemma tr_extends_single_trans:
  assumes "trans \<alpha>"
      and "tr_extends_single \<alpha> tr1 tr2"
      and "tr_extends_single \<alpha> tr2 tr3"
    shows "tr_extends_single \<alpha> tr1 tr3"
  using assms
  by (meson tr_extends_single_compose tr_extends_single_weaken trans_O_subset)
  
definition hybrid_sim_single :: "proc \<Rightarrow> state \<Rightarrow> (state rel) \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" 
  ("'(_, _') \<sqsubseteq> _ '(_, _')") where
  "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a) = (\<forall>s\<^sub>c' tr\<^sub>c. big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>
   (\<exists>s\<^sub>a' tr\<^sub>a. big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_extends_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>))"

definition reachable :: "proc \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "reachable C s s' = (\<exists>tr. big_step C s tr s')"

definition finish :: "proc \<Rightarrow> state \<Rightarrow> bool" where
  "finish C s = (\<exists>s'. reachable C s s')"

theorem sim_weaken:
  assumes "\<alpha> \<subseteq> \<beta>"
      and "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
    shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<beta> (P\<^sub>a, s\<^sub>a)"
  using assms hybrid_sim_single_def
  by (meson subsetD tr_extends_single_weaken)

theorem sim_refl: 
  assumes "refl \<alpha>"
  shows "(C, s) \<sqsubseteq> \<alpha> (C, s)"
  using assms hybrid_sim_single_def
  by (meson proc_wf_tr_single reflD tr_extends_single_refl)

theorem sim_compose:
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>m, s\<^sub>m)"
      and "(P\<^sub>m, s\<^sub>m) \<sqsubseteq> \<beta> (P\<^sub>a, s\<^sub>a)"
    shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> (\<alpha> O \<beta>) (P\<^sub>a, s\<^sub>a)"
  using assms hybrid_sim_single_def
  by (smt (verit) list_all2_trans relcomp.simps tblk_extends_single_compose tr_extends_single_def)

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
  apply (rule_tac x = tr\<^sub>c in exI, simp add: tr_extends_single_def)
  using HavocB assignE by blast

corollary sim_havoc_Id: "((x ::= e), s) \<sqsubseteq> Id ((x ::= *), s)"
  by (rule sim_havoc, simp_all)

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
  apply (simp add: hybrid_sim_single_def, clarify)
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
  by (metis AssumeB AssumeE list_all2_Nil2 tr_extends_single_def)
  
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
      "tr_extends_single \<alpha> tr\<^sub>c\<^sub>1 tr\<^sub>a\<^sub>1" "(s\<^sub>c\<^sub>m, s\<^sub>a\<^sub>m) \<in> \<alpha>"
        using hybrid_sim_single_def by blast       
      from assms(3) a0(1) a0(2) a1(3) obtain s\<^sub>a' tr\<^sub>a\<^sub>2 where "big_step P\<^sub>a\<^sub>2 s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>2 s\<^sub>a'"
      "tr_extends_single \<alpha> tr\<^sub>c\<^sub>2 tr\<^sub>a\<^sub>2" "(s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis hybrid_sim_single_def reachable_def)
      with a0(3) a1(1) a1(2) have "\<exists>tr\<^sub>a s\<^sub>a'. big_step (P\<^sub>a\<^sub>1; P\<^sub>a\<^sub>2) s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_extends_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis list_all2_appendI seqB tr_extends_single_def)
    }
    with assms(1) show ?thesis
      using hybrid_sim_single_def by blast      
  qed

corollary sim_seq_Id:
  assumes "(P\<^sub>c\<^sub>1, s) \<sqsubseteq> Id (P\<^sub>a\<^sub>1, s)"
      and "\<forall>s'. reachable P\<^sub>c\<^sub>1 s s' \<longrightarrow> (P\<^sub>c\<^sub>2, s') \<sqsubseteq> Id (P\<^sub>a\<^sub>2, s')"
    shows "(P\<^sub>c\<^sub>1;P\<^sub>c\<^sub>2, s) \<sqsubseteq> Id (P\<^sub>a\<^sub>1; P\<^sub>a\<^sub>2, s)"
  by (rule sim_seq, simp_all add: assms)

(*
theorem sim_loop_l:
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>" "trans \<alpha>"
      and "\<forall>s\<^sub>c' s\<^sub>a'. reachable (Rep P\<^sub>c\<^sub>1) s\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> \<alpha> \<longrightarrow> (P\<^sub>c\<^sub>1; P\<^sub>a, s\<^sub>c') \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a')"
      and "\<forall>s\<^sub>c' s\<^sub>a'. reachable (Rep P\<^sub>c\<^sub>1) s\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c', s\<^sub>a') \<in> \<alpha> \<longrightarrow> (P\<^sub>c\<^sub>2, s\<^sub>c') \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a')"
    shows "(Rep P\<^sub>c\<^sub>1; P\<^sub>c\<^sub>2, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
proof-
  from assms have "(P\<^sub>c\<^sub>1; P\<^sub>a, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
    using RepetitionB1 reachable_def by blast
proof-
  {
    fix s\<^sub>c' tr\<^sub>c
    assume "big_step (Rep P\<^sub>c\<^sub>1; P\<^sub>c\<^sub>2) s\<^sub>c tr\<^sub>c s\<^sub>c'"
    then obtain s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>2 where a0: "big_step (Rep P\<^sub>c\<^sub>1) s\<^sub>c tr\<^sub>c\<^sub>1 s\<^sub>c\<^sub>m" "big_step P\<^sub>c\<^sub>2 s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>2 s\<^sub>c'" "tr\<^sub>c = tr\<^sub>c\<^sub>1 @ tr\<^sub>c\<^sub>2"
      by (meson seqE)
    then obtain n where a1: "iterate_bigstep n (s\<^sub>c, []) P\<^sub>c\<^sub>1 (s\<^sub>c\<^sub>m, tr\<^sub>c\<^sub>1)"
      by (metis append_Nil big_step_while)
    with a0(2) a0(3) have "\<exists>s\<^sub>a' tr\<^sub>a. big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_extends_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
      case 0
      then have b0: "s\<^sub>c = s\<^sub>c\<^sub>m \<and> tr\<^sub>c\<^sub>1 = []"
        by simp
      from assms(4) assms(1) have "(P\<^sub>c\<^sub>2, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
        using RepetitionB1 reachable_def sorry
      with b0 obtain s\<^sub>a' tr\<^sub>a where "big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_extends_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis "0.prems"(1) a0(3) hybrid_sim_single_def self_append_conv2)
      then show ?case
        by auto        
    next
      case (Suc n)
      from Suc.prems(3) obtain s\<^sub>c\<^sub>m\<^sub>1 tr\<^sub>c\<^sub>m\<^sub>1 tr\<^sub>c\<^sub>m\<^sub>2 where c0: "big_step P\<^sub>c\<^sub>1 s\<^sub>c tr\<^sub>c\<^sub>m\<^sub>1 s\<^sub>c\<^sub>m\<^sub>1"
      "iterate_bigstep n (s\<^sub>c\<^sub>m\<^sub>1, []) P\<^sub>c\<^sub>1 (s\<^sub>c\<^sub>m, tr\<^sub>c\<^sub>m\<^sub>2)" "tr\<^sub>c\<^sub>1 = tr\<^sub>c\<^sub>m\<^sub>1 @ tr\<^sub>c\<^sub>m\<^sub>2"
        by (metis append_Nil iterate_bigstep_converse iterate_bigstep_init')       
      with Suc.prems(1) Suc.hyps           
      then show ?case sorry
    qed
  }
  with assms(1) show ?thesis
    by (simp add: hybrid_sim_single_def)
qed
*)

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
    then have "\<exists>s\<^sub>a' tr\<^sub>a. big_step (Rep P\<^sub>a) s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_extends_single \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
    proof(induct n arbitrary: s\<^sub>c' tr\<^sub>c)
      case 0
      then have "s\<^sub>c = s\<^sub>c' \<and> tr\<^sub>c = []"
        by simp
      with assms(1) show ?case
        by (rule_tac x = s\<^sub>a in exI, rule_tac x = "[]" in exI, simp add: RepetitionB1 tr_extends_single_def) 
    next
      case (Suc n)
      from Suc.prems obtain s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>1 tr\<^sub>c\<^sub>2 where b0: "iterate_bigstep n (s\<^sub>c, []) P\<^sub>c (s\<^sub>c\<^sub>m, tr\<^sub>c\<^sub>1)"
      "big_step P\<^sub>c s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>2 s\<^sub>c'" "tr\<^sub>c = tr\<^sub>c\<^sub>1 @ tr\<^sub>c\<^sub>2"
        by auto
      with Suc.hyps[of s\<^sub>c\<^sub>m tr\<^sub>c\<^sub>1] obtain s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>1 where b1: "big_step (Rep P\<^sub>a) s\<^sub>a tr\<^sub>a\<^sub>1 s\<^sub>a\<^sub>m" 
           "tr_extends_single \<alpha> tr\<^sub>c\<^sub>1 tr\<^sub>a\<^sub>1" "(s\<^sub>c\<^sub>m, s\<^sub>a\<^sub>m) \<in> \<alpha>"
        by auto
      from b0(1) b0(2) assms(2) b1(3) obtain tr\<^sub>a\<^sub>2 s\<^sub>a' where b2: "big_step P\<^sub>a s\<^sub>a\<^sub>m tr\<^sub>a\<^sub>2 s\<^sub>a'" 
           "tr_extends_single \<alpha> tr\<^sub>c\<^sub>2 tr\<^sub>a\<^sub>2" "(s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
        by (metis big_step_while hybrid_sim_single_def reachable_def self_append_conv2)
      with b0(3) b1 show ?case
        by (rule_tac x = s\<^sub>a' in exI, rule_tac x = "tr\<^sub>a\<^sub>1 @ tr\<^sub>a\<^sub>2" in exI, simp add: 
               big_step_RepetitionB3 tr_extends_single_def list_all2_appendI)
    qed
  }
  with assms(1) show ?thesis
    using hybrid_sim_single_def by blast
qed

theorem sim_unloop_Id:
  assumes "\<forall>s'. reachable (Rep P\<^sub>c) s s' \<longrightarrow> (P\<^sub>c, s') \<sqsubseteq> Id (P\<^sub>a, s')"
  shows "(Rep P\<^sub>c, s) \<sqsubseteq> Id (Rep P\<^sub>a, s)"
  by (rule sim_unloop, simp_all add: assms)

text \<open>ODE with invariant\<close>
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
    by (meson hybrid_sim_single_def pair_in_Id_conv proc_wf_tr_single refl_Id tr_extends_single_refl)
qed


end

