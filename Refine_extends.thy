theory Refine_extends
  imports Refine
begin

fun tblk_single_extends :: "state rel \<Rightarrow> trace_block \<Rightarrow> trace_block \<Rightarrow> bool" where
  "tblk_single_extends \<alpha> (WaitBlock d1 p1 r1) (WaitBlock d2 p2 r2) = (
     d1 \<le> d2 \<and> r1 = r2 \<and> (\<forall>t\<in>{0..d1}.
       (\<exists>s1 s2. p1 t = State s1 \<and> p2 t = State s2 \<and> (s1, s2) \<in> \<alpha>)
     ))"
| "tblk_single_extends _ b1 b2 = (b1 = b2)"

lemma tblk_implie_extends:
  assumes "tblk_single \<alpha> blk1 blk2"
  shows "tblk_single_extends \<alpha> blk1 blk2"
  using assms
  apply (cases blk1, cases blk2, simp_all)
  apply (cases blk2, simp)
  by auto

definition tr_single_extends :: "state rel \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "tr_single_extends \<alpha> tr1 tr2 \<equiv> list_all2 (tblk_single_extends \<alpha>) tr1 tr2"

lemma tr_single_implies_extends:
  assumes "tr_single \<alpha> tr1 tr2"
  shows "tr_single_extends \<alpha> tr1 tr2"
  by (metis assms list_all2_mono tblk_implie_extends tr_single_def tr_single_extends_def)

definition hybrid_sim_single_extends :: "proc \<Rightarrow> state \<Rightarrow> (state rel) \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" 
  ("'(_, _') \<sqsubseteq>\<^sub>e\<^sub>x _ '(_, _')") where
  "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>e\<^sub>x \<alpha> (P\<^sub>a, s\<^sub>a) = (\<forall>s\<^sub>c' tr\<^sub>c. big_step P\<^sub>c s\<^sub>c tr\<^sub>c s\<^sub>c' \<longrightarrow> (s\<^sub>c, s\<^sub>a) \<in> \<alpha> \<and>
   (\<exists>s\<^sub>a' tr\<^sub>a. big_step P\<^sub>a s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_single_extends \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>))"

lemma hybrid_sim_single_implies_extends:
  assumes "(P\<^sub>c, s\<^sub>c) \<sqsubseteq> \<alpha> (P\<^sub>a, s\<^sub>a)"
  shows "(P\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>e\<^sub>x \<alpha> (P\<^sub>a, s\<^sub>a)"
  by (meson assms hybrid_sim_single_def hybrid_sim_single_extends_def tr_single_implies_extends)

theorem sim_ex_wait:
  assumes "(s\<^sub>c, s\<^sub>a) \<in> \<alpha>"
      and "e\<^sub>c s\<^sub>c \<le> e\<^sub>a s\<^sub>a" "e\<^sub>c s\<^sub>c > 0"
    shows "(Wait e\<^sub>c, s\<^sub>c) \<sqsubseteq>\<^sub>e\<^sub>x \<alpha> (Wait e\<^sub>a, s\<^sub>a)"
proof-
  {
    fix s\<^sub>c' tr\<^sub>c
    assume "big_step (Wait e\<^sub>c) s\<^sub>c tr\<^sub>c s\<^sub>c'"
    with assms(3) have a0: "tr\<^sub>c = [WaitBlk (e\<^sub>c s\<^sub>c) (\<lambda>_. State s\<^sub>c) ({}, {})]" "s\<^sub>c = s\<^sub>c'"
      using waitE by blast+
    let ?tr\<^sub>a = "[WaitBlk (e\<^sub>a s\<^sub>a) (\<lambda>_. State s\<^sub>a) ({}, {})]"
    from assms(1, 2) a0(1) have a1: "tr_single_extends \<alpha> tr\<^sub>c ?tr\<^sub>a"
      by (simp add: tr_single_extends_def WaitBlk_def)
    then have "\<exists>s\<^sub>a' tr\<^sub>a. big_step (Wait e\<^sub>a) s\<^sub>a tr\<^sub>a s\<^sub>a' \<and> tr_single_extends \<alpha> tr\<^sub>c tr\<^sub>a \<and> (s\<^sub>c', s\<^sub>a') \<in> \<alpha>"
      using a0(2) assms dual_order.strict_trans1 waitB1 by blast
  }
  then show ?thesis
    using assms(1) hybrid_sim_single_extends_def by auto
qed

theorem sim_ex_DR:
  assumes "\<forall>s. b1 s \<longrightarrow> b2 s"
      and "finish (Cont ode b2) s"
    shows "(Cont ode b1, s) \<sqsubseteq>\<^sub>e\<^sub>x Id (Cont ode b2, s)"
proof-
  {
    fix s' tr 
    assume "big_step (Cont ode b1) s tr s'"
    then have "\<exists>tr1 s1'. big_step (Cont ode b2) s tr1 s1'"
    proof(rule contE)
      assume "tr = []" "s' = s" "\<not> b1 s"
      then show ?thesis
        using ContB1 assms(2) finish_def reachable_def by auto
    next
      assume ""
  }
end