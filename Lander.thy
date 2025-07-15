theory Lander
  imports Sync_Refine
begin

definition Fc :: char where "Fc = CHR ''a''"
definition M :: char where "M = CHR ''b''"
definition V :: char where "V = CHR ''c''"
definition T :: char where "T = CHR ''d''"
definition W :: char where "W = CHR ''e''"

definition Period :: real where "Period = 0.128"


lemma train_vars_distinct [simp]: "T \<noteq> V" "T \<noteq> W"  
                                  "V \<noteq> T" "V \<noteq> W" 
                                  "W \<noteq> T" "W \<noteq> V" 
  unfolding T_def V_def W_def by auto

definition W_upd :: "real \<Rightarrow> real \<Rightarrow> real" where
  "W_upd v w = (-(w - 3.732) * 0.01 + 3.732 - (v - (-1.5)) * 0.6)"

text \<open>Processes\<close>

definition Plant :: proc where
  "Plant = Interrupt (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                       W := (\<lambda>s. (s W)^2 / 2500 )))) ((\<lambda>_. True))
   [(''p2c''[!](\<lambda>s. s V), Cm (''p2c''[!](\<lambda>s. s W)); Cm (''c2p''[?]W))]"

definition Plant' :: proc where
  "Plant' = Interrupt (ODE ((\<lambda>_ _. 0)(V := \<lambda>s. s W - 3.732, W := \<lambda>s. (s W)\<^sup>2 / 2500))) (\<lambda>s. True)
   [(''p2c''[!](\<lambda>s. s V), outputs ''p2c'' [\<lambda>s. s W]; inputs ''c2p'' [W])]"

definition Ctrl :: proc where
  "Ctrl = Wait (\<lambda>_. Period);
      Cm (''p2c''[?]V);
      Cm (''p2c''[?]W);
      Cm (''c2p''[!](\<lambda>s. W_upd (s V) (s W)))"

definition Ctrl' :: proc where 
  "Ctrl' = Wait (\<lambda>s. Period); 
           Cm (''p2c''[?]V); 
           inputs ''p2c'' [W]; 
           outputs ''c2p'' [\<lambda>s. W_upd (s V) (s W)]"

definition Abs :: proc where
  "Abs = T ::= (\<lambda>_. 0);
   Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                        W := (\<lambda>s. (s W)^2 / 2500 ),
                        T := (\<lambda>_. 1)))) ((\<lambda>s. s T < Period));
   W ::= (\<lambda>s. W_upd (s V) (s W))"

lemma assign_refine:
  assumes "s\<^sub>p' = s\<^sub>p(T := t)"
  shows "(W ::= (\<lambda>_. W_upd (s\<^sub>p V) (s\<^sub>p W)), s\<^sub>p') \<sqsubseteq> Id (W ::= (\<lambda>s. W_upd (s V) (s W)), s\<^sub>p')"
  using assms
  by (rule_tac sim_assign_Id, simp)

lemma Ctrl_refine: "(Ctrl, s) \<sqsubseteq> Id (Ctrl', s)"
  apply (simp add: Ctrl_def Ctrl'_def)
  apply (rule sim_seq_Id, simp add: refl_Id sim_refl, clarsimp)
  subgoal for s1
    apply (rule sim_seq_Id,simp add: refl_Id sim_refl, clarsimp)
    subgoal for s2
      apply (rule sim_seq_Id)
      using equiv_Id_single_skipr hybrid_equiv_single_def apply auto[1]
      apply clarsimp
      subgoal for s3
        using equiv_Id_single_skipr hybrid_equiv_single_def by blast
      done
    done
  done

lemma Plant_refine: "(Plant, s) \<sqsubseteq> Id (Plant', s)"
  apply (simp add: Plant_def Plant'_def)
  apply (rule sim_interrupt_Id, simp_all, clarify)
  subgoal for s1
    apply (rule sim_seq_Id)
    using equiv_Id_single_skipr hybrid_equiv_single_def apply force
    apply clarsimp
    using equiv_Id_single_skipr hybrid_equiv_single_def by blast
  done

lemma Lander_Refine_mid:
  assumes "\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"
  shows "(Parallel (Single (Rep Plant')) {''p2c'', ''c2p''} (Single (Rep Ctrl')), ParState (State s\<^sub>p) (State s\<^sub>c))
   \<sqsubseteq>\<^sub>I \<alpha>  (Rep Abs, s\<^sub>p)"
  using assms Period_def exp_independ_def unfolding Abs_def Ctrl'_def Plant'_def 
  apply (rule_tac sim_control_loop[of "''p2c''" "{''p2c'', ''c2p''}" "''c2p''" \<alpha> T "[W]" "[(W, \<lambda>s. s W)]"
  "[\<lambda>s. s W]" "[W]" "[(W, \<lambda>s. W_upd (s V) (s W))]" "[\<lambda>s. W_upd (s V) (s W)]" Period 
  "(\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500 ))" V "(\<lambda>s. s V)" 
  "W ::= (\<lambda>s. W_upd (s V) (s W))" s\<^sub>p s\<^sub>c], simp_all)
  using assign_refine big_step_skipr hybrid_sim_single_Id by force

theorem Lander_Refine:
  assumes "\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"
  shows "(Parallel (Single (Rep Plant)) {''p2c'', ''c2p''} (Single (Rep Ctrl)), ParState (State s\<^sub>p) (State s\<^sub>c))
   \<sqsubseteq>\<^sub>I \<alpha> (Rep Abs, s\<^sub>p)"
  using assms
  apply (rule_tac P\<^sub>c\<^sub>1 = "Rep Plant'" and P\<^sub>c\<^sub>2 = "Rep Ctrl'" and P\<^sub>a = "Rep Abs" in sim_int_cons)
     apply (rule sim_unloop, simp_all add: Plant_refine)
    apply (rule sim_unloop, simp_all add: Ctrl_refine)
   apply (simp add: refl_Id sim_refl)
  by (simp add: Lander_Refine_mid)




end