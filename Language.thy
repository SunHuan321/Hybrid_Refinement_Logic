theory Language
  imports Analysis_More
begin

subsection \<open>Syntax\<close>

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Ready information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.\<close>
type_synonym rdy_info = "cname set \<times> cname set"

text \<open>Communications\<close>
datatype comm =
  Send cname exp        ("_[!]_" [110,108] 100)
| Receive cname var     ("_[?]_" [110,108] 100)

text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Assign var exp             ("_ ::= _" [99,95] 94)
| Havoc var                 ("_ ::= *" [99] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Assume fform         
| Wait exp  \<comment> \<open>Waiting for a specified amount of time\<close>
| IChoice proc proc  \<comment> \<open>Nondeterminism\<close>
| Rep proc   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE fform  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE fform "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc =
  Single proc
| Parallel pproc "cname set" pproc

text \<open>Global states\<close>
datatype gstate =
  State state
| ParState gstate gstate

subsection \<open>Traces\<close>

datatype comm_type = In | Out | IO

datatype trace_block =
  CommBlock comm_type cname real
| WaitBlock real "real \<Rightarrow> gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"
abbreviation "IOBlock ch v \<equiv> CommBlock IO ch v"

definition WaitBlk :: "real \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> rdy_info \<Rightarrow> trace_block" where
  "WaitBlk d p rdy = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"

lemma WaitBlk_not_Comm [simp]:
  "WaitBlk d p rdy \<noteq> CommBlock ch_type ch v"
  "CommBlock ch_type ch v \<noteq> WaitBlk d p rdy"
  by (simp add: WaitBlk_def)+

lemma restrict_cong_to_eq:
  fixes x :: real
  shows "restrict p1 {0..t} = restrict p2 {0..t} \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma restrict_cong_to_eq2:
  fixes x :: real
  shows "restrict p1 {0..} = restrict p2 {0..} \<Longrightarrow> 0 \<le> x \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma WaitBlk_ext: "t1 = t2 \<Longrightarrow>
   (\<And>\<tau>::real. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
   WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  by (auto simp add: restrict_def WaitBlk_def)

lemma WaitBlk_ext_real:  "t1 = t2 \<Longrightarrow> (\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
         WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  by (auto simp add: restrict_def WaitBlk_def)

lemma WaitBlk_cong:
  "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2 \<Longrightarrow> t1 = t2 \<and> rdy1 = rdy2"
  by (simp add: WaitBlk_def)

lemma WaitBlk_cong2:
  assumes "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
    and "0 \<le> t" "t \<le> t1"
  shows "hist1 t = hist2 t"
  using assms by (metis WaitBlk_def  restrict_cong_to_eq trace_block.inject(2))

lemma WaitBlk_split1:
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "t1 < t"
  shows "WaitBlk t1 p1 rdy = WaitBlk t1 p2 rdy"
  by (smt (verit, best) WaitBlk_cong2 WaitBlk_ext_real assms(1) assms(3))

lemma WaitBlk_split2:
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "t1 < t"
  shows "WaitBlk (t - t1) (\<lambda>\<tau>::real. p1 (\<tau> + t1)) rdy =
         WaitBlk (t - t1) (\<lambda>\<tau>::real. p2 (\<tau> + t1)) rdy"
  by (smt (verit, best) WaitBlk_cong2 WaitBlk_ext_real assms(1) assms(2))

lemmas WaitBlk_split = WaitBlk_split1 WaitBlk_split2

type_synonym trace = "trace_block list"


subsection \<open>Big-step semantics for the single process\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "(comm \<times> proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((ch[!]e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((ch[?]var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"

text \<open>big_step p s1 tr s2 means executing p starting from state s1 results
in a trace tr and final state s2.\<close>
inductive big_step :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (s(var := e s))"
| HavocB: "big_step (var ::= *) s [] (s(var := v))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| AssumeB: "b s1 \<Longrightarrow> big_step (Assume b) s1 [] s1"
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlk (e s) (\<lambda>_. State s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlk d (\<lambda>_. State s) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlk d (\<lambda>_. State s) ({}, {ch}),
             InBlock ch v] (s(var := v))"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      OutBlock ch (e (p d)) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy] s2"

lemma big_step_cong:
  "big_step c s1 tr s2 \<Longrightarrow> tr = tr' \<Longrightarrow> s2 = s2' \<Longrightarrow> big_step c s1 tr' s2'"
  by auto

inductive_cases skipE: "big_step Skip s1 tr s2"
inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
inductive_cases HavocE: "big_step (Havoc var) s1 tr s2"
inductive_cases sendE: "big_step (Cm (ch[!]e)) s1 tr s2"
inductive_cases receiveE: "big_step (Cm (ch[?]var)) s1 tr s2"
inductive_cases seqE: "big_step (Seq p1 p2) s1 tr s2"
inductive_cases AssumeE: "big_step (Assume b) s1 tr s2"
inductive_cases waitE: "big_step (Wait d) s1 tr s2"
inductive_cases echoiceE: "big_step (EChoice es) s1 tr s2"
inductive_cases ichoiceE: "big_step (IChoice p1 p2) s1 tr s2"
inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
inductive_cases RepE: "big_step (Rep C) s1 tr s2"
inductive_cases interruptE: "big_step (Interrupt ode b cs) s1 tr s2"

subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"

lemma WaitBlk_eq_combine:
  assumes "WaitBlk d1 p1 rdy1 = WaitBlk d1' p1' rdy1'"
    and "WaitBlk d1 p2 rdy2 = WaitBlk d1' p2' rdy2'"
   shows "WaitBlk d1 (\<lambda>\<tau>. ParState (p1 \<tau>) (p2 \<tau>)) (merge_rdy rdy1 rdy2) =
          WaitBlk d1' (\<lambda>\<tau>. ParState (p1' \<tau>) (p2' \<tau>)) (merge_rdy rdy1' rdy2')"
proof -
  have a1: "d1 = d1'" "rdy1 = rdy1'" "rdy2 = rdy2'"
    using assms WaitBlk_cong by blast+
  have a2: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p1 t = p1' t"
    using assms(1) WaitBlk_cong2 by auto
  have a3: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p2 t = p2' t"
    using assms(2) WaitBlk_cong2 by auto
  show ?thesis
    using WaitBlk_ext_real a1(1) a1(2) a1(3) a2 a3 by presburger
qed


text \<open>combine_blocks comms tr1 tr2 tr means tr1 and tr2 combines to tr, where
comms is the list of internal communication channels.\<close>
inductive combine_blocks :: "cname set \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  \<comment> \<open>Empty case\<close>
  combine_blocks_empty:
  "combine_blocks comms [] [] []"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (InBlock ch v # blks1) (OutBlock ch v # blks2) (IOBlock ch v # blks)"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlock ch v # blks1) (InBlock ch v # blks2) (IOBlock ch v # blks)"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (CommBlock ch_type ch v # blks1) blks2 (CommBlock ch_type ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (CommBlock ch_type ch v # blks2) (CommBlock ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlk (t2 - t1) (\<lambda>\<tau>. (\<lambda>x::real. hist2 x) (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. (\<lambda>x::real. hist1 x) (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t2 hist rdy # blks)"

inductive par_big_step :: "pproc \<Rightarrow> gstate \<Rightarrow> trace \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single p) (State s1) tr (State s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (ParState s11 s21) tr (ParState s12 s22)"

inductive_cases SingleE: "par_big_step (Single p) s1 tr s2"
inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"

subsection \<open>Lemmas for Loop\<close>

definition big_step_rel :: "proc \<Rightarrow> state \<times> trace \<Rightarrow> state \<times> trace \<Rightarrow> bool"
  where "big_step_rel C \<phi> \<phi>' = (\<exists>tr. big_step C (fst \<phi>) tr (fst \<phi>') \<and> snd \<phi>' = snd \<phi> @ tr)"

lemma while_then_reaches: 
  assumes "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
  shows "(big_step_rel (Rep C)) \<phi> \<phi>'"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case
    by (simp add: RepetitionB1 big_step_rel_def)
next
  case (step y z)
  then show ?case 
    using RepetitionB2 big_step_rel_def by auto
qed

lemma in_closure_then_while:
  assumes "big_step C' \<sigma> tr \<sigma>''"
  shows "\<And>C. C' = Rep C \<Longrightarrow> (big_step_rel C)\<^sup>*\<^sup>* (\<sigma>, l) (\<sigma>'', l @ tr)"
  using assms
proof(induct arbitrary: l rule: big_step.induct)
  case (RepetitionB2 C' \<sigma> tr1 \<sigma>' tr2 \<sigma>'' tr3)
  then show ?case
    by (metis append.assoc big_step_rel_def converse_rtranclp_into_rtranclp proc.inject(8) prod.sel(1,2))
next
  case (RepetitionB1 C' \<sigma>)
  then show ?case
    by force
qed(auto)

theorem loop_equiv:
  "big_step_rel (Rep C) \<phi> \<phi>' \<longleftrightarrow> (big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
  by (metis big_step_rel_def in_closure_then_while prod.collapse while_then_reaches)

fun iterate_bigstep :: "nat \<Rightarrow> state \<times> trace \<Rightarrow> proc \<Rightarrow> state \<times> trace \<Rightarrow> bool" where
  "iterate_bigstep 0 (s0, tr0) C (s, tr) \<longleftrightarrow> (s = s0 \<and> tr = tr0)"
| "iterate_bigstep (Suc n) (s0, tr0) C (s, tr) \<longleftrightarrow> (\<exists>s1 tr1 tr2. iterate_bigstep n (s0, tr0) C (s1, tr1) \<and>
   big_step C s1 tr2 s \<and> tr = tr1 @ tr2)"

lemma big_step_in_iterate_then_in_trans:
  assumes "iterate_bigstep n \<phi> C \<phi>'"
  shows "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
  using assms
proof(induct n arbitrary: \<phi> \<phi>')
  case 0
  then show ?case 
    using iterate_bigstep.elims(2) by blast
next
  case (Suc n)
  then show ?case
    using  rtranclp.rtrancl_into_rtrancl
    by (smt (verit, ccfv_SIG) Suc_inject big_step_rel_def fst_conv iterate_bigstep.elims(2) rtranclp.simps snd_conv)
qed

lemma big_step_reciprocal:
  assumes "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
      and "\<phi> \<in> S"
    shows "\<exists>n. iterate_bigstep n \<phi> C \<phi>'"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  then show ?case
    by (metis iterate_bigstep.simps(1) surj_pair)
next
  case (step y z)
  then obtain n where "iterate_bigstep n \<phi> C y" by blast
  then show ?case
    using iterate_bigstep.simps(2) step.hyps(2)
    by (metis (no_types, lifting) big_step_rel_def split_pairs)
qed
 
lemma big_step_while: "big_step (Rep C) s0 tr s1 \<longleftrightarrow> 
                       (\<exists>n. iterate_bigstep n (s0, tr0) C (s1, tr0 @ tr))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
    by (meson CollectI big_step_reciprocal in_closure_then_while)
next
  assume ?B
  then have "(big_step_rel C)\<^sup>*\<^sup>* (s0, tr0) (s1, tr0 @ tr)"
    using big_step_in_iterate_then_in_trans by blast
  then show ?A
    by (metis big_step_rel_def fst_conv same_append_eq snd_conv while_then_reaches)
qed

lemma big_step_RepetitionB3: "big_step (Rep p) s1 tr1 s2 \<Longrightarrow> big_step p s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow> big_step (Rep p) s1 tr s3"
  by (metis append.assoc big_step_while iterate_bigstep.simps(2))

lemma iterate_bigstep_converse:
  "iterate_bigstep (Suc n) (s0, tr0) C (s, tr) \<longleftrightarrow> (\<exists>s1 tr1. big_step C s0 tr1 s1
   \<and> iterate_bigstep n (s1, tr0 @ tr1) C (s, tr))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
  proof(induct n arbitrary: s tr)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc.prems obtain sm trm1 trm2 where a0: "iterate_bigstep (Suc n) (s0, tr0) C (sm, trm1)"
    "big_step C sm trm2 s" "tr = trm1 @ trm2"
      using iterate_bigstep.simps(2) by blast
    with Suc.hyps obtain sm' trm1' where a1: "big_step C s0 trm1' sm'" 
    "iterate_bigstep n (sm', tr0 @ trm1') C (sm, trm1)"
      by blast
    with a0(2) a0(3) have "iterate_bigstep (Suc n) (sm', tr0 @ trm1') C (s, tr)"
      by auto
    with a1(1) show ?case
      by blast
  qed
next
  assume ?B
  then show ?A
  proof(induct n arbitrary: s tr)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    from Suc.prems obtain s1 tr1 sm1 trm1 trm2 where b0: "big_step C s0 tr1 s1" 
    "iterate_bigstep n (s1, tr0 @ tr1) C (sm1, trm1)" "big_step C sm1 trm2 s"
    "tr = trm1 @ trm2"
      by auto
    with Suc.hyps have "iterate_bigstep (Suc n) (s0, tr0) C (sm1, trm1)"
      by blast
    with b0(3) b0(4) show ?case 
      using iterate_bigstep.simps(2) by blast
  qed
qed

lemma iterate_bigstep_init:
  assumes "iterate_bigstep n (s0, []) C (s, tr)" 
  shows "iterate_bigstep n (s0, tr0) C (s, tr0 @ tr)" 
  using assms
  apply (induct n arbitrary: s tr, simp)
  by fastforce

lemma iterate_bigstep_init':
  assumes "iterate_bigstep n (s0, tr0) C (s, tr)"
  shows "\<exists>tr1. iterate_bigstep n (s0, []) C (s, tr1) \<and> tr = tr0 @ tr1"
  using assms
proof(induct n arbitrary: s tr tr0)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by fastforce
qed


subsection \<open>Lemmas for well behaved trace for single thread\<close>

fun wf_tblk_single :: "trace_block \<Rightarrow> bool" where
  "wf_tblk_single (WaitBlock d p r) = (\<forall>t \<in> {0..d}. \<exists>s. p t = State s)"
| "wf_tblk_single _ = True"

lemma wf_waitblk: "wf_tblk_single (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy)"
  by (simp add: WaitBlk_def)

fun wf_tr_single :: "trace \<Rightarrow> bool" where
  "wf_tr_single tr = list_all wf_tblk_single tr"

lemma proc_wf_tr_single: 
  assumes "big_step C s tr s'"
  shows "wf_tr_single tr"
  using assms
  by (induction rule: big_step.induct, simp_all add: wf_waitblk)



end


