theory conditions
  imports boolean_algebra
begin

(** We define and interrelate some useful axiomatic conditions on unary operations
(operators) having a 'w-parametric type @{type "('w \<sigma> \<Rightarrow> 'w \<sigma>)"} (i.e. @{type "('w\<Rightarrow>bool)\<Rightarrow>('w\<Rightarrow>bool)"}).
Those operations are aimed at extending a Boolean algebra towards different sorts of topological Boolean algebras.*)

named_theorems cond

(**Monotonicity (MONO).*)
definition MONO::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MONO")
  where "MONO \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> \<phi> A \<preceq> \<phi> B"

declare MONO_def[cond]

lemma MONO_dual: "MONO \<phi> = MONO \<phi>\<^sup>d" by (smt (verit, best) BA_cp MONO_def dual_invol op_dual_def op_equal_equ)
lemma MONO_ant: "MONO \<phi> \<Longrightarrow> \<forall>A B C. A \<preceq> B \<longrightarrow> \<phi>(B \<^bold>\<rightarrow> C) \<preceq> \<phi>(A \<^bold>\<rightarrow> C)" by (metis (full_types) MONO_def impl_def subset_def)
lemma MONO_cons: "MONO \<phi> \<Longrightarrow> \<forall>A B C. A \<preceq> B \<longrightarrow> \<phi>(C \<^bold>\<rightarrow> A) \<preceq> \<phi>(C \<^bold>\<rightarrow> B)" by (metis (full_types) MONO_def impl_def subset_def)


(**Expansive/extensive (EXPN) and its dual contractive (CNTR).*)
definition EXPN::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("EXPN")
  where "EXPN \<phi>  \<equiv> \<forall>A. A \<preceq> \<phi> A"
definition CNTR::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("CNTR")
  where "CNTR \<phi> \<equiv> \<forall>A. \<phi> A \<preceq> A"

declare EXPN_def[cond] CNTR_def[cond]

lemma EXPN_CNTR_dual1: "EXPN \<phi> = CNTR \<phi>\<^sup>d" by (metis BA_cp BA_dn CNTR_def EXPN_def op_dual_def) 
lemma EXPN_CNTR_dual2: "EXPN \<phi> = CNTR \<phi>\<^sup>d" by (simp add: EXPN_CNTR_dual1)

(**Normality (NORM) and its dual (DNRM).*)
definition NORM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("NORM")
  where "NORM \<phi>  \<equiv> (\<phi> \<^bold>\<bottom>) \<approx> \<^bold>\<bottom>"
definition DNRM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("DNRM")
  where "DNRM \<phi> \<equiv> (\<phi> \<^bold>\<top>) \<approx> \<^bold>\<top>" 

declare NORM_def[cond] DNRM_def[cond]

lemma NOR_dual1: "NORM \<phi> = DNRM \<phi>\<^sup>d" unfolding NORM_def DNRM_def op_dual_def order conn by simp
lemma NOR_dual2: "DNRM \<phi> = NORM \<phi>\<^sup>d" by (metis NOR_dual1 dual_invol op_equal_equ)

(**EXPN (resp. CNTR) entail DNRM (resp. NORM).*)
lemma EXPN_impl_DNRM: "EXPN \<phi> \<Longrightarrow> DNRM \<phi>" by (simp add: EXPN_def DNRM_def setequ_def subset_def top_def)
lemma CNTR_impl_NORM: "CNTR \<phi> \<Longrightarrow> NORM \<phi>" by (metis NORM_def bottom_def CNTR_def setequ_def subset_def)

(**Idempotence (IDEM).*)
definition IDEM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEM") 
  where "IDEM \<phi>  \<equiv> \<forall>A. (\<phi> A) \<approx> \<phi>(\<phi> A)"
definition IDEM_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEM\<^sup>a") 
  where "IDEM_a \<phi> \<equiv> \<forall>A. (\<phi> A) \<preceq> \<phi>(\<phi> A)"
definition IDEM_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEM\<^sup>b") 
  where "IDEM_b \<phi> \<equiv> \<forall>A. (\<phi> A) \<succeq> \<phi>(\<phi> A)"
lemma IDEM_char: "IDEM \<phi> = (IDEM_a \<phi> \<and> IDEM_b \<phi>)" using IDEM_def IDEM_a_def IDEM_b_def by (metis setequ_def) 

declare IDEM_def[cond] IDEM_a_def[cond] IDEM_b_def[cond]

lemma IDEM_dual1: "IDEM\<^sup>a \<phi> = IDEM\<^sup>b \<phi>\<^sup>d" unfolding IDEM_a_def IDEM_b_def by (smt (verit, best) BA_cp dual_invol ofp_c ofp_d ofp_invol op_compl_def op_dual_def op_equal_equ)
lemma IDEM_dual2: "IDEM\<^sup>b \<phi> = IDEM\<^sup>a \<phi>\<^sup>d" by (metis IDEM_dual1 dual_invol op_equal_equ)
lemma IDEM_dual: "IDEM \<phi> = IDEM \<phi>\<^sup>d" unfolding IDEM_def by (metis IDEM_a_def IDEM_b_def IDEM_dual1 IDEM_dual2 setequ_def)

(**EXPN (resp. CNTR) entail IDEM-a (resp. IDEM-b).*)
lemma EXPN_impl_IDEM_a: "EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi>" by (simp add: EXPN_def IDEM_a_def)
lemma CNTR_impl_IDEM_b: "CNTR \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi>" by (simp add: CNTR_def IDEM_b_def)

(**IDEM has the property of collapsing the range and the set of fixed-points of an operator*)
lemma IDEM_Ra_fp: "IDEM \<phi> \<Longrightarrow> \<lbrakk>\<phi> -\<rbrakk> = fp \<phi>" unfolding IDEM_def fixpoint_pred_def setequ_equ range_def by fastforce

(**Distribution over joins or additivity (ADDI).*)
definition ADDI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDI")
  where "ADDI \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<approx> (\<phi> A) \<^bold>\<or> (\<phi> B)" 
definition ADDI_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDI\<^sup>a")
  where "ADDI\<^sup>a \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<preceq> (\<phi> A) \<^bold>\<or> (\<phi> B)"
definition ADDI_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDI\<^sup>b")
  where "ADDI\<^sup>b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<succeq> (\<phi> A) \<^bold>\<or> (\<phi> B)" 

declare ADDI_def[cond] ADDI_a_def[cond] ADDI_b_def[cond]

(**Distribution over meets or multiplicativity (MULT).*)
definition MULT::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULT") 
  where "MULT \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<approx> (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition MULT_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULT\<^sup>a")
  where "MULT\<^sup>a \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition MULT_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULT\<^sup>b")
  where "MULT_b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<succeq> (\<phi> A) \<^bold>\<and> (\<phi> B)"

declare MULT_def[cond] MULT_a_def[cond] MULT_b_def[cond]

lemma ADDI_char: "ADDI \<phi> = (ADDI\<^sup>a \<phi> \<and> ADDI\<^sup>b \<phi>)" using ADDI_a_def ADDI_b_def ADDI_def by (metis setequ_def)
lemma MULT_char: "MULT \<phi> = (MULT\<^sup>a \<phi> \<and> MULT\<^sup>b \<phi>)" using MULT_a_def MULT_b_def MULT_def by (metis setequ_def)

(**MONO, MULT-a and ADDI-b are equivalent.*)
lemma MONO_MULTa: "MULT\<^sup>a \<phi> = MONO \<phi>" by (smt (verit, ccfv_threshold) L10 L3 L4 L5 L8 MONO_def MULT_a_def setequ_equ subset_transitive transitive_def)
lemma MONO_ADDIb: "ADDI\<^sup>b \<phi> = MONO \<phi>" unfolding MONO_def ADDI_b_def by (smt (verit, del_insts) L9 join_def setequ_equ subset_def)

(**Below we prove several duality relationships between ADDI(a/b) and MULT(a/b).*)

(**The first duality is an easy corollary of the previous equivalence.*)
lemma MULTa_ADDIb_dual1: "MULT\<^sup>a \<phi> = ADDI\<^sup>b \<phi>\<^sup>d" using MONO_ADDIb MONO_MULTa MONO_dual by auto
lemma MULTa_ADDIb_dual2: "ADDI\<^sup>b \<phi> = MULT\<^sup>a \<phi>\<^sup>d" using MONO_ADDIb MONO_MULTa MONO_dual by auto

(*these two lemmas below are introduced for technical reasons (as stepping stones)*)
lemma MULTb_impl_ADDIa: "\<forall>\<phi>. MULT\<^sup>b \<phi> \<longrightarrow> ADDI\<^sup>a \<phi>\<^sup>d" unfolding MULT_b_def ADDI_a_def op_dual_def order conn by auto
lemma ADDIa_impl_MULTb: "\<forall>\<phi>. ADDI\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>b \<phi>\<^sup>d" proof -
    { fix \<phi>::"('w \<sigma> \<Rightarrow> 'w \<sigma>)" { assume cl1a: "ADDI\<^sup>a \<phi>" 
      { fix A and B
        have "\<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>(A \<^bold>\<and> B)) \<approx> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" unfolding conn order by simp
        moreover from cl1a have "\<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>B)) \<preceq> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" using ADDI_a_def BA_cp by blast
        ultimately have "\<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>A)) \<^bold>\<and> \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>B)) \<preceq> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>(A \<^bold>\<and> B))" unfolding conn by simp
        hence "(\<phi>\<^sup>d A) \<^bold>\<and> (\<phi>\<^sup>d B) \<preceq> (\<phi>\<^sup>d (A \<^bold>\<and> B))" unfolding op_dual_def by simp
      } hence "MULT\<^sup>b \<phi>\<^sup>d" using MULT_b_def by blast
    } hence "ADDI\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>b \<phi>\<^sup>d" by simp
} thus "\<forall>\<phi>. ADDI\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>b \<phi>\<^sup>d" by blast qed

(**Duality between ADDI-a and MULT-b.*)
lemma ADDIa_MULTb_dual1: "ADDI\<^sup>a \<phi> = MULT\<^sup>b \<phi>\<^sup>d" by (metis dual_invol op_equal_equ MULTb_impl_ADDIa ADDIa_impl_MULTb)
lemma ADDIa_MULTb_dual2: "MULT\<^sup>b \<phi> = ADDI\<^sup>a \<phi>\<^sup>d" by (metis ADDIa_MULTb_dual1 dual_invol op_equal_equ)

(**Duality between ADDI and MULT.*)
lemma ADDI_MULT_dual1: "ADDI \<phi> = MULT \<phi>\<^sup>d" using ADDI_char ADDIa_MULTb_dual1 MULT_char MULTa_ADDIb_dual2 by blast
lemma ADDI_MULT_dual2: "MULT \<phi> = ADDI \<phi>\<^sup>d" using ADDI_char ADDIa_MULTb_dual2 MULT_char MULTa_ADDIb_dual1 by blast


(**We verify properties regarding closure over meets/joins for fixed-points.*)

(**MULT and ADDI imply meet-closed and join-closed respectively (the converse requires additional assumptions)*)
lemma MULT_meetclosed: "MULT \<phi> \<Longrightarrow> meet_closed (fp \<phi>)" by (simp add: MULT_def fixpoint_pred_def meet_closed_def setequ_equ)
lemma "meet_closed (fp \<phi>) \<Longrightarrow> MULT \<phi>" nitpick oops (*countermodel*)
lemma meetclosed_MULT: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> meet_closed (fp \<phi>) \<Longrightarrow> MULT \<phi>"
  unfolding MONO_def CNTR_def IDEM_a_def meet_closed_def by (smt (z3) L12 L8 MULT_def fixpoint_pred_def meet_def setequ_def setequ_equ subset_def)

lemma ADDI_joinclosed: "ADDI \<phi> \<Longrightarrow> join_closed (fp \<phi>)" by (simp add: ADDI_def fixpoint_pred_def join_closed_def setequ_equ)
lemma "join_closed (fp \<phi>) \<Longrightarrow> ADDI \<phi>" nitpick oops (*countermodel*)
lemma joinclosed_ADDI: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> join_closed (fp \<phi>) \<Longrightarrow> ADDI \<phi>" 
  by (smt (verit) ADDI_def BA_cp BA_deMorgan1 BA_dn EXPN_CNTR_dual2 IDEM_dual2 MONO_dual MULT_a_def MULT_b_def MULT_char dual_invol fp_join_meet_closed_dual meetclosed_MULT op_dual_def op_equal_equ setequ_def)

(**Assuming MONO, we have that EXPN (resp. CNTR) implies meet-closed (resp. join-closed) for @{text "\<phi>"}'s fixed-points.*)
lemma EXPN_meetclosed: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> meet_closed (fp \<phi>)" 
  by (smt (verit) EXPN_def MONO_MULTa MULT_a_def fixpoint_pred_def meet_closed_def setequ_def setequ_equ)
lemma CNTR_meetclosed: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> join_closed (fp \<phi>)" 
  by (smt (verit, ccfv_threshold) ADDI_b_def CNTR_def MONO_ADDIb fixpoint_pred_def join_closed_def setequ_def setequ_equ)
(**Further assuming IDEM the above results can be stated to the whole range of @{text "\<phi>"}.*)
lemma "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> meet_closed (\<lbrakk>\<phi> -\<rbrakk>)" 
  by (smt (verit, ccfv_threshold) EXPN_def IDEM_Ra_fp L3 L4 L5 L8 MONO_def fixpoint_pred_def meet_closed_def setequ_def setequ_equ)
lemma "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> join_closed (\<lbrakk>\<phi> -\<rbrakk>)" 
  by (smt (verit, del_insts) BA_deMorgan1 BA_dn CNTR_def IDEM_Ra_fp L3 L4 L5 L7 MONO_def fixpoint_pred_def join_closed_def setequ_def setequ_equ)


(**Properties regarding distribution over implication/difference.*)
definition DISTR_impl_inc::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<rightarrow>\<^sup>i")
  where "DISTR\<^sub>\<rightarrow>\<^sup>i \<phi> \<equiv> \<forall>A B. \<phi> (A \<^bold>\<rightarrow> B) \<preceq> (\<phi> A) \<^bold>\<rightarrow> (\<phi> B)" 
definition DISTR_impl_dec::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<rightarrow>\<^sup>d")
  where "DISTR\<^sub>\<rightarrow>\<^sup>d \<phi> \<equiv> \<forall>A B. \<phi> (A \<^bold>\<rightarrow> B) \<succeq> (\<phi> A) \<^bold>\<rightarrow> (\<phi> B)"

definition DISTR_diff_inc::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<leftharpoonup>\<^sup>i")
  where "DISTR\<^sub>\<leftharpoonup>\<^sup>i \<phi> \<equiv> \<forall>A B. \<phi> (A \<^bold>\<leftharpoonup> B) \<preceq> (\<phi> A) \<^bold>\<leftharpoonup> (\<phi> B)" 
definition DISTR_diff_dec::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<leftharpoonup>\<^sup>d")
  where "DISTR\<^sub>\<leftharpoonup>\<^sup>d \<phi> \<equiv> \<forall>A B. \<phi> (A \<^bold>\<leftharpoonup> B) \<succeq> (\<phi> A) \<^bold>\<leftharpoonup> (\<phi> B)" 

lemma DISTR_diff_inc_prop: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> DISTR\<^sub>\<leftharpoonup>\<^sup>i \<phi>" unfolding DISTR_diff_inc_def CNTR_def by (smt (verit) MONO_def diff_def subset_def)
lemma DISTR_impl_inc_prop: "MULT \<phi> \<Longrightarrow> DISTR\<^sub>\<rightarrow>\<^sup>i \<phi>" proof -
  assume mult: "MULT \<phi>"
  { fix a::"'a \<sigma>" and b::"'a \<sigma>"
    have "a \<^bold>\<and> b = a \<^bold>\<and> (a \<^bold>\<rightarrow> b)" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<and> b) = \<phi>(a \<^bold>\<and> (a \<^bold>\<rightarrow> b))" by simp
    moreover from mult have "\<phi>(a \<^bold>\<and> b) \<approx> \<phi> a \<^bold>\<and> \<phi> b" by (simp add: MULT_def)
    moreover from mult have "\<phi>(a \<^bold>\<and> (a \<^bold>\<rightarrow> b)) \<approx> \<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b)" by (simp add: MULT_def)
    ultimately have "\<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b) \<approx> \<phi> a \<^bold>\<and> \<phi> b" by (simp add: setequ_equ)
    hence "\<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b) \<approx> \<phi> a \<^bold>\<and> (\<phi> a \<^bold>\<rightarrow> \<phi> b)" unfolding conn order by blast
    hence "\<phi>(a \<^bold>\<rightarrow> b) \<preceq> \<phi> a \<^bold>\<rightarrow> \<phi> b" unfolding conn order by blast
  } thus ?thesis by (simp add: DISTR_impl_inc_def)
qed
lemma DISTR_impl_dec_prop: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> DISTR\<^sub>\<rightarrow>\<^sup>d \<phi>" by (smt (verit, best) DISTR_impl_dec_def EXPN_def MONO_def impl_def subset_def)
lemma DISTR_diff_dec_prop: "ADDI \<phi> \<Longrightarrow> DISTR\<^sub>\<leftharpoonup>\<^sup>d \<phi>" proof -
  assume addi: "ADDI \<phi>"
  { fix a::"'a \<sigma>" and b::"'a \<sigma>"
    have "a \<^bold>\<or> b = (a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<or> b) = \<phi>((a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b)" by simp
    moreover from addi have "\<phi>(a \<^bold>\<or> b) \<approx> \<phi> a \<^bold>\<or> \<phi> b" by (simp add: ADDI_def)
    moreover from addi have "\<phi>((a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b) \<approx> \<phi> (a \<^bold>\<leftharpoonup> b) \<^bold>\<or> (\<phi> b)" by (simp add: ADDI_def)
    ultimately have "\<phi> a \<^bold>\<or> \<phi> b \<approx> \<phi>(a \<^bold>\<leftharpoonup> b) \<^bold>\<or> \<phi> b" unfolding order by metis
    hence "(\<phi> a \<^bold>\<leftharpoonup> \<phi> b) \<^bold>\<or> \<phi> b \<approx> \<phi>(a \<^bold>\<leftharpoonup> b) \<^bold>\<or> \<phi> b" unfolding conn order by blast
    hence "\<phi> a \<^bold>\<leftharpoonup> \<phi> b \<preceq> \<phi> (a \<^bold>\<leftharpoonup> b)" unfolding conn order by blast
  } thus ?thesis by (simp add: DISTR_diff_dec_def)
qed

lemma ADDI_distr_impl_dual: "ADDI \<phi> \<Longrightarrow> \<forall>A B. \<phi>\<^sup>d(A \<^bold>\<rightarrow> B) \<preceq> \<phi> A \<^bold>\<rightarrow> \<phi> B" by (smt (verit) BA_cp BA_dn DISTR_diff_dec_def DISTR_diff_dec_prop impl_diff_rel op_dual_def setequ_equ)
lemma MULT_distr_diff_dual: "MULT \<phi> \<Longrightarrow> \<forall>A B. \<phi>\<^sup>d(A \<^bold>\<leftharpoonup> B) \<succeq> \<phi> A \<^bold>\<leftharpoonup> \<phi> B" by (smt (verit) BA_cp BA_dn DISTR_impl_inc_def DISTR_impl_inc_prop impl_diff_rel op_dual_def setequ_equ)
lemma ADDI_distr_diff_dual: "ADDI \<phi> \<Longrightarrow> \<forall>A B. \<phi>(A \<^bold>\<leftharpoonup> B) \<succeq> \<phi>\<^sup>d A \<^bold>\<leftharpoonup> \<phi>\<^sup>d B" by (smt (verit, ccfv_SIG) ADDI_MULT_dual1 BA_cp BA_dn DISTR_impl_inc_def DISTR_impl_inc_prop impl_diff_rel op_dual_def setequ_equ)
lemma MULT_distr_impl_dual: "MULT \<phi> \<Longrightarrow> \<forall>A B. \<phi>(A \<^bold>\<rightarrow> B) \<preceq> \<phi>\<^sup>d A \<^bold>\<rightarrow> \<phi>\<^sup>d B" by (metis ADDI_MULT_dual2 ADDI_distr_impl_dual dual_invol op_equal_equ)

end