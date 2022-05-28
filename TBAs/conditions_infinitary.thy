theory conditions_infinitary
  imports conditions boolean_algebra_infinitary
begin

(**We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.*)

(**Distribution over infinite meets (infima) or infinite multiplicativity (iMULT).*)
definition iMULT::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("iMULT")
  where "iMULT \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<approx> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>" 
definition iMULT_a::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("iMULT\<^sup>a")
  where "iMULT\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<preceq> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"
definition iMULT_b::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("iMULT\<^sup>b")
  where "iMULT\<^sup>b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<succeq> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"

declare iMULT_def[cond] iMULT_a_def[cond] iMULT_b_def[cond]

(**Distribution over infinite joins (suprema) or infinite additivity (iADDI).*)
definition iADDI::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("iADDI")
  where "iADDI \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<approx> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_a::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("iADDI\<^sup>a")
  where "iADDI\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_b::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("iADDI\<^sup>b")
  where "iADDI\<^sup>b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<succeq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>"

declare iADDI_def[cond] iADDI_a_def[cond] iADDI_b_def[cond]

lemma iMULT_char: "iMULT \<phi> = (iMULT\<^sup>a \<phi> \<and> iMULT\<^sup>b \<phi>)" using iMULT_a_def iMULT_b_def iMULT_def by (metis setequ_def)
lemma iADDI_char: "iADDI \<phi> = (iADDI\<^sup>a \<phi> \<and> iADDI\<^sup>b \<phi>)" using iADDI_a_def iADDI_b_def iADDI_def by (metis setequ_def)

(**MULT-a and iMULT-a are in fact equivalent.*)
lemma iMULTa_equ: "iMULT\<^sup>a \<phi> = MULT\<^sup>a \<phi>" proof -
  have lr: "iMULT\<^sup>a \<phi> \<Longrightarrow> MULT\<^sup>a \<phi>" proof - (*maybe prove as a one-liner by instantiating iMULT_a_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume imulta: "iMULT\<^sup>a \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>" (* for some reason Isabelle doesn't like 'w as variable. Why?*)
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    from imulta have "\<phi>(\<^bold>\<And>?S) \<^bold>\<preceq> \<Q>\<^sup>\<forall>[\<lparr>?S\<rparr>] \<phi>" unfolding iMULT_a_def by (smt (verit) iconn Ra_restr_all setequ_equ subset_def)
    moreover have "\<^bold>\<And>?S = A \<^bold>\<and> B" unfolding infimum_def meet_def by blast 
    moreover have "\<Q>\<^sup>\<forall>[\<lparr>?S\<rparr>] \<phi> = (\<phi> A) \<^bold>\<and> (\<phi> B)" unfolding meet_def iconn by auto
    ultimately have "\<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" by smt
  } thus ?thesis by (simp add: MULT_a_def) qed
  have rl: "MULT\<^sup>a \<phi> \<Longrightarrow> iMULT\<^sup>a \<phi>"by (smt (verit, del_insts) MONO_MULTa MONO_def iMULT_a_def img_dir_def inf_char)
  from lr rl show ?thesis by auto
qed
(**ADDI-b and iADDI-b are also equivalent.*)
lemma iADDIb_equ: "iADDI\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" proof -
  have lr: "iADDI\<^sup>b \<phi> \<Longrightarrow> ADDI\<^sup>b \<phi>" proof - (*maybe prove as a one-liner by instantiating iADDI_b_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume iaddib: "iADDI\<^sup>b \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>"
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    from iaddib have "\<phi>(\<^bold>\<Or>?S) \<^bold>\<succeq> \<Q>\<^sup>\<exists>[\<lparr>?S\<rparr>] \<phi>" unfolding iADDI_b_def by (smt (z3) iconn img_dir_def subset_def)
    moreover have "\<^bold>\<Or>?S = A \<^bold>\<or> B" unfolding supremum_def join_def by auto
    moreover have "\<Q>\<^sup>\<exists>[\<lparr>?S\<rparr>] \<phi> = (\<phi> A) \<^bold>\<or> (\<phi> B)" unfolding join_def iconn by auto
    ultimately have "\<phi>(A \<^bold>\<or> B) \<^bold>\<succeq> (\<phi> A) \<^bold>\<or> (\<phi> B)" by smt
  } thus ?thesis by (simp add: ADDI_b_def) qed
  have rl: "ADDI\<^sup>b \<phi> \<Longrightarrow> iADDI\<^sup>b \<phi>" unfolding iADDI_b_def MONO_ADDIb by (smt (verit, del_insts) MONO_def img_dir_def sup_char)
  from lr rl show ?thesis by auto
qed

(**Thus we have that MONO, MULT-a/iMULT-a and ADDI-b/iADDI-b are all equivalent.*)
lemma MONO_iADDIb: "iADDI\<^sup>b \<phi> = MONO \<phi>" unfolding MONO_ADDIb iADDIb_equ by simp
lemma MONO_iMULTa: "iMULT\<^sup>a \<phi> = MONO \<phi>" unfolding MONO_MULTa iMULTa_equ by simp


(**Below we prove several duality relationships between iADDI(a/b) and iMULT(a/b).*)

(**The first duality is an easy corollary of the previous equivalence.*)
lemma iMULTa_iADDIb_dual1: "iMULT\<^sup>a \<phi> = iADDI\<^sup>b \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual1 iADDIb_equ iMULTa_equ)
lemma iMULTa_iADDIb_dual2: "iADDI\<^sup>b \<phi> = iMULT\<^sup>a \<phi>\<^sup>d" using MONO_dual MONO_iADDIb MONO_iMULTa by auto

(*these two lemmas below are introduced for technical reasons (as stepping stones)*)
lemma iADDIa_impl_iMULTb: "\<forall>\<phi>. iADDI\<^sup>a \<phi> \<longrightarrow> iMULT\<^sup>b \<phi>\<^sup>d" unfolding iADDI_a_def iMULT_b_def using iDM_a iDM_b Ra_dual1 using order compl_def op_dual_def by (smt (verit, del_insts) setequ_equ)
lemma iMULTb_impl_iADDIa: "\<forall>\<phi>. iMULT\<^sup>b \<phi> \<longrightarrow> iADDI\<^sup>a \<phi>\<^sup>d" unfolding iADDI_a_def iMULT_b_def by (smt (verit, del_insts) Ra_dual3 compl_def iDM_b infimum_def op_dual_def setequ_equ subset_def)

(**Duality between iADDI-a and iMULT-b.*)
lemma iADDIa_iMULTb_dual1: "iADDI\<^sup>a \<phi> = iMULT\<^sup>b \<phi>\<^sup>d" by (metis dual_invol iADDIa_impl_iMULTb iMULTb_impl_iADDIa op_equal_equ)
lemma iADDIa_iMULTb_dual2: "iMULT\<^sup>b \<phi> = iADDI\<^sup>a \<phi>\<^sup>d" by (metis dual_invol iADDIa_iMULTb_dual1 op_equal_equ) 

(**Duality between iADDI and iMULT.*)
lemma iADDI_iMULT_dual1: "iADDI \<phi> = iMULT \<phi>\<^sup>d" by (meson MONO_dual MONO_iADDIb MONO_iMULTa iADDI_char iADDIa_iMULTb_dual1 iMULT_char)
lemma iADDI_iMULT_dual2: "iMULT \<phi> = iADDI \<phi>\<^sup>d" by (metis dual_invol iADDI_iMULT_dual1 op_equal_equ)

(**Other (not really surprising) result:*)
lemma iMULT_DNRM: "iMULT \<phi> \<Longrightarrow> DNRM \<phi>" by (metis (no_types) BA_dn DNRM_def NORM_def bottom_def comp_invol fp_c_rel fp_rel iADDI_def iADDI_iMULT_dual2 img_dir_def ofp_c ofp_invol op_compl_def op_dual_def op_equal_equ setequ_def setequ_equ subset_def sup_char)
lemma iADDI_NORM: "iADDI \<phi> \<Longrightarrow> NORM \<phi>" by (simp add: NOR_dual1 iADDI_iMULT_dual1 iMULT_DNRM)

(**Interestingly, we can show that suitable conditions on an operation can make the set
of its fixed points closed under infinite meets/joins.*)
lemma fp_inf_closed_cond1: "iMULT \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)" unfolding iMULT_def infimum_closed_def using Ra_restr_all by (smt (z3) fixpoint_pred_def iconn setequ_char)
lemma fp_inf_closed_cond2: "iMULT\<^sup>b \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)" by (smt (z3) iconn CNTR_def Ra_restr_all fixpoint_pred_def iMULT_b_def infimum_closed_def infimum_def setequ_def subset_def)
lemma fp_inf_closed_cond3: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)" by (smt (z3) EXPN_def MONO_def fixpoint_pred_def inf_char infimum_closed_def setequ_def setequ_equ)
lemma "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> infimum_closed (\<lbrakk>\<phi> -\<rbrakk>)" by (simp add: IDEM_Ra_fp fp_inf_closed_cond3)

lemma fp_sup_closed_cond1: "iADDI \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" unfolding iADDI_def supremum_closed_def using Ra_restr_ex by (smt (z3) fixpoint_pred_def iconn setequ_char)
lemma fp_sup_closed_cond2: "iADDI\<^sup>a \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" by (smt (verit, best) BA_dn EXPN_CNTR_dual2 dom_compl_def fp_d fp_inf_closed_cond2 iADDIa_impl_iMULTb iDM_b infimum_closed_def setequ_equ supremum_closed_def)
lemma fp_sup_closed_cond3: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" by (metis CNTR_impl_NORM EXPN_CNTR_dual2 MONO_dual NORM_def dual_invol fixpoint_pred_def fp_inf_closed_cond3 fp_inf_sup_closed_dual inf_closed_char op_equal_equ sup_closed_char)
lemma "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> supremum_closed (\<lbrakk>\<phi> -\<rbrakk>)" by (simp add: IDEM_Ra_fp fp_sup_closed_cond3)

(**OTOH, the converse conjectures have (finite) countermodels. They need additional assumptions.*)
lemma "infimum_closed (fp \<phi>) \<Longrightarrow> iMULT \<phi>" nitpick oops
lemma "supremum_closed (fp \<phi>) \<Longrightarrow> iADDI \<phi>" nitpick oops
lemma fp_inf_closed_iMULT: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> infimum_closed (fp \<phi>) \<Longrightarrow> iMULT \<phi>"
proof -
  assume mono: "MONO \<phi>" and cntr: "CNTR \<phi>" and idem:"IDEM\<^sup>a \<phi>" and ic:"infimum_closed (fp \<phi>)"
  { fix S
    from ic have "\<forall>D. D \<sqsubseteq> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<And>D)" unfolding infimum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<^bold>\<approx> \<phi> X)) \<longrightarrow> \<^bold>\<And>D \<^bold>\<approx> \<phi> \<^bold>\<And>D" by (simp add: fixpoint_pred_def setequ_equ)
    moreover from idem have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<^bold>\<approx> \<phi> X))" by (metis (mono_tags, lifting) CNTR_def IDEM_a_def cntr img_dir_def setequ_def)
    ultimately have aux: "\<^bold>\<And>(\<lbrakk>\<phi> S\<rbrakk>) \<^bold>\<approx> \<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    from cntr have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<preceq> \<^bold>\<And>S" by (smt (verit, best) CNTR_def img_dir_def infimum_def subset_def)
    hence "\<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>) \<^bold>\<preceq> \<phi>(\<^bold>\<And>S)" using mono by (simp add: MONO_def) 
    from this aux have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<preceq> \<phi>(\<^bold>\<And>S)" by (simp add: setequ_equ)
  } hence "\<forall>S. \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<preceq> \<phi>(\<^bold>\<And>S)" by (rule allI)
  thus ?thesis using MONO_iMULTa iMULT_b_def iMULT_char mono by blast
qed
lemma fp_sup_closed_iADDI: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> supremum_closed (fp \<phi>) \<Longrightarrow> iADDI \<phi>" 
   unfolding MONO_def EXPN_def IDEM_def supremum_closed_def iADDI_def by (metis EXPN_CNTR_dual2 EXPN_def IDEM_dual2 MONO_def MONO_dual fp_inf_closed_iMULT fp_sup_inf_closed_dual iADDI_def iADDI_iMULT_dual1 supremum_closed_def)
(*proof -
  assume mono: "MONO \<phi>" and expn: "EXPN \<phi>" and idem:"IDEM\<^sup>b \<phi>" and sc:"supremum_closed (fp \<phi>)"
  { fix S
    from sc have "\<forall>D. D \<sqsubseteq> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<Or>D)" unfolding supremum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<^bold>\<approx> \<phi> X)) \<longrightarrow> \<^bold>\<Or>D \<^bold>\<approx> \<phi> \<^bold>\<Or>D" by (simp add: fixpoint_pred_def setequ_def)
    moreover have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<^bold>\<approx> \<phi> X))" by (metis (mono_tags, lifting) EXPN_def IDEM_b_def expn idem img_dir_def setequ_def)
    ultimately have aux: "\<^bold>\<Or>(\<lbrakk>\<phi> S\<rbrakk>) \<^bold>\<approx> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    have "\<^bold>\<Or>S \<^bold>\<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis EXPN_CNTR_dual2 EXPN_def IDEM_dual2 MONO_dual expn fp_inf_closed_iMULT fp_sup_inf_closed_dual iADDI_def iADDI_iMULT_dual1 idem mono sc setequ_equ)
    hence "\<phi>(\<^bold>\<Or>S) \<^bold>\<preceq> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" using mono by (simp add: MONO_def) 
    from this aux have "\<phi>(\<^bold>\<Or>S) \<^bold>\<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis setequ_equ)
  } hence "\<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (rule allI)
  thus ?thesis by (simp add: MONO_iADDIb iADDI_a_def iADDI_char mono)
qed*)

end