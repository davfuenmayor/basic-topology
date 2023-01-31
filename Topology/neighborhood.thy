theory neighborhood
  imports "../TBAs/closure_algebra"
begin

(**The following four conditions characterize a neighborhood relation/function
as a centered proper filter.*)
definition Nbhd_1::"('w,'w \<sigma>)\<rho> \<Rightarrow> bool" ("Nbhd_1") 
  where "Nbhd_1 F \<equiv> \<forall>x. meet_closed (F x)" (**filter-base*)
definition Nbhd_2::"('w,'w \<sigma>)\<rho> \<Rightarrow> bool" ("Nbhd_2") 
  where "Nbhd_2 F \<equiv> \<forall>x. upwards_closed (F x)" (**filter*)
definition Nbhd_3::"('w,'w \<sigma>)\<rho> \<Rightarrow> bool" ("Nbhd_3") 
  where "Nbhd_3 F \<equiv> \<forall>x. nonEmpty (F x)" (**proper filter(-base)*)
definition Nbhd_4::"('w,'w \<sigma>)\<rho> \<Rightarrow> bool" ("Nbhd_4") 
  where "Nbhd_4 F \<equiv> \<forall>x N. F x N \<longrightarrow> N x" (**centered*)

abbreviation Nbhd_all::"('w,'w \<sigma>)\<rho> \<Rightarrow> bool" ("\<NN>")
  where "\<NN> F \<equiv> Nbhd_1 F \<and> Nbhd_2 F \<and> Nbhd_3 F \<and> Nbhd_4 F"

(**Neighborhood functions are useful to introduce the notions of adherent (aka. closure)
 and accumulation (aka. limit) points of a set (wrt. a neighborhood function).*)
definition adherent_points::"('w,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("ADH[_]") 
  where "ADH[F] A \<equiv> \<lambda>p. \<forall>N. F p N \<longrightarrow> \<not>Disj N A"
definition accumulation_points::"('w,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("ACC[_]") 
  where "ACC[F] A \<equiv> \<lambda>p. \<forall>N. F p N \<longrightarrow> \<not>Disj N (A \<^bold>\<leftharpoonup> {p})"

(**We can in fact easily define a neighborhood function given a closure operator.*)
definition Nbhd_Cl::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w,'w \<sigma>)\<rho>" ("\<N>[_]") 
  where "\<N>[\<C>] \<equiv> \<I>[\<C>]\<Zcat>"

(**We prove below that in doing this the characterising neighborhood conditions are satisfied.*)
lemma nbhd_prop1: "Cl_1' \<C> \<Longrightarrow> Nbhd_1 \<N>[\<C>]" unfolding Nbhd_1_def Nbhd_Cl_def swap_def op_dual_def by (smt (z3) ADDI_a_def BA_deMorgan2 compl_def join_def meet_closed_def subset_def)
lemma nbhd_prop2: "MONO \<C> \<Longrightarrow> Nbhd_2 \<N>[\<C>]" unfolding Nbhd_2_def Nbhd_Cl_def swap_def op_dual_def MONO_def subset_def by (smt (z3) BA_deMorgan1 L9 compl_def meet_def setequ_equ upwards_closed_def)
lemma nbhd_prop3: "Cl_3 \<C> \<Longrightarrow> Nbhd_3 \<N>[\<C>]" by (metis DNRM_def NOR_dual1 Nbhd_Cl_def swap_def Nbhd_3_def setequ_equ top_def)
lemma nbhd_prop4: "Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> Nbhd_4 \<N>[\<C>]" by (metis (mono_tags) CNTR_def EXPN_CNTR_dual2 Nbhd_Cl_def swap_def Nbhd_4_def subset_def)

(**Moreover, we can show under which (minimal) conditions the well-known characterisation of neighborhood
functions in terms of open sets obtains.*)
lemma nbhd_open1: "Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>p N. \<N>[\<C>] p N \<longrightarrow> (\<exists>E. Op[\<C>] E \<and> E \<preceq> N \<and> E p)" by (metis BA_cp BA_dn EXPN_def IDEM_a_def IDEM_char Int_Open Nbhd_Cl_def base.swap_def op_dual_def)
lemma nbhd_open2: "MONO \<C> \<Longrightarrow> \<forall>p N. (\<exists>E. Op[\<C>] E \<and> E \<preceq> N \<and> E p) \<longrightarrow> \<N>[\<C>] p N" unfolding Nbhd_Cl_def swap_def by (metis MONO_def MONO_dual fixpoint_pred_def setequ_equ subset_def)
lemma nbhd_open: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow>
                 \<forall>p. \<N>[\<C>] p = (\<lambda>N. (\<exists>E. Op[\<C>] E \<and> E \<preceq> N \<and> E p))" by (meson nbhd_open1 nbhd_open2)

(**We can also verify (using minimal conditions) the characterization of open sets by neighborhoods.*)
(**Every open set is a neighborhood of all (and only) of its points.*)
lemma open_nbhd1: "\<forall>N. Op[\<C>] N \<longrightarrow> (\<forall>x. N x \<longleftrightarrow> \<N>[\<C>] x N)"  by (simp add: Nbhd_Cl_def swap_def fixpoint_pred_def setequ_equ)
(**If a set is a neighborhood of all of its points then it is open.*)
lemma open_nbhd2: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> \<forall>N. (\<forall>x. N x \<longrightarrow> \<N>[\<C>] x N) \<longrightarrow> Op[\<C>] N" by (metis (mono_tags) CNTR_def EXPN_CNTR_dual2 Nbhd_Cl_def base.swap_def fixpoint_pred_def setequ_def subset_def)
lemma open_nbhd: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> \<forall>N. Op[\<C>] N = (\<forall>x. N x \<longrightarrow> \<N>[\<C>] x N)" by (metis open_nbhd1 open_nbhd2)


(**Having a closure operator allows for an alternative characterization of the set of limit points*)
definition limit::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("limit[_]")
  where "limit[\<C>] A \<equiv> \<lambda>w. \<C> (A \<^bold>\<leftharpoonup> {w}) w"

lemma "MONO \<C> \<Longrightarrow> limit[\<C>] = ACC[\<N>[\<C>]]" 
  unfolding limit_def accumulation_points_def Nbhd_Cl_def swap_def 
  by (simp add: CI_Disj_rel) 

end