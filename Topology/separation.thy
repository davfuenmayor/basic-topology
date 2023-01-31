theory separation
  imports "../TBAs/closure_algebra"
begin

(**Introduces a predicate for indicating that A and B are separated and proves some properties.*)
definition Sep ("Sep[_]") where "Sep[\<C>] A B \<equiv> Disj (\<C> A) B \<and> Disj (\<C> B) A"
lemma Sep_def2: "Sep[\<C>] A B = ((A \<^bold>\<and> \<C> B) \<^bold>\<or> (B \<^bold>\<and> \<C> A) \<approx> \<^bold>\<bottom>)" by (smt (verit, best) Disj_char Disj_def L7 Sep_def bottom_def join_def meet_def setequ_def subset_def)

lemma Sep_comm: "\<forall>A B. Sep[\<C>] A B \<longrightarrow> Sep[\<C>] B A" by (simp add: Sep_def)
lemma Sep_disj: "Cl_2 \<C> \<Longrightarrow> \<forall>A B. Sep[\<C>] A B \<longrightarrow> Disj A B" by (smt (verit, best) Disj_def EXPN_def Sep_def meet_def setequ_char subset_def)
lemma Sep_I: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>A. Sep[\<C>] (\<I>[\<C>] A) (\<I>[\<C>] (\<^bold>\<midarrow>A))" by (smt (verit, del_insts) BA_dn CI_Disj_rel_b Disj_I Disj_def Sep_def) 
lemma Sep_sub: "MONO \<C> \<Longrightarrow> \<forall>A B C D. Sep[\<C>] A B \<and> C \<preceq> A \<and> D \<preceq> B \<longrightarrow> Sep[\<C>] C D" using MONO_def unfolding Sep_def Disj_def conn by (smt (verit, best) setequ_char subset_def)
lemma Sep_Cl_diff: "MONO \<C>  \<Longrightarrow> \<forall>A B. Cl[\<C>](A) \<and> Cl[\<C>](B) \<longrightarrow> Sep[\<C>] (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" unfolding Disj_def MONO_def Sep_def fixpoint_pred_def setequ_char subset_def conn by (smt (z3))
lemma Sep_Op_diff: "MONO \<C> \<Longrightarrow> \<forall>A B. Op[\<C>](A) \<and> Op[\<C>](B) \<longrightarrow> Sep[\<C>] (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" proof -
  assume mono:"MONO \<C>"
  { fix A B 
    from mono have aux: "let M=\<^bold>\<midarrow>A ; N=\<^bold>\<midarrow>B in (Cl[\<C>](M) \<and> Cl[\<C>](N) \<longrightarrow> Sep[\<C>] (M \<^bold>\<leftharpoonup> N) (N \<^bold>\<leftharpoonup> M))" using Sep_Cl_diff by fastforce
    { assume "Op[\<C>](A) \<and> Op[\<C>](B)"
      hence "Cl[\<C>](\<^bold>\<midarrow>A) \<and> Cl[\<C>](\<^bold>\<midarrow>B)" using fp_d by blast
      hence "Sep[\<C>] (\<^bold>\<midarrow>A \<^bold>\<leftharpoonup> \<^bold>\<midarrow>B) (\<^bold>\<midarrow>B \<^bold>\<leftharpoonup> \<^bold>\<midarrow>A)" using mono aux unfolding conn by simp
      moreover have "(\<^bold>\<midarrow>A \<^bold>\<leftharpoonup> \<^bold>\<midarrow>B) \<approx> (B \<^bold>\<leftharpoonup> A)" unfolding conn setequ_char by blast
      moreover have "(\<^bold>\<midarrow>B \<^bold>\<leftharpoonup> \<^bold>\<midarrow>A) \<approx> (A \<^bold>\<leftharpoonup> B)" unfolding conn setequ_char by blast
      ultimately have "Sep[\<C>] (B \<^bold>\<leftharpoonup> A) (A \<^bold>\<leftharpoonup> B)" unfolding conn setequ_char by simp
      hence "Sep[\<C>] (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Sep_comm by blast
    } hence "Op[\<C>](A) \<and> Op[\<C>](B) \<longrightarrow> Sep[\<C>] (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" by (rule impI)
  } thus ?thesis by simp
qed
lemma Sep_Union: "Cl_1' \<C> \<Longrightarrow> \<forall>A B C. Sep[\<C>] A B \<and> Sep[\<C>] A C \<longrightarrow> Sep[\<C>] A (B \<^bold>\<or> C)" by (smt (verit, ccfv_threshold) ADDI_a_def Disj_def Sep_def join_def subset_def)

(**A stronger separation condition: the given sets are open, resp. closed, and disjoint*)
definition OpenDisj ("OpenDisj[_]") 
  where "OpenDisj[\<C>] A B \<equiv>  Op[\<C>] A \<and> Op[\<C>] B \<and> Disj A B"
definition ClosedDisj ("ClosedDisj[_]") 
  where "ClosedDisj[\<C>] A B \<equiv>  Cl[\<C>] A \<and> Cl[\<C>] B \<and> Disj A B"

lemma ClDisj_implies_Sep: "\<forall>A B. ClosedDisj[\<C>] A B \<longrightarrow> Sep[\<C>] A B" by (simp add: ClosedDisj_def Disj_symm Sep_def fixpoint_pred_def setequ_equ)
lemma OpDisj_implies_Sep: "MONO \<C> \<Longrightarrow> \<forall>A B. OpenDisj[\<C>] A B \<longrightarrow> Sep[\<C>] A B" by (smt (verit, best) CI_Disj_rel Disj_def OpenDisj_def Sep_def fixpoint_pred_def setequ_char) 
(*proof -

  assume mono:"MONO \<C>"
  { fix A B 
    from mono have aux: "Op[\<C>](A) \<and> Op[\<C>](B) \<longrightarrow> Sep[\<C>] (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Sep_Op_diff by blast
    { assume op: "Op[\<C>](A) \<and> Op[\<C>](B)" and disj: "Disj A B"
      hence "(A \<^bold>\<leftharpoonup> B) \<approx> A \<and> (B \<^bold>\<leftharpoonup> A) \<approx> B" unfolding conn by (smt (verit, best) Disj_def bottom_def meet_def setequ_char) 
      hence "Sep[\<C>] A B" using op aux by (simp add: setequ_equ)
    } hence "OpenDisj[\<C>] A B \<longrightarrow> Sep[\<C>] A B" by (simp add: OpenDisj_def)
  } thus ?thesis by blast
qed *)

(**Another condition: separation by open sets (aka. "by open neighborhoods")*)
definition SepByOpens ("SepByOpens[_]") 
  where "SepByOpens[\<C>] A B \<equiv> (\<exists>G H. OpenDisj[\<C>] G H \<and> A \<preceq> G \<and> B \<preceq> H)"

lemma SepByOpens_implies_Sep: "MONO \<C> \<Longrightarrow> SepByOpens[\<C>] A B \<longrightarrow> Sep[\<C>] A B" using SepByOpens_def OpDisj_implies_Sep Sep_sub by blast
lemma "\<CC> \<C> \<Longrightarrow> Sep[\<C>] A B \<longrightarrow> SepByOpens[\<C>] A B" nitpick oops (*countermodel*)

(**T0 (Kolmogorov): for any two distinct points there exists an open set containing one point but not the other.*)
definition "T0 \<C> \<equiv> \<forall>p q. p \<noteq> q \<longrightarrow> (\<exists>G. Op[\<C>] G \<and> \<not>(G p \<longleftrightarrow> G q))"
(**T1 (Fréchet): for any two distinct points there exist two (not necessarily disjoint) open sets, each containing one point but not the other.*)
definition "T1 \<C> \<equiv> \<forall>p q. p \<noteq> q \<longrightarrow> (\<exists>G H. Op[\<C>] G \<and> Op[\<C>] H \<and> G p \<and> \<not>G q \<and> H q \<and> \<not>H p)"
(**T2 (Hausdorff): any two distinct points are separated by open sets*)
definition "T2 \<C> \<equiv> \<forall>p q. p \<noteq> q \<longrightarrow> SepByOpens[\<C>] {p} {q}"
(**Regular: closed sets and their non-contained points are separated by open sets*)
definition "Regular \<C> \<equiv> \<forall>p Q. Cl[\<C>] Q \<and> \<not>Q p \<longrightarrow> SepByOpens[\<C>] {p} Q"
(**Normal: disjoint closed sets are separated by open sets*)
definition "Normal \<C> \<equiv> \<forall>P Q. ClosedDisj[\<C>] P Q \<longrightarrow> SepByOpens[\<C>] P Q"
(**T3 (regular Hausdorff): *)
definition "T3 \<C> \<equiv> T0 \<C> \<and> Regular \<C>"
(**T4 (normal Hausdorff): *)
definition "T4 \<C> \<equiv> T1 \<C> \<and> Normal \<C>"

(**T0 and T1 can be given similar definitions with closed sets*)
lemma T0_def2: "T0 \<C> = (\<forall>p q. p \<noteq> q \<longrightarrow> (\<exists>G. Cl[\<C>] G \<and> \<not>(G p \<longleftrightarrow> G q)))" by (metis (mono_tags) BA_dn T0_def compl_def fp_d)
lemma T1_def2: "T1 \<C> = (\<forall>p q. p \<noteq> q \<longrightarrow> (\<exists>G H. Cl[\<C>] G \<and> Cl[\<C>] H \<and> G p \<and> \<not>G q \<and> H q \<and> \<not>H p))" by (smt (verit, del_insts) BA_dn T1_def compl_def fp_d)

(**Another alternative definition for T0: the closures of distinct points are distinct.*)
lemma T0_def3: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C>      
          \<Longrightarrow> T0 \<C> = (\<forall>p q. p \<noteq> q \<longrightarrow> \<not>(\<C> {p} \<approx> \<C> {q}))"
proof -
  assume mono: "MONO \<C>" and cl2: "Cl_2 \<C>" and cl4: "Cl_4' \<C>"
  from mono cl2 cl4 have l2r: "T0 \<C> \<longrightarrow> (\<forall>p q. p \<noteq> q \<longrightarrow> \<not>(\<C> {p} \<approx> \<C> {q}))"
    unfolding T0_def2 by (smt (z3) C_fp_def singleton_def inf_char setequ_equ subset_def)
  have r2l: "(\<forall>p q. p \<noteq> q \<longrightarrow> \<not>(\<C> {p} \<approx> \<C> {q})) \<longrightarrow> T0 \<C>" 
    proof -
      { assume def3: "\<forall>p q. p \<noteq> q \<longrightarrow> \<not>(\<C> {p} \<approx> \<C> {q})"
        { fix p::'a and q::'a 
          { assume pqdiff: "p \<noteq> q" 
            from this def3 have "\<not>(\<C> {p} \<approx> \<C> {q})" by simp
            from this mono cl2 cl4 have "(\<exists>G. Cl[\<C>] G \<and> \<not>(G p \<longleftrightarrow> G q))" using C_fp_def inf_char by (smt (z3) singleton_def  setequ_def setequ_equ subset_def)
          }} hence "T0 \<C>" by (simp add: T0_def2)
        } thus ?thesis by blast
      qed
  from l2r r2l show ?thesis by blast
qed

(**Another alternative definition for T1: singleton sets are all closed.*)
lemma T1_def3a: "(\<forall>p. Cl[\<C>] {p}) \<longrightarrow> T1 \<C>" by (metis T1_def2 singleton_def)
lemma T1_def3b: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T1 \<C> \<longrightarrow> (\<forall>p. Cl[\<C>] {p})" proof -
  assume mono: "MONO \<C>" and cl2: "Cl_2 \<C>" 
  { assume t1: "T1 \<C>"
    have "\<forall>p. Cl[\<C>] {p}" proof (rule ccontr)
      assume "\<not>(\<forall>p. Cl[\<C>] {p})"
      hence "\<exists>p. \<not>Cl[\<C>] {p}" by simp
      from this obtain p where "\<not>Cl[\<C>] {p}" ..
      hence "\<exists>q. p \<noteq> q \<and> \<C>{p} q" by (smt (verit, ccfv_threshold) EXPN_def singleton_def cl2 fixpoint_pred_def setequ_char subset_def)
      from this obtain q where 1: "p \<noteq> q \<and> \<C>{p} q" ..
      from this t1 have "\<exists>G H. Cl[\<C>] G \<and> Cl[\<C>] H \<and> G p \<and> \<not>G q \<and> H q \<and> \<not>H p" by (simp add: T1_def2)
      from this obtain G H where 2: "Cl[\<C>] G \<and> Cl[\<C>] H \<and> G p \<and> \<not>G q \<and> H q \<and> \<not>H p" by blast
      from 1 2 mono show False by (metis (no_types, lifting) MONO_def singleton_def fixpoint_pred_def setequ_equ subset_def)
    qed
  } thus ?thesis by blast
qed
lemma T1_def3: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T1 \<C> = (\<forall>p. Cl[\<C>] {p})" using T1_def3a T1_def3b by auto

(**As expected, our encoding does not (a priori) assume any separation property.*)
lemma "\<CC> \<C> \<Longrightarrow> Normal \<C>" nitpick oops (**countermodel to NORM *)
lemma "\<CC> \<C> \<Longrightarrow> Regular \<C>" nitpick oops (**countermodel to REG *)
lemma "\<CC> \<C> \<Longrightarrow> T2 \<C>" nitpick oops (**countermodel to T2 *)
lemma "\<CC> \<C> \<Longrightarrow> T1 \<C>" nitpick oops (**countermodel to T1 *)
lemma "\<CC> \<C> \<Longrightarrow> T0 \<C>" nitpick oops (**countermodel to T0 *)

lemma T1_implies_T0: "T1 \<C> \<longrightarrow> T0 \<C>" using T0_def T1_def by metis
lemma "\<CC> \<C> \<Longrightarrow> T0 \<C> \<longrightarrow> T1 \<C>" nitpick oops (**(finite) countermodel*)

lemma T2_implies_T1: "T2 \<C> \<longrightarrow> T1 \<C>" unfolding T2_def T1_def SepByOpens_def by (smt (verit, best) Disj_def OpenDisj_def singleton_def bottom_def meet_def setequ_equ subset_def)
lemma "\<CC> \<C> \<Longrightarrow> T1 \<C> \<longrightarrow> T2 \<C>" oops (**expect infinite countermodel*)

lemma RegularCollapsesT0andT1: "Regular \<C> \<longrightarrow> (T0 \<C> = T1 \<C>)" proof -
  have l2r: "Regular \<C> \<longrightarrow> (T0 \<C> \<longrightarrow> T1 \<C>)" 
    unfolding T0_def T1_def Regular_def OpenDisj_def Disj_def SepByOpens_def singleton_def by (smt (verit, ccfv_threshold) bottom_def compl_def fp_d meet_def setequ_equ subset_def)
  from l2r T1_implies_T0 show ?thesis by blast
qed
lemma RegularCollapsesT1andT2: "Regular \<C> \<longrightarrow> (T1 \<C> = T2 \<C>)" proof -
  have l2r: "Regular \<C> \<longrightarrow> (T1 \<C> \<longrightarrow> T2 \<C>)" unfolding T1_def T2_def Regular_def subset_def SepByOpens_def by (metis singleton_def fp_d compl_def)
  from l2r T2_implies_T1 show ?thesis by blast
qed
lemma T1_Normal_implies_Regular: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T1 \<C> \<longrightarrow> (Normal \<C> \<longrightarrow> Regular \<C>)" proof -
  assume mono: "MONO \<C>" and cl2: "Cl_2 \<C>" 
  { assume T1: "T1 \<C>" and NORM: "Normal \<C>" 
    { fix p and Q
      { assume clQ: "Cl[\<C>](Q)" and nQp: "\<not>Q(p)"
        from T1 cl2 mono have "Cl[\<C>]({p})" by (simp add: T1_def3)
        moreover have "Disj {p} Q" by (simp add: singleton_def Disj_def bottom_def meet_def nQp setequ_char)
        ultimately have "SepByOpens[\<C>] {p} Q" using ClosedDisj_def NORM Normal_def clQ by blast
      } hence "Cl[\<C>](Q) \<and> \<not>Q(p) \<longrightarrow> SepByOpens[\<C>] {p} Q" by simp
    } hence "Regular \<C>" by (simp add: Regular_def)
  } thus ?thesis by simp
qed

lemma T3_implies_T2: "T3 \<C> \<longrightarrow> T2 \<C>" using RegularCollapsesT0andT1 RegularCollapsesT1andT2 T3_def by blast
lemma "\<CC> \<C> \<Longrightarrow> T3 \<C> \<longrightarrow> T2 \<C>" oops (** expect infinite countermodel*)

lemma T4_implies_T3: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T4 \<C> \<longrightarrow> T3 \<C>" by (simp add: T1_Normal_implies_Regular T1_implies_T0 T3_def T4_def)
lemma "\<CC> \<C> \<Longrightarrow> T4 \<C> \<longrightarrow> T3 \<C>" oops (** expect infinite countermodel*)

(**We can also generate countermodels to some well-known non-theorems (assuming all conditions).*)
lemma "\<CC> \<C> \<Longrightarrow> Regular \<C> \<longrightarrow> T1 \<C>" nitpick oops (**(finite) countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> Normal \<C> \<longrightarrow> T1 \<C>" nitpick oops (**(finite) countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> Regular \<C> \<longrightarrow> T2 \<C>" nitpick oops (**(finite) countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> Normal \<C> \<longrightarrow> T2 \<C>" nitpick oops (**(finite) countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> T2 \<C> \<longrightarrow> Regular \<C>" oops (**expect infinite countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> T2 \<C> \<longrightarrow> Normal \<C>" oops (**expect infinite countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> Regular \<C> \<longrightarrow> Normal \<C>" oops (**expect infinite countermodel*)
lemma "\<CC> \<C> \<Longrightarrow> Normal \<C> \<longrightarrow> Regular \<C>" nitpick oops (**expect infinite countermodels*)

(**Just for fun: here is another (pseudo-interactive) proof that is actually subsumed under "T2_implies_T1" above.
This is a 'textbook' proof. Observe that it employs additional assumptions than the one above. *)
lemma "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T2 \<C> \<longrightarrow> T1 \<C>" proof -
  assume mono: "MONO \<C>" and cl2: "Cl_2 \<C>" 
  { assume T2: "T2 \<C>"
    fix p::'a
    let ?np= "\<lambda>q. q \<noteq> p"
    let ?Prop= "\<lambda>G.  Op[\<C>](G) \<and> \<not>G(p)"    
    have aux: "Op[\<C>](\<^bold>\<Or>?Prop)" by (metis (no_types, lifting) Int_sup_closed cl2 mono supremum_closed_def)
    from T2 have "\<forall>x. ?np x \<longrightarrow> (\<exists>G. ?Prop(G) \<and> G(x))" unfolding singleton_def SepByOpens_def OpenDisj_def T2_def Disj_def by (smt (verit, best) bottom_def meet_def setequ_char subset_def)
    hence "?np \<approx> \<^bold>\<Or>?Prop" by (smt (verit) setequ_char supremum_def)
    hence "Op[\<C>](?np)" using aux setequ_equ by force
    hence "Cl[\<C>]{p}" by (simp add: singleton_def ClOpdual compl_def)
  } thus ?thesis unfolding singleton_def using T1_def2 by blast
qed

end