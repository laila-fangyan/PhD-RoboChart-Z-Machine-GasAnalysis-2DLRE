theory GasAnalysis_22122022_041540
imports "Z_Machines.Z_Machine"
begin

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the GasAnalysis state machine in Z Machine notations.\<close>

notation undefined ("???")

subsection \<open> type definition \<close>

datatype ('s, 'e) tag =
  State (ofState: 's) | Event (ofEvent: 'e)

abbreviation "is_Event x \<equiv> \<not> is_State x"

type_synonym ('s, 'e) rctrace = "('s, 'e) tag list"

definition wf_rcstore :: "('s, 'e) rctrace \<Rightarrow> 's \<Rightarrow> 's option \<Rightarrow> bool" where
[z_defs]: "wf_rcstore tr st final = (
     length(tr) > 0 
   \<and> tr ! ((length tr) -1) = State st 
   \<and> (final \<noteq> None \<longrightarrow> (\<forall>i<length tr. tr ! i = State (the final) \<longrightarrow> i= (length tr) -1)) 
   \<and> (filter is_State tr) ! (length (filter is_State tr) -1) = State  st)"
   
enumtype St = initial | NoGas | Analysis | GasDetected | final | Reading 
definition [z_defs]: "St = {initial, NoGas, Analysis, GasDetected, final, Reading}" 


enumtype Evt = gas | resume | turn | stop 
definition: "Evt = {gas, resume, turn, stop}" 


enumtype Status = noGas | gasD

definition "Status = {noGas, gasD}"
enumtype Angle = Left | Right | Back | Front

definition "Angle = {Left, Right, Back, Front}"
type_synonym Chem= "nat"
type_synonym Intensity= "nat"
record GasSensor =
  c :: Chem
  i :: Intensity
record_default GasSensor




consts thr :: "Intensity"

text \<open> function definition \<close>

zfun location(gs::" GasSensor list ")::Angle
precondition "size(gs)>0"
postcondition "\<exists> x::nat. 0<x \<and> x\<le>size(gs) \<longrightarrow> i(gs!x)= (intensity(gs)) \<and> result= (angle(x))"
zfun intensity(gs::" GasSensor list ")::Intensity
precondition "size(gs)>0"
postcondition "\<forall> x::nat. 0<x \<and> x\<le>size(gs) \<longrightarrow> goreq(result, i(gs!x))"
postcondition "\<exists> y::nat. 0<y \<and> y\<le>size(gs) \<longrightarrow> result= (i(gs!y))"
zfun angle(x:: nat)::Angle
zfun analysis(gs::" GasSensor list ")::Status
precondition "size(gs)>0"
postcondition "\<exists> x::nat. 0<x \<and> x\<le>size(gs) \<and> i(gs!x)>0 \<longrightarrow> result= (gasD)"
postcondition "\<forall> y::nat. 0<y \<and> y\<le>size(gs) \<and> i(gs!y)= (0) \<longrightarrow> result= (noGas)"
zfun goreq(i1::Intensity, i2::Intensity):: bool
postcondition "result= (i1>i2)"

subsection \<open> State Space \<close>

zstore GasAnalysis =
  st :: "Status"
  gs :: "GasSensor list"
  ins :: "Intensity"
  anl :: "Angle"
  
  st::"St"
  tr :: "(St, Evt) tag list"
  trg:: "Evt option"
  triggers:: "Evt set"
  where inv: 
    "wf_rcstore tr st (Some final)"

subsection \<open> Operations \<close>

zoperation Trigger= 
params trigger \<in> "triggers"
pre "triggers \<noteq> {}"
update "[
        trg\<Zprime>= Some trigger
        ]"
        
zoperation InitialToReading =
  over GasAnalysis
  pre "st= initial"
  update "[st\<Zprime>= Reading
         , gs\<Zprime> =[]
         , anl\<Zprime> = Front
         ,tr\\<Zprime> =tr  @ [State Reading]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {gas}
         ]"
        
zoperation AnalysisToNoGas =
  over GasAnalysis
  pre "st= Analysis \<and> st= (noGas)"
  update "[st\<Zprime>= NoGas
         ,tr\\<Zprime> =tr @ [Event resume] @ [State NoGas]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {}
         ]"
        
zoperation AnalysisToGasDetected =
  over GasAnalysis
  pre "st= Analysis \<and> st= (gasD)"
  update "[st\<Zprime>= GasDetected
          , ins\<Zprime> =intensity(gs)
         ,tr\\<Zprime> =tr  @ [State GasDetected]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {}
         ]"
        
zoperation GasDetectedToFinal =
  over GasAnalysis
  pre "st= GasDetected \<and> goreq(ins, thr)"
  update "[st\<Zprime>= final
         ,tr\\<Zprime> =tr @ [Event stop] @ [State final]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {}
         ]"
        
zoperation GasDetectedToReading =
  over GasAnalysis
  pre "st= GasDetected \<and> \<not>goreq(ins, thr)"
  update "[st\<Zprime>= Reading
         , anl\<Zprime> = location(gs)
         ,tr\\<Zprime> =tr @ [Event turn] @ [State Reading]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {gas}
         ]"
        
zoperation ReadingToAnalysis =
  over GasAnalysis
  params gs \<in> "SeqGasSensor" 
  pre "st= Reading \<and> trg=Some gas"
  update "[st\<Zprime>= Analysis
          , st\<Zprime> =analysis(gs)
         ,tr\\<Zprime> =tr @ [Event gas] @ [State Analysis]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {}
         ]"
        
zoperation NoGasToReading =
  over GasAnalysis
  pre "st= NoGas"
  update "[st\<Zprime>= Reading
         ,tr\\<Zprime> =tr  @ [State Reading]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {gas}
         ]"
        

  
definition Init :: "GasAnalysis subst" where
  [z_defs]:
  "Init = 
  [st\<leadsto> ,
   tr\<leadsto> ,
   trg\<leadsto> ,
   triggers\<leadsto> ,
   ]"
(*To be filled in by user*)
  
  
zmachine GasAnalysisMachine =
  init Init
  invariant GasAnalysis_inv
  operations  InitialToReading AnalysisToNoGas AnalysisToGasDetected GasDetectedToFinal GasDetectedToReading ReadingToAnalysis NoGasToReading 



subsection \<open> Structural Invariants \<close>

lemma Init_inv [hoare_lemmas]: "Init establishes GasAnalysis_inv"
  by zpog_full

lemma InitialToReading_inv [hoare_lemmas]: "InitialToReading() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma AnalysisToNoGas_inv [hoare_lemmas]: "AnalysisToNoGas() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma AnalysisToGasDetected_inv [hoare_lemmas]: "AnalysisToGasDetected() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma GasDetectedToFinal_inv [hoare_lemmas]: "GasDetectedToFinal() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma GasDetectedToReading_inv [hoare_lemmas]: "GasDetectedToReading() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma ReadingToAnalysis_inv [hoare_lemmas]: "ReadingToAnalysis (gs) preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma NoGasToReading_inv [hoare_lemmas]: "NoGasToReading() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  

subsection \<open> Safety Requirements \<close>

zexpr R1 is ""

lemma  "Init establishes R1"
  by zpog_full

lemma "InitialToReading() preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma "AnalysisToNoGas() preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma "AnalysisToGasDetected() preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma "GasDetectedToFinal() preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma "GasDetectedToReading() preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma "ReadingToAnalysis (gs) preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma "NoGasToReading() preserves R1 under GasAnalysis_inv"
  by (zpog_full; auto)
  

definition [z_defs]: "GasAnalysis_axioms = ()"

lemma GasAnalysis_deadlock_free: "GasAnalysis_axioms  \<Longrightarrow> deadlock_free GasAnalysisMachine" 
  unfolding GasAnalysisMachine_def
  by deadlock_free
end

