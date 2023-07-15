theory GasAnalysis_22082022_115847
imports "Z_Machines.Z_Machine"
begin

notation undefined ("???")

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the GasAnalysis state machine in Z Machine notations.\<close>

subsection \<open> type definition \<close>

enumtype ProperState = initial | NoGas | Analysis | GasDetected | final | Reading 

definition "ProperState = {initial, NoGas, Analysis, GasDetected, final, Reading}" 

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


zfun angle(x:: nat)::Angle

zfun analysis(gs::" GasSensor list ")::Status
precondition "size(gs)>0"
postcondition "\<exists> x::nat. 0<x\<and>x\<le>size(gs)\<and>i(gs!x)>0 \<longrightarrow> result= (gasD)"
postcondition "\<forall> y::nat. 0<y\<and>y\<le>size(gs)\<and>i(gs!y)= (0) \<longrightarrow> result= (noGas)"

zfun location(gs::" GasSensor list ")::Angle
precondition "size(gs)>0"
postcondition "\<exists> x::nat. 0<x\<and>x\<le>size(gs) \<longrightarrow> i(gs!x)= (intensity(gs))\<and>result= (angle(x))"

zfun goreq(i1::Intensity, i2::Intensity):: bool
postcondition "result= (i1>i2)"

zfun intensity(gs::" GasSensor list ")::Intensity
precondition "size(gs)>0"
postcondition "\<forall> x::nat. 0<x\<and>x\<le>size(gs) \<longrightarrow> goreq(result, i(gs!x))"
postcondition "\<exists> y::nat. 0<y\<and>y\<le>size(gs) \<longrightarrow> result= (i(gs!y))"

subsection \<open> State Space \<close>

zstore GasAnalysis =
  st :: "Status"
  gs :: "GasSensor list"
  ins :: "Intensity"
  anl :: "Angle"
  
  event_resume::"bool"
  event_stop::"bool"
  act_st::"ProperState"
  desired_st::"ProperState set"
where inv: "To be entered manually"

subsection \<open> Operations \<close>

zoperation InitialToReading =
  over GasAnalysis
  pre "act_st= initial"
  update "[ act_st\<Zprime>= Reading
  		  , desired_st\<Zprime>= {Analysis}
         , gs\<Zprime> =[]
         , anl\<Zprime> = Front
          ]"
        
zoperation AnalysisToNoGas =
  over GasAnalysis
  pre "act_st= Analysis \<and> st=noGas"
  update "[ act_st\<Zprime>= NoGas
  		  , desired_st\<Zprime>= {Reading}
         , event_resume\<Zprime> = True
          ]"
        
zoperation AnalysisToGasDetected =
  over GasAnalysis
  pre "act_st= Analysis \<and> st=gasD"
  update "[ act_st\<Zprime>= GasDetected
  		  , desired_st\<Zprime>= {final, Reading}
          ,ins\<Zprime> =intensity(gs)
          ]"
        
zoperation GasDetectedToFinal =
  over GasAnalysis
  pre "act_st= GasDetected \<and> goreq(ins, thr)"
  update "[ act_st\<Zprime>= final
  		  , desired_st\<Zprime>= {}
         , event_stop\<Zprime> = True
          ]"
        
zoperation GasDetectedToReading =
  over GasAnalysis
  pre "act_st= GasDetected \<and> \<not>goreq(ins, thr)"
  update "[ act_st\<Zprime>= Reading
  		  , desired_st\<Zprime>= {Analysis}
         , anl\<Zprime> = location(gs)
          ]"
        
zoperation ReadingToAnalysis =
  over GasAnalysis
  params gs\<in>"SeqGasSensor"
  pre "act_st= Reading"
  update "[ act_st\<Zprime>= Analysis
  		  , desired_st\<Zprime>= {NoGas, GasDetected}
          ,st\<Zprime> =analysis(gs)
          ]"
        
zoperation NoGasToReading =
  over GasAnalysis
  pre "act_st= NoGas"
  update "[ act_st\<Zprime>= Reading
  		  , desired_st\<Zprime>= {Analysis}
          ]"
        
zoperation Shine =
  over GasAnalysis
  params s\<in>"{act_st}"
  
definition Init :: "GasAnalysis subst" where
  [z_defs]:
  "Init = 
  [\<leadsto>]"
(*To be filled in by user*)
  
  
zmachine GasAnalysisMachine =
  init Init
  operations  InitialToReading AnalysisToNoGas AnalysisToGasDetected GasDetectedToFinal GasDetectedToReading ReadingToAnalysis NoGasToReading Shine

animate GasAnalysisMachine


subsection \<open> Structural Invariants \<close>

lemma Init_inv: "Init establishes GasAnalysis_inv"
  by zpog_full

lemma InitialToReading_inv: "InitialToReading() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma AnalysisToNoGas_inv: "AnalysisToNoGas() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma AnalysisToGasDetected_inv: "AnalysisToGasDetected() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma GasDetectedToFinal_inv: "GasDetectedToFinal() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma GasDetectedToReading_inv: "GasDetectedToReading() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma ReadingToAnalysis_inv: "ReadingToAnalysis l preserves GasAnalysis_inv"
  by (zpog_full; auto)
  
lemma NoGasToReading_inv: "NoGasToReading() preserves GasAnalysis_inv"
  by (zpog_full; auto)
  

end

