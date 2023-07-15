theory GasAnalysis_06072022_095424
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


text \<open> function definition \<close>


consts analysis :: " GasSensor list \<Rightarrow> Status"


consts location :: " GasSensor list \<Rightarrow> Angle"


consts goreq :: " Intensity \<times> Intensity \<Rightarrow>bool"


consts angle :: " nat \<Rightarrow> Angle"


consts intensity :: " GasSensor list \<Rightarrow> Intensity"

subsection \<open> State Space \<close>

zstore GasAnalysis =
  st :: "Status"
  gs :: "GasSensor list"
  ins :: "Intensity"
  anl :: "Angle"
  
  act_st::"ProperState"
where inv: "To be entered manually"

subsection \<open> Operations \<close>

zoperation InitialToNoGas =
  over GasAnalysis
  pre "act_st= initial"
  update "[ act_st\<Zprime>= NoGas
         , gs\<Zprime> = []
         , anl\<Zprime> = Front
          ]"
        
zoperation NoGasToAnalysis =
  over GasAnalysis
  params gs\<in>"SeqGasSensor"
  pre "act_st= NoGas"
  update "[ act_st\<Zprime>= Analysis
          ,st\<Zprime> =analysis(gs)
          ]"
        
zoperation AnalysisToNoGas =
  over GasAnalysis
  pre "act_st= Analysis \<and> st=noGas""
  update "[ act_st\<Zprime>= NoGas
          ]"
        
zoperation AnalysisToGasDetected =
  over GasAnalysis
  pre "act_st= Analysis \<and> st=gasD""
  update "[ act_st\<Zprime>= GasDetected
          ,ins\<Zprime> =intensity(gs)
          ]"
        
zoperation GasDetectedToFinal =
  over GasAnalysis
  pre "act_st= GasDetected"
  update "[ act_st\<Zprime>= final
          ]"
        
zoperation GasDetectedToReading =
  over GasAnalysis
  pre "act_st= GasDetected"
  update "[ act_st\<Zprime>= Reading
         , anl\<Zprime> = location(gs)
         , anl\<Zprime> = location(gs)
          ]"
        
zoperation ReadingToAnalysis =
  over GasAnalysis
  params gs\<in>"SeqGasSensor"
  pre "act_st= Reading"
  update "[ act_st\<Zprime>= Analysis
          ,st\<Zprime> =analysis(gs)
          ]"
        
zoperation Shine =
  over GasAnalysis
  params s\<in>"{act_st}"
  
definition Init :: "GasAnalysis subst" where
  [z_defs]:
  "Init = 
  [
 st\<leadsto> noGas,
  gs \<leadsto> [],
  ins\<leadsto> 0,
  anl\<leadsto> Front,
  act_st\<leadsto> initial
  ]"
  
zmachine GasAnalysisMachine =
  init initial
  operations  InitialToNoGas NoGasToAnalysis AnalysisToNoGas AnalysisToGasDetected GasDetectedToFinal GasDetectedToReading ReadingToAnalysis

animate GasAnalysisMachine


subsection \<open> Structural Invariants \<close>

lemma Init_inv: "initial establishes GasAnalysis_inv"
  by zpog_full

lemma InitialToNoGas_inv: "InitialToNoGas preserves GasAnalysis_inv"
  by (zpog_full, auto)
  
lemma NoGasToAnalysis_inv: "NoGasToAnalysis preserves GasAnalysis_inv"
  by (zpog_full, auto)
  
lemma AnalysisToNoGas_inv: "AnalysisToNoGas preserves GasAnalysis_inv"
  by (zpog_full, auto)
  
lemma AnalysisToGasDetected_inv: "AnalysisToGasDetected preserves GasAnalysis_inv"
  by (zpog_full, auto)
  
lemma GasDetectedToFinal_inv: "GasDetectedToFinal preserves GasAnalysis_inv"
  by (zpog_full, auto)
  
lemma GasDetectedToReading_inv: "GasDetectedToReading preserves GasAnalysis_inv"
  by (zpog_full, auto)
  
lemma ReadingToAnalysis_inv: "ReadingToAnalysis preserves GasAnalysis_inv"
  by (zpog_full, auto)
  

end

