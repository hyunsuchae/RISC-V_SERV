# RISC-V_SERV
Verifying RISC-V core SERV

A. Description of files


  In this repository, there are two folders, "formal" and "rtl".
	"formal" - contains file used for formal verifiction (assertion files ".sv" and script files used to run JasperGold ".tcl")

B. How to run the program


 -> The "/formal/insn_types" directory is used for instruction-unit verification.
	There are assertion files with the name *"v_serv_XXX.sv"*, and script files with the name *"top_XXX.tcl"*.
	The "XXX" represents the type of the instruction.
	
	
 -> The "/formal/module_unit" directory is used for module-unit verification.
	There are assertion files with the name *"v_XXX"*, and script files with the name *"XXX.tcl"*.
	The "XXX" represents the name of the rtl module.
 
  	a) do "module load cadence/2016" in the top most directory
  	b) run "JasperGold top_XXX.tcl &" in the "formal/module_unit" or "formal/insn_type" directory
