# RISC-V_SERV
Verifying RISC-V core SERV

1) Description of files
  In this repository, there are two folders, "formal" and "rtl".
	"formal" - contains file used for formal verifiction (assertion files ".sv" and script files used to run JasperGold ".tcl")

2) How to run the program
    The "/formal/insn_types" directory is used for instruction-unit verification.
	There are assertion files with the name "v_serv_*.sv", and script files with the name "top_*.tcl".
	The "*" represents the type of the instruction.
    The "/formal/module_unit" directory is used for module-unit verification.
	There are assertion files with the name "v_*", and script files with the name "*.tcl".
	The "*" represents the rtl module.
 
  a) do "module load cadence/2016" in the top most directory
  b) run "JasperGold top_*.tcl &" in the "formal/module_unit" or "formal/insn_type" directory
