#----------------------------------------
# JasperGold Version Info
# tool      : JasperGold 2015.09
# platform  : Linux 2.6.32-754.9.1.el6.x86_64
# version   : 2015.09 FCS 64 bits
# build date: 2015.09.29 22:07:32 PDT
#----------------------------------------
# started Wed May 01 23:20:41 CDT 2019
# hostname  : wario
# pid       : 12342
# arguments : '-label' 'session_0' '-console' 'wario:45152' '-style' 'windows' '-proj' '/home/ecelrc/students/hchae/verif_labs/project/formal/module_unit/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/ecelrc/students/hchae/verif_labs/project/formal/module_unit/jgproject/.tmp/.initCmds.tcl' 'add.tcl'
#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

clear -all
#Reading the files (.v and .sv) 
analyze -v2k {../rtl/ser_add.v}
source add.tcl
