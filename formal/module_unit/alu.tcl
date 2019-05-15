#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

clear -all
#Reading the files (.v and .sv) 
analyze -v2k {../rtl/ser_add.v}
analyze -v2k {../rtl/ser_shift.v}
analyze -v2k {../rtl/ser_lt.v}
analyze -v2k {../rtl/shift_reg.v}

analyze -v2k {../rtl/serv_alu.v}

analyze -sv v_serv_alu.sv

#Elaborating the design, specify the top module
#elaborate -top ser_add
elaborate -top serv_alu

#You may  need to add commands below

#Set the clock
clock clk

#Set Reset
reset i_rst

#Prove all
prove -bg -all
